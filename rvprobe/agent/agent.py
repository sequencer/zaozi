#!/usr/bin/env python3
"""
RVProbe Agent - Automated Verification Generator
Converts natural language intent to Scala DSL constraint code via LLM-in-the-loop.
"""

import os
import subprocess
import re
from typing import TypedDict, Literal, Any, Dict
from pathlib import Path

from dotenv import load_dotenv
from langgraph.graph import StateGraph, END
from langchain_openai import ChatOpenAI

try:
    import yaml
    YAML_AVAILABLE = True
except ImportError:
    YAML_AVAILABLE = False

# Load environment variables from .env file
load_dotenv()

# Import RAG retriever
try:
    from rag import get_retriever
    RAG_AVAILABLE = True
except Exception as e:
    print(f"⚠️ RAG system not available: {e}")
    RAG_AVAILABLE = False

# ==================== Configuration ====================
MAX_RETRIES = 3
PROJECT_ROOT = Path(__file__).parent.parent.parent  # zaozi root
TEST_FILE_PATH = PROJECT_ROOT / "rvprobe" / "src" / "agent" / "Test.scala"
OUTPUT_BIN_PATH = PROJECT_ROOT / "out" / "test.bin"
MILL_COMMAND = ["nix", "develop", ".", "-c", "mill", "rvprobe.runMain", "me.jiuyang.rvprobe.agent.Test", str(OUTPUT_BIN_PATH)]

# ==================== Difftest Configuration ====================
_CONFIG_FILE = Path(__file__).parent / "benchmark" / "config.yaml"

def _load_difftest_config() -> Dict[str, Any]:
    """Load difftest section from config.yaml."""
    defaults = {
        "enabled": False,
        "test_bin": str(OUTPUT_BIN_PATH),
        "nexus_am_test_dir": "/home/clo91eaf/Project/xs-env/nexus-am/tests/rvprobetest",
        "nexus_am_arch": "riscv64-xs",
        "emu_bin": "/home/clo91eaf/Project/xs-env/XiangShan/build/emu",
        "workload_bin": "build/rvprobetest-riscv64-xs.bin",
        "diff_so": "/home/clo91eaf/Project/xs-env/XiangShan/ready-to-run/riscv64-nemu-interpreter-so",
        "emu_log": "/tmp/xs_difftest.log",
    }
    if YAML_AVAILABLE and _CONFIG_FILE.exists():
        with open(_CONFIG_FILE) as f:
            cfg = yaml.safe_load(f) or {}
        defaults.update(cfg.get("difftest", {}))
    return defaults

DIFFTEST_CFG = _load_difftest_config()

# LLM Configuration from environment variables
# Support both LLM_* and OPENAI_* for backward compatibility
LLM_API_KEY = os.getenv("LLM_API_KEY")
LLM_API_BASE = os.getenv("LLM_API_BASE")
LLM_MODEL = os.getenv("LLM_MODEL")


# ==================== State Definition ====================
class AgentState(TypedDict):
    """State container for the LangGraph workflow"""
    user_input: str          # Natural language constraint description
    dsl_code: str           # Generated Scala DSL code
    error_log: str          # Compilation/execution errors
    retry_count: int        # Current retry attempt
    is_success: bool        # Whether execution succeeded
    instructions: str       # Final instruction sequence
    retrieved_docs: str     # RAG retrieved documentation output
    difftest_log: str       # XiangShan difftest output log path
    difftest_passed: bool   # Whether difftest passed


# ==================== DSL API Documentation (Fallback) ====================
DSL_API_DOCS = """
# RVProbe Scala DSL API Reference

## Core Structure
```scala
object test extends RVGenerator:
  val sets = isRV64GC()  // or isRV64G(), isRV32I(), etc.
  def constraints() =
    // Define instruction constraints here
```

## Instruction Definition
```scala
instruction(index, opcodeConstraint) {
  argumentConstraints
}
```

## Opcode Constraints

### Arithmetic (I-type, immediate)
- `isAddi()` - ADDI instruction (rd, rs1, imm12)
- `isAddiw()` - ADDIW instruction (rd, rs1, imm12)
- `isSlti()` - SLTI instruction (rd, rs1, imm12)
- `isSltiu()` - SLTIU instruction (rd, rs1, imm12)
- `isAndi()` - ANDI instruction (rd, rs1, imm12)
- `isOri()` - ORI instruction (rd, rs1, imm12)
- `isXori()` - XORI instruction (rd, rs1, imm12)

### Arithmetic (R-type, register-register)
- `isAdd()` - ADD instruction (rd, rs1, rs2)
- `isAddw()` - ADDW instruction (rd, rs1, rs2)
- `isSub()` - SUB instruction (rd, rs1, rs2)
- `isSubw()` - SUBW instruction (rd, rs1, rs2)
- `isAnd()` - AND instruction (rd, rs1, rs2)
- `isOr()` - OR instruction (rd, rs1, rs2)
- `isXor()` - XOR instruction (rd, rs1, rs2)
- `isSlt()` - SLT instruction (rd, rs1, rs2)
- `isSltu()` - SLTU instruction (rd, rs1, rs2)

### Shift Instructions
- `isSlliRV64I()` - SLLI for RV64I (rd, rs1, shamtd) - 6-bit shift amount
- `isSrliRV64I()` - SRLI for RV64I (rd, rs1, shamtd) - 6-bit shift amount
- `isSraiRV64I()` - SRAI for RV64I (rd, rs1, shamtd) - 6-bit shift amount
- `isSlliRV32I()` - SLLI for RV32I (rd, rs1, shamtw) - 5-bit shift amount
- `isSrliRV32I()` - SRLI for RV32I (rd, rs1, shamtw) - 5-bit shift amount
- `isSraiRV32I()` - SRAI for RV32I (rd, rs1, shamtw) - 5-bit shift amount
- `isSlliw()` - SLLIW (rd, rs1, shamtw)
- `isSrliw()` - SRLIW (rd, rs1, shamtw)
- `isSraiw()` - SRAIW (rd, rs1, shamtw)
- `isSll()` - SLL register shift (rd, rs1, rs2)
- `isSrl()` - SRL register shift (rd, rs1, rs2)
- `isSra()` - SRA register shift (rd, rs1, rs2)

IMPORTANT: There is NO `isSlli()` or `isSrli()` or `isSrai()` function!
Use `isSlliRV64I()` for 64-bit or `isSlliRV32I()` for 32-bit.

### Branch Instructions
- `isBeq()` - BEQ instruction (rs1, rs2)
- `isBne()` - BNE instruction (rs1, rs2)
- `isBlt()` - BLT instruction (rs1, rs2)
- `isBge()` - BGE instruction (rs1, rs2)
- `isBltu()` - BLTU instruction (rs1, rs2)
- `isBgeu()` - BGEU instruction (rs1, rs2)

### Memory Instructions
- `isLw()` - LW instruction (rd, rs1, imm12)
- `isLd()` - LD instruction (rd, rs1, imm12)
- `isSw()` - SW instruction (rs1, rs2)
- `isSd()` - SD instruction (rs1, rs2)
- `isLui()` - LUI instruction (rd, imm20)

## Argument Constraints (Range Functions)

### Register Ranges
- `rdRange(min, max)` - Destination register range
- `rs1Range(min, max)` - Source register 1 range
- `rs2Range(min, max)` - Source register 2 range

### Immediate Ranges
- `imm12Range(min, max)` - 12-bit immediate value range (for ADDI, LW, etc.)
- `imm20Range(min, max)` - 20-bit immediate (for LUI, AUIPC)

### Shift Amount Ranges
- `shamtwRange(min, max)` - 5-bit shift amount (for RV32I shifts, SLLIW/SRLIW)
- `shamtdRange(min, max)` - 6-bit shift amount (for RV64I shifts)

IMPORTANT: There is NO `shamtRange()` or `immRange()` function!
Use `shamtwRange()` for 32-bit shifts, `shamtdRange()` for 64-bit shifts,
and `imm12Range()` for 12-bit immediates.

Constraints are combined with `&` (logical AND):
```scala
rdRange(1, 32) & rs1Range(1, 32) & imm12Range(-2048, 2047)
```

## Instruction Sets
- `isRV64GC()` - RV64 with G+C extensions
- `isRV64G()` - RV64 base with IMAFD
- `isRV32I()` - RV32 base integer

## Examples

### ADDI with immediate constraint
```scala
(0 until 10).foreach { i =>
  instruction(i, isAddi()) {
    rdRange(1, 16) & rs1Range(1, 16) & imm12Range(0, 100)
  }
}
```

### SLLI with shift amount constraint (RV64I)
```scala
(0 until 5).foreach { i =>
  instruction(i, isSlliRV64I()) {
    rdRange(1, 32) & rs1Range(1, 32) & shamtdRange(0, 31)
  }
}
```

### Mixed instruction types
```scala
(0 until 10).foreach { i =>
  instruction(i, isAddi()) {
    rdRange(1, 32) & rs1Range(1, 32) & imm12Range(-100, 100)
  }
}
(10 until 20).foreach { i =>
  instruction(i, isSlliRV64I()) {
    rdRange(1, 32) & rs1Range(1, 32) & shamtdRange(0, 31)
  }
}
(20 until 30).foreach { i =>
  instruction(i, isXor()) {
    rdRange(1, 32) & rs1Range(1, 32) & rs2Range(1, 32)
  }
}
```

Do NOT use Scala standard library features like Array.fill(), var, val inside
instruction() blocks. The constraint DSL only accepts range constraints combined with &.
"""


# ==================== Node 1: Retrieve ====================
def retrieve_node(state: AgentState) -> AgentState:
    """
    Retrieve relevant DSL API documentation using RAG.
    Falls back to static docs if RAG is unavailable.
    """
    print("📚 [Retrieve] Querying RAG system for relevant constraints...")

    if RAG_AVAILABLE:
        try:
            retriever = get_retriever()
            retrieved_docs = retriever.retrieve(state['user_input'], top_k=10)
            state['retrieved_docs'] = retrieved_docs
            # Count how many functions were retrieved (each starts with ###)
            func_count = retrieved_docs.count('###')
            print(f"📚 [Retrieve] Retrieved {func_count} constraint functions")
        except Exception as e:
            print(f"⚠️ RAG retrieval failed: {e}")
            print("   Falling back to static documentation...")
            state['retrieved_docs'] = DSL_API_DOCS
    else:
        print("⚠️ RAG not available, using static documentation")
        state['retrieved_docs'] = DSL_API_DOCS

    return state


# ==================== Node 2: Generate ====================
def generate_node(state: AgentState) -> AgentState:
    """
    Generate Scala DSL code from natural language using LLM.
    """
    print(f"🤖 [Generate] Attempt {state['retry_count'] + 1}/{MAX_RETRIES}")

    # Build prompt with context
    system_prompt = f"""You are an expert in RISC-V instruction generation and Scala DSL.

{state.get('retrieved_docs', DSL_API_DOCS)}

Your task: Generate ONLY the Scala code for the constraints() method body based on user requirements.
"""

    user_prompt = f"""User Request: {state['user_input']}"""

    # Add error context if retrying
    if state['error_log']:
        user_prompt += f"\n\nPrevious Error:\n{state['error_log']}\n\nPlease fix the code to resolve this error."

    user_prompt += """

IMPORTANT:
1. Generate ONLY the method body content for constraints()
2. Do NOT include the object definition, package, imports, or main function
3. Start directly with the constraint logic (e.g., (0 until N).foreach ...)
4. Use proper Scala syntax with correct indentation
5. Ensure all constraints are properly defined

Example output format:
```scala
(0 until 20).foreach { i =>
  instruction(i, isAddi()) {
    rdRange(1, 32) & rs1Range(1, 32)
  }
}
```
"""

    # Call LLM
    llm_kwargs = {"model": LLM_MODEL, "temperature": 0}
    if LLM_API_BASE:
        llm_kwargs["base_url"] = LLM_API_BASE
    if LLM_API_KEY:
        llm_kwargs["api_key"] = LLM_API_KEY

    llm = ChatOpenAI(**llm_kwargs)
    messages = [
        {"role": "system", "content": system_prompt},
        {"role": "user", "content": user_prompt}
    ]

    response = llm.invoke(messages)
    generated_code = response.content.strip()

    # Extract code from markdown if present
    if "```scala" in generated_code:
        generated_code = re.search(r"```scala\n(.*?)```", generated_code, re.DOTALL).group(1)
    elif "```" in generated_code:
        generated_code = re.search(r"```\n(.*?)```", generated_code, re.DOTALL).group(1)

    generated_code = generated_code.strip()

    print(f"📝 Generated constraints body:\n{generated_code[:200]}...")

    state['dsl_code'] = generated_code
    state['retry_count'] += 1
    return state


# ==================== Node 3: Execute ====================
def execute_node(state: AgentState) -> AgentState:
    """
    Write generated code to Test.scala, execute Mill command, and parse results.
    """
    print("⚙️  [Execute] Writing code and running Mill...")

    # Build complete Scala file
    # Add proper indentation (6 spaces) to each line of generated code
    indented_code = '\n'.join('      ' + line if line.strip() else '' for line in state['dsl_code'].split('\n'))

    scala_code = f"""// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 Jianhao Ye <Clo91eaf@qq.com>
package me.jiuyang.rvprobe.agent

import me.jiuyang.smtlib.default.{{*, given}}
import me.jiuyang.rvprobe.*
import me.jiuyang.rvprobe.constraints.*

import java.nio.file.{{Files, Paths}}
import scala.util.control.NonFatal

// Run with: nix develop . -c mill rvprobe.runMain me.jiuyang.rvprobe.agent.Test out/test.bin
@main def Test(outputPath: String): Unit =
  object test extends RVGenerator:
    val sets          = isRV64GC()
    def constraints() =
{indented_code}

  test.printInstructions()
  test.writeInstructionsToFile(outputPath)
"""

    # Write to file
    try:
        TEST_FILE_PATH.parent.mkdir(parents=True, exist_ok=True)
        TEST_FILE_PATH.write_text(scala_code)
        print(f"✅ Written to {TEST_FILE_PATH}")
    except Exception as e:
        state['error_log'] = f"File write error: {str(e)}"
        state['is_success'] = False
        return state

    # Execute Mill command
    try:
        # Ensure output directory exists
        OUTPUT_BIN_PATH.parent.mkdir(parents=True, exist_ok=True)

        # Run Mill from project root
        result = subprocess.run(
            MILL_COMMAND,
            cwd=PROJECT_ROOT,
            capture_output=True,
            text=True,
            timeout=60
        )

        output = result.stdout + result.stderr
        print(f"📤 Mill output:\n{output[:500]}...")

        # Check for errors
        if result.returncode != 0:
            state['error_log'] = f"Mill execution failed (exit code {result.returncode}):\n{output}"
            state['is_success'] = False
            return state

        # Check for compilation errors or UNSAT
        if "Error" in output or "error" in output:
            state['error_log'] = f"Compilation error detected:\n{output}"
            state['is_success'] = False
            return state

        if "UNSAT" in output or "unsat" in output:
            state['error_log'] = f"SMT solver returned UNSAT (no satisfying solution):\n{output}"
            state['is_success'] = False
            return state

        # Extract instruction sequence
        # Match lines like "0: addi x1 x2 10" or "[308] 0: addi x1 x2 10"
        instruction_lines = []
        for line in output.split('\n'):
            # Look for instruction format: number followed by colon, then instruction mnemonic
            match = re.search(r'(\d+:\s+\w+.*)', line)
            if match:
                instruction_lines.append(match.group(1))

        if instruction_lines:
            state['instructions'] = '\n'.join(instruction_lines)
            state['is_success'] = True
            state['error_log'] = ''
            print(f"✅ Success! Generated {len(instruction_lines)} instructions")
        else:
            state['error_log'] = "No valid instruction sequence found in output"
            state['is_success'] = False

    except subprocess.TimeoutExpired:
        state['error_log'] = "Execution timeout (>60s)"
        state['is_success'] = False
    except Exception as e:
        state['error_log'] = f"Execution error: {str(e)}"
        state['is_success'] = False

    return state


# ==================== Node 4: Difftest ====================
def difftest_node(state: AgentState, cfg: Dict[str, Any] | None = None) -> AgentState:
    """
    Run XiangShan difftest pipeline:
      1. cp test.bin -> nexus_am_test_dir/output.bin
      2. Build workload with nexus-am (make ARCH=<arch>)
      3. Run XiangShan emulator with NEMU co-simulation

    cfg: merged config dict (CLI overrides on top of config.yaml defaults).
         Falls back to the module-level DIFFTEST_CFG when not provided.
    """
    if cfg is None:
        cfg = DIFFTEST_CFG

    if not cfg.get("enabled", False):
        print("⏭️  [Difftest] Disabled in config, skipping.")
        state['difftest_passed'] = False
        state['difftest_log'] = ""
        return state

    print("🔬 [Difftest] Starting XiangShan difftest pipeline...")

    test_bin = Path(cfg["test_bin"])
    nexus_dir = Path(cfg["nexus_am_test_dir"])
    arch = cfg["nexus_am_arch"]
    emu_bin = cfg["emu_bin"]
    workload_rel = cfg["workload_bin"]
    diff_so = cfg["diff_so"]
    emu_log = cfg["emu_log"]

    state['difftest_log'] = emu_log

    # Open the log file immediately so it always exists when we report its path.
    # All three steps write their stdout/stderr here for unified debugging.
    log_path = Path(emu_log)
    log_path.parent.mkdir(parents=True, exist_ok=True)

    with open(log_path, "w") as log_f:
        def _log(msg: str) -> None:
            log_f.write(msg + "\n")
            log_f.flush()

        _log(f"=== XiangShan Difftest Log ===")
        _log(f"test_bin:    {test_bin}")
        _log(f"nexus_dir:   {nexus_dir}")
        _log(f"emu_bin:     {emu_bin}")
        _log(f"workload:    {nexus_dir / workload_rel}")
        _log(f"diff_so:     {diff_so}")
        _log("")

        # --- Step 1: Run test.bin to generate output.bin ---
        output_bin = nexus_dir / "output.bin"
        try:
            _log(f"--- Step 1: cp {test_bin} {output_bin} ---")
            print(f"  [1/3] cp {test_bin} -> {output_bin}")
            result = subprocess.run(
                ["cp", str(test_bin), str(output_bin)],
                cwd=str(nexus_dir),
                capture_output=True,
                text=True,
                timeout=30,
            )
            _log(result.stdout)
            _log(result.stderr)
            if result.returncode != 0:
                _log(f"FAILED (exit {result.returncode})")
                state['error_log'] = (
                    f"[Difftest] test.bin step failed (exit {result.returncode}):\n"
                    + result.stdout + result.stderr
                )
                state['difftest_passed'] = False
                return state
            _log("OK")
        except subprocess.TimeoutExpired:
            _log("TIMEOUT")
            state['error_log'] = "[Difftest] test.bin execution timed out"
            state['difftest_passed'] = False
            return state
        except Exception as e:
            _log(f"EXCEPTION: {e}")
            state['error_log'] = f"[Difftest] test.bin execution error: {e}"
            state['difftest_passed'] = False
            return state

        # --- Step 2: make ARCH=<arch> inside nexus_am_test_dir ---
        try:
            _log(f"\n--- Step 2: make ARCH={arch} (cwd={nexus_dir}) ---")
            print(f"  [2/3] Building nexus-am workload (make ARCH={arch})")
            result = subprocess.run(
                ["make", f"ARCH={arch}"],
                cwd=str(nexus_dir),
                capture_output=True,
                text=True,
                timeout=120,
            )
            _log(result.stdout)
            _log(result.stderr)
            if result.returncode != 0:
                _log(f"FAILED (exit {result.returncode})")
                state['error_log'] = (
                    f"[Difftest] make failed (exit {result.returncode}):\n"
                    + result.stdout + result.stderr
                )
                state['difftest_passed'] = False
                return state
            _log("OK")
            print(f"  [2/3] Build succeeded")
        except subprocess.TimeoutExpired:
            _log("TIMEOUT")
            state['error_log'] = "[Difftest] nexus-am make timed out"
            state['difftest_passed'] = False
            return state
        except Exception as e:
            _log(f"EXCEPTION: {e}")
            state['error_log'] = f"[Difftest] make error: {e}"
            state['difftest_passed'] = False
            return state

        # --- Step 3: Run XiangShan emulator ---
        workload_bin = nexus_dir / workload_rel
        emu_cmd = [
            str(emu_bin),
            "-i", str(workload_bin),
            "--diff", str(diff_so),
        ]
        try:
            _log(f"\n--- Step 3: {' '.join(emu_cmd)} ---")
            print(f"  [3/3] Running XiangShan emu, log -> {emu_log}")
            result = subprocess.run(
                emu_cmd,
                cwd=str(nexus_dir),
                stdout=log_f,
                stderr=log_f,
                text=True,
                timeout=600,
            )
            log_f.flush()
            if result.returncode == 0:
                _log("\nPASSED")
                print(f"✅ [Difftest] Passed! Log: {emu_log}")
                state['difftest_passed'] = True
                state['error_log'] = ""
            else:
                _log(f"\nFAILED (exit {result.returncode})")
                # Read last 40 lines for inline error context
                try:
                    with open(log_path) as lf:
                        tail_str = "".join(lf.readlines()[-40:])
                except Exception:
                    tail_str = "(could not read log)"
                state['error_log'] = (
                    f"[Difftest] emu exited with code {result.returncode}.\n"
                    f"Last lines of {emu_log}:\n{tail_str}"
                )
                state['difftest_passed'] = False
                print(f"❌ [Difftest] Failed (exit {result.returncode}). See {emu_log}")
        except subprocess.TimeoutExpired:
            _log("TIMEOUT (>600s)")
            state['error_log'] = "[Difftest] emu timed out (>600s)"
            state['difftest_passed'] = False
        except Exception as e:
            _log(f"EXCEPTION: {e}")
            state['error_log'] = f"[Difftest] emu error: {e}"
            state['difftest_passed'] = False

    return state


# ==================== Conditional Edge: Decide ====================
def should_retry(state: AgentState) -> Literal["generate", "end"]:
    """
    Decision logic: retry if failed and under max retries, otherwise end.
    """
    if state['is_success']:
        return "end"
    elif state['retry_count'] < MAX_RETRIES:
        print(f"⚠️  Failed. Retrying... ({state['retry_count']}/{MAX_RETRIES})")
        return "generate"
    else:
        print(f"❌ Max retries reached. Giving up.")
        return "end"


# ==================== Graph Construction ====================
def build_agent_graph():
    """
    Build the LangGraph state machine.
    """
    workflow = StateGraph(AgentState)

    # Add nodes
    workflow.add_node("retrieve", retrieve_node)
    workflow.add_node("generate", generate_node)
    workflow.add_node("execute", execute_node)
    workflow.add_node("difftest", difftest_node)

    # Add edges
    workflow.set_entry_point("retrieve")
    workflow.add_edge("retrieve", "generate")
    workflow.add_edge("generate", "execute")
    workflow.add_conditional_edges(
        "execute",
        should_retry,
        {
            "generate": "generate",
            "end": "difftest",   # on success / max-retries, always run difftest
        }
    )
    workflow.add_edge("difftest", END)

    return workflow.compile()


# ==================== Main Entry Point ====================
def run_agent(user_input: str) -> dict:
    """
    Run the agent with natural language input.
    Returns final state with instructions or error.
    """
    print(f"\n{'='*60}")
    print(f"🚀 RVProbe Agent Starting")
    print(f"{'='*60}")
    print(f"Input: {user_input}\n")

    # Initialize state
    initial_state = AgentState(
        user_input=user_input,
        dsl_code="",
        error_log="",
        retry_count=0,
        is_success=False,
        instructions="",
        retrieved_docs="",
        difftest_log="",
        difftest_passed=False,
    )

    # Build and run graph
    graph = build_agent_graph()
    final_state = graph.invoke(initial_state)

    print(f"\n{'='*60}")
    if final_state['is_success']:
        print("✅ Agent Succeeded!")
        print(f"{'='*60}")
        print("\n📋 Generated Instructions:")
        print(final_state['instructions'])
        print(f"\n📁 Test.scala saved to: {TEST_FILE_PATH}")
        print(f"📁 Binary saved to: {OUTPUT_BIN_PATH}")
    else:
        print("❌ Agent Failed!")
        print(f"{'='*60}")
        print(f"\n❗ Error Log:\n{final_state['error_log']}")
        print("\n⚠️  No satisfying constraint solution found or compilation error.")

    if DIFFTEST_CFG.get("enabled", False):
        if final_state.get('difftest_passed'):
            print("\n🔬 XiangShan Difftest: ✅ PASSED")
        else:
            print("\n🔬 XiangShan Difftest: ❌ FAILED")
        if final_state.get('difftest_log'):
            print(f"   Log: {final_state['difftest_log']}")
    print(f"{'='*60}\n")

    return final_state


if __name__ == "__main__":
    import sys
    import argparse

    parser = argparse.ArgumentParser(
        prog="agent.py",
        description="RVProbe Agent - Automated Verification Generator",
    )
    subparsers = parser.add_subparsers(dest="command", metavar="COMMAND")

    # --- subcommand: run ---
    run_parser = subparsers.add_parser(
        "run",
        help="Generate RISC-V instructions from a natural language description",
    )
    run_parser.add_argument(
        "request",
        nargs="+",
        help='Natural language constraint description, e.g. "Generate 20 ADDI instructions"',
    )
    run_parser.add_argument(
        "--no-difftest",
        action="store_true",
        help="Skip the XiangShan difftest step even if enabled in config",
    )

    # --- subcommand: difftest ---
    difftest_parser = subparsers.add_parser(
        "difftest",
        help="Run XiangShan difftest on an already-generated test.bin (skips LLM generation)",
    )
    difftest_parser.add_argument(
        "--test-bin",
        metavar="PATH",
        default=None,
        help=f"Override path to test.bin (default: value in config.yaml, currently {DIFFTEST_CFG.get('test_bin')})",
    )

    args = parser.parse_args()

    # Default to 'run' with a demo request when called with no arguments
    if args.command is None:
        parser.print_help()
        sys.exit(0)

    # Build the final config: config.yaml defaults <- CLI overrides (CLI wins)
    def _build_cfg(**cli_overrides) -> Dict[str, Any]:
        merged = dict(DIFFTEST_CFG)          # copy of yaml defaults
        merged.update({k: v for k, v in cli_overrides.items() if v is not None})
        return merged

    if args.command == "difftest":
        final_cfg = _build_cfg(test_bin=args.test_bin)

        _state = AgentState(
            user_input="", dsl_code="", error_log="",
            retry_count=0, is_success=True, instructions="",
            retrieved_docs="", difftest_log="", difftest_passed=False,
        )
        _result = difftest_node(_state, cfg=final_cfg)
        print(f"\n{'='*60}")
        if _result['difftest_passed']:
            print("🔬 XiangShan Difftest: ✅ PASSED")
        else:
            print("🔬 XiangShan Difftest: ❌ FAILED")
            if _result['error_log']:
                print(f"\n❗ {_result['error_log']}")
        if _result['difftest_log']:
            print(f"   Log: {_result['difftest_log']}")
        print(f"{'='*60}\n")
        sys.exit(0 if _result['difftest_passed'] else 1)

    if args.command == "run":
        # --no-difftest overrides config.yaml's enabled flag
        final_cfg = _build_cfg(enabled=False if args.no_difftest else None)
        # Temporarily apply to module-level cfg so run_agent -> difftest_node picks it up
        DIFFTEST_CFG.update(final_cfg)
        run_agent(" ".join(args.request))
