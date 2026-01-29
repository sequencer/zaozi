#!/usr/bin/env python3
"""
RVProbe Agent - Automated Verification Generator
Converts natural language intent to Scala DSL constraint code via LLM-in-the-loop.
"""

import os
import subprocess
import re
from typing import TypedDict, Literal
from pathlib import Path

from dotenv import load_dotenv
from langgraph.graph import StateGraph, END
from langchain_openai import ChatOpenAI

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
MILL_COMMAND = ["mill", "rvprobe.runMain", "me.jiuyang.rvprobe.agent.Test", str(OUTPUT_BIN_PATH)]

# LLM Configuration from environment variables
# Support both LLM_* and OPENAI_* for backward compatibility
LLM_API_KEY = os.getenv("LLM_API_KEY") or os.getenv("OPENAI_API_KEY")
LLM_API_BASE = os.getenv("LLM_API_BASE") or os.getenv("OPENAI_API_BASE")
LLM_MODEL = os.getenv("LLM_MODEL") or os.getenv("OPENAI_MODEL", "gpt-4o")


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


# ==================== DSL API Documentation (Mock Retrieval) ====================
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

## Opcode Constraints (Examples)
- `isAddi()` - ADDI instruction
- `isSlliRV64I()` - SLLI instruction (RV64I)
- `isAddw()` - ADDW instruction
- `isSub()` - SUB instruction
- `isLui()` - LUI instruction
- `isBeq()` - BEQ instruction
- `isLw()` - LW instruction
- `isSw()` - SW instruction

## Argument Constraints
- `rdRange(min, max)` - Destination register range
- `rs1Range(min, max)` - Source register 1 range
- `rs2Range(min, max)` - Source register 2 range
- `immRange(min, max)` - Immediate value range

Constraints can be combined with `&` (logical AND):
```scala
rdRange(1, 32) & rs1Range(1, 32) & immRange(-2048, 2047)
```

## Instruction Sets
- `isRV64GC()` - RV64 with G+C extensions
- `isRV64G()` - RV64 base with IMAFD
- `isRV32I()` - RV32 base integer

## Example
```scala
object test extends RVGenerator:
  val sets = isRV64GC()
  def constraints() =
    (0 until 10).foreach { i =>
      instruction(i, isAddi()) {
        rdRange(1, 16) & rs1Range(1, 16) & immRange(0, 100)
      }
    }
```
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

// Run with: mill rvprobe.runMain me.jiuyang.rvprobe.agent.Test out/test.bin
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

    # Add edges
    workflow.set_entry_point("retrieve")
    workflow.add_edge("retrieve", "generate")
    workflow.add_edge("generate", "execute")
    workflow.add_conditional_edges(
        "execute",
        should_retry,
        {
            "generate": "generate",
            "end": END
        }
    )

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
        instructions=""
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
    print(f"{'='*60}\n")

    return final_state


if __name__ == "__main__":
    import sys

    # Example usage
    if len(sys.argv) > 1:
        user_request = " ".join(sys.argv[1:])
    else:
        # Default example
        user_request = "Generate 20 ADDI instructions where rd and rs1 are both in range 1-31"

    run_agent(user_request)
