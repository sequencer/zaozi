"""
DirectLLMRunner - Method B: Pure LLM generation without verification

Directly calls LLM to generate RISC-V assembly instructions without:
- RAG retrieval (optional variant)
- Scala DSL generation
- Mill compilation
- Z3 verification
- Auto-retry

Supports two variants:
- no_docs: Pure LLM without documentation
- with_docs: LLM with constraint documentation (simulates perfect RAG)
"""

import os
import re
import time
from typing import Optional
import sys

# Add project paths
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '../../..')))
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '../..')))

from benchmark.runners.base_runner import BaseRunner
from benchmark.test_suite.schemas import (
    TestCase,
    RunResult,
    CorrectnessMetrics,
    EfficiencyMetrics,
    RobustnessMetrics,
    FailureMode
)
from benchmark.utils.timing import MultiTimer

# Import LLM
try:
    from langchain_openai import ChatOpenAI
    from dotenv import load_dotenv
    load_dotenv()
    LLM_AVAILABLE = True
except ImportError:
    LLM_AVAILABLE = False
    print("⚠️ Warning: langchain_openai not available")


# RISC-V instruction documentation for "with_docs" variant
RISCV_DOCS = """
# RISC-V Assembly Instruction Reference

## Instruction Format
All instructions should be output in the format:
```
<index>: <mnemonic> <operands>
```

Example:
```
0: addi x1 x2 10
1: add x3 x4 x5
2: lw x6 0(x7)
```

## Common Instructions

### Arithmetic (I-type with immediate)
- **addi rd rs1 imm** - Add immediate. rd = rs1 + imm
  - rd, rs1: x0-x31 (register range)
  - imm: -2048 to 2047 (12-bit signed immediate)

- **addw rd rs1 imm** - Add word immediate (RV64). rd = sext((rs1 + imm)[31:0])
  - rd, rs1: x0-x31
  - imm: -2048 to 2047

- **slti rd rs1 imm** - Set less than immediate. rd = (rs1 < imm) ? 1 : 0
  - rd, rs1: x0-x31
  - imm: -2048 to 2047

- **andi rd rs1 imm** - AND immediate. rd = rs1 & imm
  - rd, rs1: x0-x31
  - imm: -2048 to 2047

- **ori rd rs1 imm** - OR immediate. rd = rs1 | imm
  - rd, rs1: x0-x31
  - imm: -2048 to 2047

- **xori rd rs1 imm** - XOR immediate. rd = rs1 ^ imm
  - rd, rs1: x0-x31
  - imm: -2048 to 2047

### Arithmetic (R-type, register-register)
- **add rd rs1 rs2** - Add. rd = rs1 + rs2
  - rd, rs1, rs2: x0-x31

- **addw rd rs1 rs2** - Add word (RV64). rd = sext((rs1 + rs2)[31:0])
  - rd, rs1, rs2: x0-x31

- **sub rd rs1 rs2** - Subtract. rd = rs1 - rs2
  - rd, rs1, rs2: x0-x31

- **subw rd rs1 rs2** - Subtract word (RV64). rd = sext((rs1 - rs2)[31:0])
  - rd, rs1, rs2: x0-x31

### Logical
- **and rd rs1 rs2** - AND. rd = rs1 & rs2
  - rd, rs1, rs2: x0-x31

- **or rd rs1 rs2** - OR. rd = rs1 | rs2
  - rd, rs1, rs2: x0-x31

- **xor rd rs1 rs2** - XOR. rd = rs1 ^ rs2
  - rd, rs1, rs2: x0-x31

### Shift
- **slli rd rs1 shamt** - Shift left logical immediate. rd = rs1 << shamt
  - rd, rs1: x0-x31
  - shamt: 0-63 (for RV64) or 0-31 (for RV32)

- **srli rd rs1 shamt** - Shift right logical immediate. rd = rs1 >> shamt
  - rd, rs1: x0-x31
  - shamt: 0-63 (for RV64) or 0-31 (for RV32)

- **srai rd rs1 shamt** - Shift right arithmetic immediate. rd = rs1 >>> shamt
  - rd, rs1: x0-x31
  - shamt: 0-63 (for RV64) or 0-31 (for RV32)

### Load/Store
- **lw rd offset(rs1)** - Load word. rd = mem[rs1 + offset][31:0]
  - rd, rs1: x0-x31
  - offset: -2048 to 2047

- **sw rs2 offset(rs1)** - Store word. mem[rs1 + offset] = rs2[31:0]
  - rs1, rs2: x0-x31
  - offset: -2048 to 2047

- **ld rd offset(rs1)** - Load doubleword (RV64). rd = mem[rs1 + offset]
  - rd, rs1: x0-x31
  - offset: -2048 to 2047

- **sd rs2 offset(rs1)** - Store doubleword (RV64). mem[rs1 + offset] = rs2
  - rs1, rs2: x0-x31
  - offset: -2048 to 2047

### Comparison
- **slt rd rs1 rs2** - Set less than. rd = (rs1 < rs2) ? 1 : 0
  - rd, rs1, rs2: x0-x31

- **sltu rd rs1 rs2** - Set less than unsigned. rd = (rs1 < rs2) ? 1 : 0 (unsigned)
  - rd, rs1, rs2: x0-x31

### Branch
- **beq rs1 rs2 offset** - Branch if equal. if (rs1 == rs2) pc += offset
  - rs1, rs2: x0-x31
  - offset: -4096 to 4094 (even values)

- **bne rs1 rs2 offset** - Branch if not equal. if (rs1 != rs2) pc += offset
  - rs1, rs2: x0-x31
  - offset: -4096 to 4094 (even values)

- **blt rs1 rs2 offset** - Branch if less than. if (rs1 < rs2) pc += offset
  - rs1, rs2: x0-x31
  - offset: -4096 to 4094 (even values)

- **bge rs1 rs2 offset** - Branch if greater or equal. if (rs1 >= rs2) pc += offset
  - rs1, rs2: x0-x31
  - offset: -4096 to 4094 (even values)

### Upper Immediate
- **lui rd imm** - Load upper immediate. rd = imm << 12
  - rd: x0-x31
  - imm: 0 to 1048575 (20-bit unsigned)

## Register Naming
Registers can be referred to by number (x0-x31) or ABI names:
- x0 = zero (always 0)
- x1 = ra (return address)
- x2 = sp (stack pointer)
- x3 = gp (global pointer)
- x4 = tp (thread pointer)
- x5-x7 = t0-t2 (temporaries)
- x8 = s0/fp (saved register / frame pointer)
- x9 = s1 (saved register)
- x10-x17 = a0-a7 (function arguments/return values)
- x18-x27 = s2-s11 (saved registers)
- x28-x31 = t3-t6 (temporaries)

For benchmark purposes, use numeric notation (x1, x2, etc.).
"""


class DirectLLMRunner(BaseRunner):
    """
    Runner for Method B: Direct LLM generation.

    Generates RISC-V assembly directly from LLM without intermediate DSL,
    compilation, or verification steps.
    """

    def __init__(self, config, include_docs: bool = False):
        """
        Initialize DirectLLMRunner.

        Args:
            config: BenchmarkConfig with settings
            include_docs: If True, include RISC-V docs in prompt (with_docs variant)
                         If False, rely on LLM's internal knowledge (no_docs variant)
        """
        super().__init__(config)

        if not LLM_AVAILABLE:
            raise RuntimeError("LLM not available. Cannot create DirectLLMRunner.")

        self.include_docs = include_docs

        # Initialize LLM
        llm_kwargs = {
            "model": config.llm_model,
            "temperature": config.llm_temperature,
            "max_tokens": config.llm_max_tokens
        }

        # Add API key and base URL from environment if available
        llm_api_key = os.getenv("LLM_API_KEY") or os.getenv("OPENAI_API_KEY")
        llm_api_base = os.getenv("LLM_API_BASE") or os.getenv("OPENAI_API_BASE")

        if llm_api_key:
            llm_kwargs["api_key"] = llm_api_key
        if llm_api_base:
            llm_kwargs["base_url"] = llm_api_base

        self.llm = ChatOpenAI(**llm_kwargs)

    def run(self, test_case: TestCase) -> RunResult:
        """
        Run direct LLM generation for a test case.

        Args:
            test_case: The test case to execute

        Returns:
            RunResult with generated assembly and metrics
        """
        variant_name = "with_docs" if self.include_docs else "no_docs"
        method_name = f"direct_llm_{variant_name}"

        print(f"\n{'='*60}")
        print(f"[DirectLLMRunner-{variant_name}] Running test case: {test_case.id}")
        print(f"Description: {test_case.description}")
        print(f"{'='*60}\n")

        # Initialize result
        result = self._create_result_template(test_case, method=method_name)

        # Timer
        timer = MultiTimer()
        timer.start("total")

        try:
            # Build prompt
            system_prompt = self._build_system_prompt()
            user_prompt = self._build_user_prompt(test_case)

            messages = [
                {"role": "system", "content": system_prompt},
                {"role": "user", "content": user_prompt}
            ]

            # Call LLM
            timer.start("llm")
            response = self.llm.invoke(messages)
            timer.stop("llm")

            # Extract assembly from response
            assembly = self._extract_assembly(response.content)

            # Store results
            result.success = len(assembly.strip()) > 0
            result.assembly = assembly
            result.raw_output = response.content

            # Build robustness metrics
            result.robustness = RobustnessMetrics(
                is_success=result.success,
                failure_mode=FailureMode.NONE if result.success else FailureMode.INVALID_ASSEMBLY,
                timed_out=False,
                first_attempt_success=result.success
            )

            # Extract token usage from response
            prompt_tokens = 0
            completion_tokens = 0
            if hasattr(response, 'response_metadata'):
                usage = response.response_metadata.get('token_usage', {})
                prompt_tokens = usage.get('prompt_tokens', 0)
                completion_tokens = usage.get('completion_tokens', 0)

            # Calculate cost
            estimated_cost = (
                (prompt_tokens / 1_000_000) * self.config.prompt_token_cost +
                (completion_tokens / 1_000_000) * self.config.completion_token_cost
            )

        except Exception as e:
            result.success = False
            result.error_log = f"DirectLLMRunner exception: {str(e)}"
            result.robustness = RobustnessMetrics(
                is_success=False,
                failure_mode=FailureMode.LLM_ERROR,
                timed_out=False,
                first_attempt_success=False
            )
            prompt_tokens = 0
            completion_tokens = 0
            estimated_cost = 0.0
            print(f"❌ Exception in DirectLLMRunner: {e}")
            import traceback
            traceback.print_exc()

        finally:
            timer.stop("total")

        # Build efficiency metrics
        result.efficiency = EfficiencyMetrics(
            total_time=timer.get("total"),
            llm_time=timer.get("llm"),
            compilation_time=None,  # Not applicable for direct LLM
            verification_time=None,  # Not applicable for direct LLM
            llm_call_count=1,
            total_prompt_tokens=prompt_tokens,
            total_completion_tokens=completion_tokens,
            estimated_cost=estimated_cost,
            retry_count=0  # No retries in direct LLM approach
        )

        # Print summary
        print(f"\n{'='*60}")
        if result.success:
            print(f"✅ [DirectLLMRunner-{variant_name}] Success!")
            instruction_count = len(result.assembly.strip().split('\n')) if result.assembly else 0
            print(f"   Generated {instruction_count} instructions")
        else:
            print(f"❌ [DirectLLMRunner-{variant_name}] Failed!")
            print(f"   Failure mode: {result.robustness.failure_mode.value}")
        print(f"   Total time: {timer.get('total'):.2f}s")
        print(f"   LLM time: {timer.get('llm'):.2f}s")
        print(f"   Tokens: {prompt_tokens} prompt + {completion_tokens} completion")
        print(f"   Cost: ${estimated_cost:.6f}")
        print(f"{'='*60}\n")

        return result

    def _build_system_prompt(self) -> str:
        """Build the system prompt for the LLM."""
        base_prompt = """You are an expert in RISC-V assembly programming.
Your task is to generate RISC-V assembly instructions that satisfy given constraints.

CRITICAL OUTPUT FORMAT:
1. Each instruction must be on its own line
2. Format: "<index>: <mnemonic> <operands>"
3. Index starts from 0 and increments by 1
4. Use numeric register notation (x1, x2, etc.)
5. Do NOT include any comments, labels, or explanations
6. Do NOT include markdown code blocks or any other formatting
7. Output ONLY the instructions, nothing else

Example output:
0: addi x1 x0 10
1: addi x2 x0 20
2: add x3 x1 x2
"""

        if self.include_docs:
            return base_prompt + "\n\n" + RISCV_DOCS
        else:
            return base_prompt

    def _build_user_prompt(self, test_case: TestCase) -> str:
        """Build the user prompt for a specific test case."""
        prompt = f"""Generate RISC-V assembly instructions for the following requirements:

{test_case.description}

Remember:
- Output format: "<index>: <mnemonic> <operands>"
- Start index from 0
- Generate EXACTLY the number of instructions specified
- Satisfy ALL constraints exactly
- No comments, no markdown, no explanations
- ONLY output the instructions
"""

        return prompt

    def _extract_assembly(self, llm_response: str) -> str:
        """
        Extract assembly instructions from LLM response.

        Args:
            llm_response: Raw LLM output

        Returns:
            Clean assembly instructions (one per line)
        """
        # Remove markdown code blocks if present
        cleaned = llm_response
        if "```" in cleaned:
            # Extract content between ```
            match = re.search(r'```(?:asm|assembly|riscv)?\n(.*?)```', cleaned, re.DOTALL)
            if match:
                cleaned = match.group(1)

        # Extract lines that look like instructions
        # Format: <number>: <mnemonic> <operands>
        instruction_pattern = r'^\s*(\d+:\s+\w+\s+.*?)$'

        instructions = []
        for line in cleaned.split('\n'):
            line = line.strip()
            if re.match(instruction_pattern, line):
                instructions.append(line)

        return '\n'.join(instructions)


def test_direct_llm_runner():
    """Quick test of DirectLLMRunner."""
    from benchmark.test_suite.test_cases import get_case_by_id
    from benchmark.test_suite.schemas import BenchmarkConfig

    print("Testing DirectLLMRunner...")

    config = BenchmarkConfig(
        llm_model="gpt-4o",
        llm_temperature=0.0,
        timeout_seconds=300
    )

    # Test both variants
    for include_docs in [False, True]:
        variant = "with_docs" if include_docs else "no_docs"
        print(f"\n{'='*60}")
        print(f"Testing variant: {variant}")
        print(f"{'='*60}")

        runner = DirectLLMRunner(config, include_docs=include_docs)
        print(f"Runner created: {runner}")

        # Test with simple case
        test_case = get_case_by_id("TC-S01")
        print(f"\nRunning test case: {test_case.id}")
        print(f"Description: {test_case.description}")

        result = runner.run(test_case)

        print("\n" + "="*60)
        print(f"RESULT ({variant}):")
        print("="*60)
        print(f"Success: {result.success}")
        print(f"Assembly lines: {len(result.assembly.split(chr(10))) if result.assembly else 0}")
        print(f"Total time: {result.efficiency.total_time:.2f}s")
        print(f"LLM time: {result.efficiency.llm_time:.2f}s")
        print(f"Tokens: {result.efficiency.total_prompt_tokens} + {result.efficiency.total_completion_tokens}")
        print(f"Cost: ${result.efficiency.estimated_cost:.6f}")
        if result.assembly:
            print(f"\nFirst 3 instructions:")
            for line in result.assembly.split('\n')[:3]:
                print(f"  {line}")


if __name__ == "__main__":
    test_direct_llm_runner()
