"""
15 test cases for benchmarking RISC-V instruction generation.

Categorized by difficulty: Simple (5), Medium (5), Complex (5).
"""

from typing import List
from .schemas import TestCase, Difficulty


def get_all_test_cases() -> List[TestCase]:
    """Return all 15 test cases."""
    return SIMPLE_CASES + MEDIUM_CASES + COMPLEX_CASES


# ============================================================================
# SIMPLE CASES (5 test cases)
# ============================================================================

TC_S01 = TestCase(
    id="TC-S01",
    difficulty=Difficulty.SIMPLE,
    category="arithmetic",
    description="Generate 10 ADDI instructions with rd in range 1-10",
    expected_count=10,
    instruction_types=["addi"],
    register_constraints={
        "rd": {"min": 1, "max": 11}  # x1 to x10 (max is exclusive in range checks)
    },
    immediate_constraints=None,  # No specific immediate constraints
    notes="Basic test with single instruction type and simple register constraint"
)

TC_S02 = TestCase(
    id="TC-S02",
    difficulty=Difficulty.SIMPLE,
    category="arithmetic",
    description="Generate 20 ADDI instructions with rd and rs1 in range 1-31, immediate in range -100 to 100",
    expected_count=20,
    instruction_types=["addi"],
    register_constraints={
        "rd": {"min": 1, "max": 32},
        "rs1": {"min": 1, "max": 32}
    },
    immediate_constraints={"min": -100, "max": 101},
    notes="Tests wider register range and immediate value constraints"
)

TC_S03 = TestCase(
    id="TC-S03",
    difficulty=Difficulty.SIMPLE,
    category="shift",
    description="Generate 15 SLLI instructions with shift amount in range 0-10",
    expected_count=15,
    instruction_types=["slli"],
    register_constraints={},
    immediate_constraints={"min": 0, "max": 11},  # Shift amount (shamt)
    notes="Tests shift instructions with bounded shift amount"
)

TC_S04 = TestCase(
    id="TC-S04",
    difficulty=Difficulty.SIMPLE,
    category="memory",
    description="Generate 10 LW instructions with rs1 in range 2-10",
    expected_count=10,
    instruction_types=["lw"],
    register_constraints={
        "rs1": {"min": 2, "max": 11}  # Base address register
    },
    immediate_constraints=None,
    notes="Basic load instruction test"
)

TC_S05 = TestCase(
    id="TC-S05",
    difficulty=Difficulty.SIMPLE,
    category="branch",
    description="Generate 8 BEQ instructions with rs1 and rs2 in range 1-15",
    expected_count=8,
    instruction_types=["beq"],
    register_constraints={
        "rs1": {"min": 1, "max": 16},
        "rs2": {"min": 1, "max": 16}
    },
    immediate_constraints=None,
    notes="Basic branch instruction test"
)

SIMPLE_CASES = [TC_S01, TC_S02, TC_S03, TC_S04, TC_S05]


# ============================================================================
# MEDIUM CASES (5 test cases)
# ============================================================================

TC_M01 = TestCase(
    id="TC-M01",
    difficulty=Difficulty.MEDIUM,
    category="mixed_arithmetic",
    description="Generate 50 mixed arithmetic instructions: 25 ADDI and 25 ADDW",
    expected_count=50,
    instruction_types=["addi", "addw"],
    register_constraints={},
    immediate_constraints=None,
    notes="Tests mixing two instruction types with expected distribution"
)

TC_M02 = TestCase(
    id="TC-M02",
    difficulty=Difficulty.MEDIUM,
    category="arithmetic",
    description="Generate 100 ADDI instructions with rd in range 1-5 and rs1 in range 10-20 (register partitioning)",
    expected_count=100,
    instruction_types=["addi"],
    register_constraints={
        "rd": {"min": 1, "max": 6},
        "rs1": {"min": 10, "max": 21}
    },
    immediate_constraints=None,
    notes="Tests non-overlapping register constraints (partitioning)"
)

TC_M03 = TestCase(
    id="TC-M03",
    difficulty=Difficulty.MEDIUM,
    category="mixed_arithmetic",
    description="Generate 60 mixed arithmetic instructions (ADDI/SLTI/ANDI) with immediate in range 0-255",
    expected_count=60,
    instruction_types=["addi", "slti", "andi"],
    register_constraints={},
    immediate_constraints={"min": 0, "max": 256},
    notes="Tests multiple instruction types with bounded immediate values"
)

TC_M04 = TestCase(
    id="TC-M04",
    difficulty=Difficulty.MEDIUM,
    category="memory",
    description="Generate 40 memory instructions: 20 LW and 20 SW",
    expected_count=40,
    instruction_types=["lw", "sw"],
    register_constraints={},
    immediate_constraints=None,
    notes="Tests load/store instruction mix"
)

TC_M05 = TestCase(
    id="TC-M05",
    difficulty=Difficulty.MEDIUM,
    category="mixed_shift_logic",
    description="Generate 75 mixed shift and logic instructions (SLLI/SRLI/XOR)",
    expected_count=75,
    instruction_types=["slli", "srli", "xor"],
    register_constraints={},
    immediate_constraints=None,
    notes="Tests shift and logical operations"
)

MEDIUM_CASES = [TC_M01, TC_M02, TC_M03, TC_M04, TC_M05]


# ============================================================================
# COMPLEX CASES (5 test cases)
# ============================================================================

TC_C01 = TestCase(
    id="TC-C01",
    difficulty=Difficulty.COMPLEX,
    category="arithmetic",
    description="Generate 200 ADDI instructions with strict constraints: rd and rs1 in range 1-8, immediate in range -50 to 50",
    expected_count=200,
    instruction_types=["addi"],
    register_constraints={
        "rd": {"min": 1, "max": 9},
        "rs1": {"min": 1, "max": 9}
    },
    immediate_constraints={"min": -50, "max": 51},
    notes="High volume with tight constraints on all parameters"
)

TC_C02 = TestCase(
    id="TC-C02",
    difficulty=Difficulty.COMPLEX,
    category="arithmetic",
    description="Generate 50 ADDI instructions with continuous RAW (Read-After-Write) dependencies: each instruction's rs1 should match the previous instruction's rd",
    expected_count=50,
    instruction_types=["addi"],
    register_constraints={},
    immediate_constraints=None,
    notes="Tests cross-instruction constraints (data dependency chains)"
)

TC_C03 = TestCase(
    id="TC-C03",
    difficulty=Difficulty.COMPLEX,
    category="highly_mixed",
    description="Generate 150 highly mixed instructions: 50 arithmetic (ADDI/ADD), 40 logic (AND/OR/XOR), 30 shift (SLLI/SRLI), and 30 branch (BEQ/BNE)",
    expected_count=150,
    instruction_types=["addi", "add", "and", "or", "xor", "slli", "srli", "beq", "bne"],
    register_constraints={},
    immediate_constraints=None,
    notes="Tests handling diverse instruction types with expected distribution"
)

TC_C04 = TestCase(
    id="TC-C04",
    difficulty=Difficulty.COMPLEX,
    category="arithmetic",
    description="Generate approximately 100 add-like instructions (ADDI, ADD, ADDW) with fuzzy count specification",
    expected_count=100,
    instruction_types=["addi", "add", "addw"],
    register_constraints={},
    immediate_constraints=None,
    notes="Tests fuzzy count handling (approximately 100, could be 95-105)"
)

TC_C05 = TestCase(
    id="TC-C05",
    difficulty=Difficulty.COMPLEX,
    category="stress_test",
    description="Generate 500 mixed instructions (all types) as a stress test for maximum volume",
    expected_count=500,
    instruction_types=[
        "addi", "add", "addw", "sub", "subw",
        "and", "or", "xor", "andi", "ori", "xori",
        "slli", "srli", "srai",
        "slti", "sltiu", "slt", "sltu",
        "lw", "sw", "ld", "sd",
        "beq", "bne", "blt", "bge"
    ],
    register_constraints={},
    immediate_constraints=None,
    notes="Maximum volume stress test with wide instruction variety"
)

COMPLEX_CASES = [TC_C01, TC_C02, TC_C03, TC_C04, TC_C05]


# ============================================================================
# Helper functions
# ============================================================================

def get_cases_by_difficulty(difficulty: Difficulty) -> List[TestCase]:
    """Get test cases filtered by difficulty."""
    return [tc for tc in get_all_test_cases() if tc.difficulty == difficulty]


def get_case_by_id(test_id: str) -> TestCase:
    """Get a specific test case by ID."""
    for tc in get_all_test_cases():
        if tc.id == test_id:
            return tc
    raise ValueError(f"Test case {test_id} not found")


def print_test_summary():
    """Print a summary of all test cases."""
    all_cases = get_all_test_cases()
    print(f"Total test cases: {len(all_cases)}")
    print(f"  Simple: {len(SIMPLE_CASES)}")
    print(f"  Medium: {len(MEDIUM_CASES)}")
    print(f"  Complex: {len(COMPLEX_CASES)}")
    print("\nTest case details:")
    for tc in all_cases:
        print(f"  {tc.id} ({tc.difficulty.value}): {tc.expected_count} instructions, "
              f"types={tc.instruction_types[:3]}{'...' if len(tc.instruction_types) > 3 else ''}")


if __name__ == "__main__":
    # Quick verification
    print_test_summary()
