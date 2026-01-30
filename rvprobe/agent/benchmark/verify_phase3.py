"""
Phase 3 Verification Script

Tests:
1. AssemblyParser can parse various instruction formats
2. ConstraintChecker can validate constraints
3. MetricsCalculator produces correct scores
4. End-to-end: Runner + Evaluator integration
"""

import sys
import os
from dotenv import load_dotenv

# Load environment variables
load_dotenv()

# Add project root to path
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

from benchmark.test_suite.test_cases import get_case_by_id
from benchmark.test_suite.schemas import BenchmarkConfig
from benchmark.runners.direct_llm_runner import DirectLLMRunner
from benchmark.evaluators.assembly_parser import AssemblyParser
from benchmark.evaluators.constraint_checker import ConstraintChecker
from benchmark.evaluators.metrics import MetricsCalculator

# Get model from environment
LLM_MODEL = os.getenv("LLM_MODEL", "gpt-4o")


def test_assembly_parser():
    """Test 1: AssemblyParser functionality."""
    print("=" * 60)
    print("Test 1: AssemblyParser")
    print("=" * 60)

    test_assembly = """
0: addi x1 x2 10
1: add x3 x4 x5
2: lw x6 100(x7)
3: sw x8 200(x9)
4: beq x10 x11 50
5: slli x12 x13 5
"""

    parser = AssemblyParser()
    instructions = parser.parse(test_assembly)

    print(f"✓ Parsed {len(instructions)} instructions")
    assert len(instructions) == 6, f"Expected 6 instructions, got {len(instructions)}"

    # Check specific instructions
    assert instructions[0].mnemonic == "addi"
    assert instructions[0].rd == 1
    assert instructions[0].rs1 == 2
    assert instructions[0].imm == 10
    print(f"✓ Instruction 0: addi x1 x2 10 parsed correctly")

    assert instructions[1].mnemonic == "add"
    assert instructions[1].rd == 3
    assert instructions[1].rs1 == 4
    assert instructions[1].rs2 == 5
    print(f"✓ Instruction 1: add x3 x4 x5 parsed correctly")

    assert instructions[2].mnemonic == "lw"
    assert instructions[2].rd == 6
    assert instructions[2].rs1 == 7
    assert instructions[2].imm == 100
    print(f"✓ Instruction 2: lw x6 100(x7) parsed correctly")

    print(f"✓ All instructions parsed successfully\n")


def test_constraint_checker():
    """Test 2: ConstraintChecker functionality."""
    print("=" * 60)
    print("Test 2: ConstraintChecker")
    print("=" * 60)

    test_case = get_case_by_id("TC-S01")
    print(f"Test case: {test_case.id}")
    print(f"Description: {test_case.description}")

    # Good assembly
    good_assembly = "\n".join([
        f"{i}: addi x{i+1} x0 {i*10}"
        for i in range(10)
    ])

    checker = ConstraintChecker()
    result = checker.check(good_assembly, test_case)

    print(f"\n--- Good Assembly ---")
    print(f"✓ Count match: {result.count_match}")
    print(f"✓ Type correctness: {result.type_correctness:.2%}")
    print(f"✓ Constraint satisfaction: {result.constraint_satisfaction_rate:.2%}")

    assert result.count_match is True
    assert result.type_correctness == 1.0
    assert result.constraint_satisfaction_rate == 1.0

    # Bad assembly
    bad_assembly = """
0: addi x15 x0 10
1: sub x1 x2 x3
"""

    result2 = checker.check(bad_assembly, test_case)

    print(f"\n--- Bad Assembly ---")
    print(f"✓ Count match: {result2.count_match} (should be False)")
    print(f"✓ Type correctness: {result2.type_correctness:.2%} (should be < 100%)")
    print(f"✓ Register violations: {result2.register_violations} (should be > 0)")
    print(f"✓ Violations detected: {len(result2.details)}")

    assert result2.count_match is False
    assert result2.type_correctness < 1.0
    assert result2.register_violations > 0

    print("\n")


def test_metrics_calculator():
    """Test 3: MetricsCalculator."""
    print("=" * 60)
    print("Test 3: MetricsCalculator")
    print("=" * 60)

    from benchmark.test_suite.schemas import (
        RunResult,
        EfficiencyMetrics,
        RobustnessMetrics,
        FailureMode
    )

    test_case = get_case_by_id("TC-S01")

    # Create a sample result
    assembly = "\n".join([
        f"{i}: addi x{i+1} x0 {i*10}"
        for i in range(10)
    ])

    result = RunResult(
        test_id=test_case.id,
        method="test",
        success=True,
        assembly=assembly,
        efficiency=EfficiencyMetrics(
            total_time=1.0,
            llm_time=0.8,
            llm_call_count=1,
            total_prompt_tokens=100,
            total_completion_tokens=50
        ),
        robustness=RobustnessMetrics(
            is_success=True,
            failure_mode=FailureMode.NONE,
            timed_out=False,
            first_attempt_success=True
        )
    )

    calculator = MetricsCalculator()
    correctness = calculator.calculate_correctness(result, test_case)

    print(f"✓ Correctness metrics calculated")
    print(f"  Valid syntax: {correctness.is_valid_syntax}")
    print(f"  Count match: {correctness.count_match}")
    print(f"  Type correctness: {correctness.type_correctness:.2%}")
    print(f"  Constraint satisfaction: {correctness.constraint_satisfaction_rate:.2%}")
    print(f"  Correctness score: {correctness.correctness_score:.4f}")

    assert correctness.is_valid_syntax is True
    assert correctness.count_match is True
    assert correctness.correctness_score == 1.0

    print(f"✓ Perfect score achieved (1.0000)\n")


def test_end_to_end_integration():
    """Test 4: End-to-end runner + evaluator integration."""
    print("=" * 60)
    print("Test 4: End-to-End Integration")
    print("=" * 60)

    config = BenchmarkConfig(
        llm_model=LLM_MODEL,
        llm_temperature=0.0,
        timeout_seconds=60
    )

    # Use simplest test case
    test_case = get_case_by_id("TC-S01")
    print(f"Test case: {test_case.id}")

    # Run with DirectLLM
    runner = DirectLLMRunner(config, include_docs=False)
    run_result = runner.run(test_case)

    print(f"\n✓ Runner completed")
    print(f"  Success: {run_result.success}")
    print(f"  Assembly lines: {len(run_result.assembly.split(chr(10))) if run_result.assembly else 0}")

    # Evaluate with MetricsCalculator
    calculator = MetricsCalculator()
    calculator.evaluate_result(run_result, test_case)

    print(f"\n✓ Evaluation completed")
    print(f"  Correctness score: {run_result.correctness.correctness_score:.4f}")
    print(f"  Type correctness: {run_result.correctness.type_correctness:.2%}")
    print(f"  Constraint satisfaction: {run_result.correctness.constraint_satisfaction_rate:.2%}")
    print(f"  Register violations: {run_result.correctness.register_constraint_violations}")

    assert run_result.correctness is not None
    assert run_result.correctness.correctness_score >= 0.0
    assert run_result.correctness.correctness_score <= 1.0

    print(f"\n✓ Integration test passed!\n")


def run_all_tests():
    """Run all Phase 3 verification tests."""
    print("\n" + "=" * 60)
    print("PHASE 3 VERIFICATION")
    print("=" * 60 + "\n")

    try:
        test_assembly_parser()
        test_constraint_checker()
        test_metrics_calculator()
        test_end_to_end_integration()

        print("=" * 60)
        print("ALL TESTS PASSED ✓")
        print("=" * 60)
        print("\nPhase 3 implementation is verified and ready!")
        print("\nCompleted components:")
        print("  ✓ AssemblyParser - Parse RISC-V assembly")
        print("  ✓ ConstraintChecker - Validate constraints")
        print("  ✓ MetricsCalculator - Compute correctness scores")
        print("  ✓ End-to-end integration - Runner + Evaluator")
        print("\nNext steps:")
        print("  - Phase 4: Implement benchmark orchestrator")
        print("  - Phase 5: Implement visualization and reporting")
        print("\n")

        return True

    except AssertionError as e:
        print(f"\n❌ TEST FAILED: {e}")
        import traceback
        traceback.print_exc()
        return False
    except Exception as e:
        print(f"\n❌ ERROR: {e}")
        import traceback
        traceback.print_exc()
        return False


if __name__ == "__main__":
    success = run_all_tests()
    sys.exit(0 if success else 1)
