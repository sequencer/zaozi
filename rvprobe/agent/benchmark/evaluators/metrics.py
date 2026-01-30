"""
Metrics Calculator for benchmark evaluation.

Computes correctness metrics by combining assembly parsing and constraint checking.
"""

import sys
import os
from typing import Optional

# Add project paths
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '../..')))

from benchmark.evaluators.assembly_parser import AssemblyParser
from benchmark.evaluators.constraint_checker import ConstraintChecker
from benchmark.test_suite.schemas import (
    TestCase,
    RunResult,
    CorrectnessMetrics
)


class MetricsCalculator:
    """
    Calculates correctness metrics for benchmark results.

    Combines assembly parsing and constraint checking to produce
    comprehensive correctness scores.
    """

    def __init__(self):
        self.parser = AssemblyParser()
        self.checker = ConstraintChecker()

    def calculate_correctness(self, run_result: RunResult,
                               test_case: TestCase) -> CorrectnessMetrics:
        """
        Calculate correctness metrics for a run result.

        Args:
            run_result: RunResult from a test execution
            test_case: TestCase with expected constraints

        Returns:
            CorrectnessMetrics with all correctness measurements
        """
        assembly_text = run_result.assembly

        # Handle empty or invalid assembly
        if not assembly_text or not assembly_text.strip():
            return self._create_failed_metrics("No assembly generated")

        # Parse assembly
        try:
            instructions = self.parser.parse(assembly_text)
        except Exception as e:
            return self._create_failed_metrics(f"Parse error: {str(e)}")

        if len(instructions) == 0:
            return self._create_failed_metrics("No valid instructions parsed")

        # Check syntax validity (all instructions parsed successfully)
        valid_count = sum(1 for instr in instructions if instr.is_valid)
        is_valid_syntax = (valid_count == len(instructions))

        # Check constraints
        try:
            check_result = self.checker.check(assembly_text, test_case)
        except Exception as e:
            return self._create_failed_metrics(f"Constraint check error: {str(e)}")

        # Build correctness metrics
        metrics = CorrectnessMetrics(
            is_valid_syntax=is_valid_syntax,
            constraint_satisfaction_rate=check_result.constraint_satisfaction_rate,
            count_match=check_result.count_match,
            type_correctness=check_result.type_correctness,
            register_constraint_violations=check_result.register_violations,
            immediate_constraint_violations=check_result.immediate_violations,
            correctness_score=0.0  # Will be calculated below
        )

        # Calculate weighted correctness score
        metrics.correctness_score = self._calculate_correctness_score(metrics)

        return metrics

    def _calculate_correctness_score(self, metrics: CorrectnessMetrics) -> float:
        """
        Calculate weighted overall correctness score.

        Weights:
        - Valid syntax: 10%
        - Count match: 20%
        - Type correctness: 30%
        - Constraint satisfaction: 40%

        Returns:
            Score between 0.0 and 1.0
        """
        score = 0.0

        # Valid syntax (10%)
        if metrics.is_valid_syntax:
            score += 0.10

        # Count match (20%)
        if metrics.count_match:
            score += 0.20

        # Type correctness (30%)
        score += 0.30 * metrics.type_correctness

        # Constraint satisfaction (40%)
        score += 0.40 * metrics.constraint_satisfaction_rate

        return round(score, 4)

    def _create_failed_metrics(self, reason: str) -> CorrectnessMetrics:
        """Create metrics for a failed case."""
        return CorrectnessMetrics(
            is_valid_syntax=False,
            constraint_satisfaction_rate=0.0,
            count_match=False,
            type_correctness=0.0,
            register_constraint_violations=0,
            immediate_constraint_violations=0,
            correctness_score=0.0
        )

    def evaluate_result(self, run_result: RunResult, test_case: TestCase) -> RunResult:
        """
        Evaluate a run result and add correctness metrics.

        This modifies the run_result in place by adding correctness metrics.

        Args:
            run_result: RunResult to evaluate
            test_case: TestCase with expected constraints

        Returns:
            The same run_result with correctness metrics added
        """
        correctness = self.calculate_correctness(run_result, test_case)
        run_result.correctness = correctness
        return run_result


def calculate_correctness_metrics(run_result: RunResult,
                                   test_case: TestCase) -> CorrectnessMetrics:
    """
    Convenience function to calculate correctness metrics.

    Args:
        run_result: RunResult from test execution
        test_case: TestCase with constraints

    Returns:
        CorrectnessMetrics
    """
    calculator = MetricsCalculator()
    return calculator.calculate_correctness(run_result, test_case)


def evaluate_run_result(run_result: RunResult, test_case: TestCase) -> RunResult:
    """
    Convenience function to evaluate and update a run result.

    Args:
        run_result: RunResult to evaluate
        test_case: TestCase with constraints

    Returns:
        Updated run_result with correctness metrics
    """
    calculator = MetricsCalculator()
    return calculator.evaluate_result(run_result, test_case)


# Example usage and testing
if __name__ == "__main__":
    from benchmark.test_suite.test_cases import get_case_by_id
    from benchmark.test_suite.schemas import (
        RunResult,
        EfficiencyMetrics,
        RobustnessMetrics,
        FailureMode
    )

    print("Testing MetricsCalculator...")

    # Test case
    test_case = get_case_by_id("TC-S01")
    print(f"\nTest Case: {test_case.id}")
    print(f"Description: {test_case.description}\n")

    # Simulate a good result
    good_assembly = "\n".join([
        f"{i}: addi x{i+1} x0 {i*10}"
        for i in range(10)
    ])

    good_result = RunResult(
        test_id=test_case.id,
        method="test",
        success=True,
        assembly=good_assembly,
        efficiency=EfficiencyMetrics(
            total_time=1.5,
            llm_time=1.0,
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

    # Calculate metrics
    calculator = MetricsCalculator()
    correctness = calculator.calculate_correctness(good_result, test_case)

    print("--- GOOD Result ---")
    print(f"Valid syntax: {correctness.is_valid_syntax}")
    print(f"Count match: {correctness.count_match}")
    print(f"Type correctness: {correctness.type_correctness:.2%}")
    print(f"Constraint satisfaction: {correctness.constraint_satisfaction_rate:.2%}")
    print(f"Register violations: {correctness.register_constraint_violations}")
    print(f"Immediate violations: {correctness.immediate_constraint_violations}")
    print(f"CORRECTNESS SCORE: {correctness.correctness_score:.4f}")

    # Simulate a bad result
    bad_assembly = """
0: addi x15 x0 10
1: sub x1 x2 x3
2: addi x20 x0 100
"""

    bad_result = RunResult(
        test_id=test_case.id,
        method="test",
        success=False,
        assembly=bad_assembly,
        efficiency=EfficiencyMetrics(
            total_time=0.5,
            llm_time=0.5,
            llm_call_count=1,
            total_prompt_tokens=100,
            total_completion_tokens=20
        ),
        robustness=RobustnessMetrics(
            is_success=False,
            failure_mode=FailureMode.INVALID_ASSEMBLY,
            timed_out=False,
            first_attempt_success=False
        )
    )

    correctness2 = calculator.calculate_correctness(bad_result, test_case)

    print("\n--- BAD Result ---")
    print(f"Valid syntax: {correctness2.is_valid_syntax}")
    print(f"Count match: {correctness2.count_match}")
    print(f"Type correctness: {correctness2.type_correctness:.2%}")
    print(f"Constraint satisfaction: {correctness2.constraint_satisfaction_rate:.2%}")
    print(f"Register violations: {correctness2.register_constraint_violations}")
    print(f"Immediate violations: {correctness2.immediate_constraint_violations}")
    print(f"CORRECTNESS SCORE: {correctness2.correctness_score:.4f}")

    # Test evaluate_result (modifies in place)
    print("\n--- Testing evaluate_result ---")
    test_result = RunResult(
        test_id=test_case.id,
        method="test",
        success=True,
        assembly=good_assembly
    )

    print(f"Before: correctness = {test_result.correctness}")
    calculator.evaluate_result(test_result, test_case)
    print(f"After: correctness score = {test_result.correctness.correctness_score:.4f}")
