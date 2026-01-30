"""
Constraint Checker for RISC-V instructions.

Verifies that generated instructions satisfy specified constraints.
"""

import sys
import os
from typing import List, Dict, Optional, Tuple
from collections import Counter

# Add project paths
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '../..')))

from benchmark.evaluators.assembly_parser import ParsedInstruction, AssemblyParser
from benchmark.test_suite.schemas import TestCase


class ConstraintCheckResult:
    """Results of constraint checking."""

    def __init__(self):
        self.count_match: bool = True
        self.expected_count: int = 0
        self.actual_count: int = 0

        self.type_correctness: float = 1.0  # Proportion of correct instruction types
        self.type_violations: int = 0

        self.register_violations: int = 0
        self.immediate_violations: int = 0

        self.constraint_satisfaction_rate: float = 1.0  # Overall satisfaction rate
        self.total_constraints_checked: int = 0
        self.constraints_satisfied: int = 0

        self.details: List[str] = []  # Detailed violation messages

    def add_violation(self, message: str):
        """Add a violation detail message."""
        self.details.append(message)

    def to_dict(self) -> Dict:
        """Convert to dictionary."""
        return {
            "count_match": self.count_match,
            "expected_count": self.expected_count,
            "actual_count": self.actual_count,
            "type_correctness": self.type_correctness,
            "type_violations": self.type_violations,
            "register_violations": self.register_violations,
            "immediate_violations": self.immediate_violations,
            "constraint_satisfaction_rate": self.constraint_satisfaction_rate,
            "total_constraints_checked": self.total_constraints_checked,
            "constraints_satisfied": self.constraints_satisfied,
            "violation_count": len(self.details),
            "details": self.details[:10]  # Limit to first 10 for brevity
        }


class ConstraintChecker:
    """
    Checks whether generated instructions satisfy test case constraints.
    """

    def __init__(self):
        self.parser = AssemblyParser()

    def check(self, assembly_text: str, test_case: TestCase) -> ConstraintCheckResult:
        """
        Check constraints for generated assembly.

        Args:
            assembly_text: Generated assembly instructions
            test_case: Test case with expected constraints

        Returns:
            ConstraintCheckResult with validation results
        """
        result = ConstraintCheckResult()

        # Parse assembly
        instructions = self.parser.parse(assembly_text)
        result.actual_count = len(instructions)
        result.expected_count = test_case.expected_count

        if len(instructions) == 0:
            result.count_match = False
            result.constraint_satisfaction_rate = 0.0
            result.add_violation("No instructions parsed")
            return result

        # Check instruction count
        result.count_match = self._check_count(instructions, test_case, result)

        # Check instruction types
        self._check_types(instructions, test_case, result)

        # Check register constraints
        self._check_register_constraints(instructions, test_case, result)

        # Check immediate constraints
        self._check_immediate_constraints(instructions, test_case, result)

        # Calculate overall satisfaction rate
        if result.total_constraints_checked > 0:
            result.constraint_satisfaction_rate = (
                result.constraints_satisfied / result.total_constraints_checked
            )
        else:
            result.constraint_satisfaction_rate = 1.0

        return result

    def _check_count(self, instructions: List[ParsedInstruction],
                     test_case: TestCase, result: ConstraintCheckResult) -> bool:
        """Check if instruction count matches expected."""
        expected = test_case.expected_count
        actual = len(instructions)

        result.total_constraints_checked += 1

        # Allow some tolerance for "approximately" cases (like TC-C04)
        # If description contains "approximately" or "~", allow ±5% tolerance
        tolerance = 0
        desc_lower = test_case.description.lower()
        if "approximately" in desc_lower or "~" in desc_lower or "about" in desc_lower:
            tolerance = int(expected * 0.05)  # 5% tolerance

        if abs(actual - expected) <= tolerance:
            result.constraints_satisfied += 1
            return True
        else:
            result.add_violation(
                f"Count mismatch: expected {expected}, got {actual}"
            )
            return False

    def _check_types(self, instructions: List[ParsedInstruction],
                     test_case: TestCase, result: ConstraintCheckResult):
        """Check if instruction types are correct."""
        expected_types = set(t.lower() for t in test_case.instruction_types)
        actual_mnemonics = [instr.mnemonic.lower() for instr in instructions]

        # Count correct types
        correct_count = sum(1 for m in actual_mnemonics if m in expected_types)
        total_count = len(actual_mnemonics)

        if total_count > 0:
            result.type_correctness = correct_count / total_count
            result.type_violations = total_count - correct_count
            result.total_constraints_checked += total_count
            result.constraints_satisfied += correct_count

            # Add details for incorrect types
            if result.type_violations > 0:
                wrong_types = [m for m in actual_mnemonics if m not in expected_types]
                type_counter = Counter(wrong_types)
                for mnemonic, count in type_counter.most_common(5):
                    result.add_violation(
                        f"Unexpected instruction type '{mnemonic}' (x{count})"
                    )

    def _check_register_constraints(self, instructions: List[ParsedInstruction],
                                     test_case: TestCase, result: ConstraintCheckResult):
        """Check register range constraints."""
        if not test_case.register_constraints:
            return

        for instr in instructions:
            for reg_name, constraint in test_case.register_constraints.items():
                min_val = constraint.get("min", 0)
                max_val = constraint.get("max", 32)

                reg_value = None
                if reg_name == "rd":
                    reg_value = instr.rd
                elif reg_name == "rs1":
                    reg_value = instr.rs1
                elif reg_name == "rs2":
                    reg_value = instr.rs2

                if reg_value is not None:
                    result.total_constraints_checked += 1
                    if min_val <= reg_value < max_val:
                        result.constraints_satisfied += 1
                    else:
                        result.register_violations += 1
                        result.add_violation(
                            f"Instr {instr.index}: {reg_name}=x{reg_value} "
                            f"outside range [{min_val}, {max_val})"
                        )

    def _check_immediate_constraints(self, instructions: List[ParsedInstruction],
                                      test_case: TestCase, result: ConstraintCheckResult):
        """Check immediate value constraints."""
        if not test_case.immediate_constraints:
            return

        min_val = test_case.immediate_constraints.get("min")
        max_val = test_case.immediate_constraints.get("max")

        if min_val is None and max_val is None:
            return

        for instr in instructions:
            if instr.imm is not None:
                result.total_constraints_checked += 1

                # Check bounds
                in_range = True
                if min_val is not None and instr.imm < min_val:
                    in_range = False
                if max_val is not None and instr.imm >= max_val:
                    in_range = False

                if in_range:
                    result.constraints_satisfied += 1
                else:
                    result.immediate_violations += 1
                    result.add_violation(
                        f"Instr {instr.index}: imm={instr.imm} "
                        f"outside range [{min_val}, {max_val})"
                    )


def check_constraints(assembly_text: str, test_case: TestCase) -> ConstraintCheckResult:
    """
    Convenience function to check constraints.

    Args:
        assembly_text: Generated assembly
        test_case: Test case with constraints

    Returns:
        ConstraintCheckResult
    """
    checker = ConstraintChecker()
    return checker.check(assembly_text, test_case)


# Example usage and testing
if __name__ == "__main__":
    from benchmark.test_suite.test_cases import get_case_by_id

    print("Testing ConstraintChecker...")

    # Test case TC-S01: 10 ADDI, rd in range 1-10
    test_case = get_case_by_id("TC-S01")
    print(f"\nTest Case: {test_case.id}")
    print(f"Description: {test_case.description}")
    print(f"Expected: {test_case.expected_count} x {test_case.instruction_types}")

    # Good assembly (should pass all constraints)
    good_assembly = "\n".join([
        f"{i}: addi x{i+1} x0 {i*10}"
        for i in range(10)
    ])

    print("\n--- Testing GOOD assembly ---")
    checker = ConstraintChecker()
    result = checker.check(good_assembly, test_case)

    print(f"Count match: {result.count_match} ({result.actual_count}/{result.expected_count})")
    print(f"Type correctness: {result.type_correctness:.2%}")
    print(f"Register violations: {result.register_violations}")
    print(f"Immediate violations: {result.immediate_violations}")
    print(f"Overall satisfaction: {result.constraint_satisfaction_rate:.2%}")
    print(f"Violations: {len(result.details)}")

    # Bad assembly (should have violations)
    bad_assembly = """
0: addi x15 x0 10
1: sub x1 x2 x3
2: addi x20 x0 100
"""

    print("\n--- Testing BAD assembly ---")
    result2 = checker.check(bad_assembly, test_case)

    print(f"Count match: {result2.count_match} ({result2.actual_count}/{result2.expected_count})")
    print(f"Type correctness: {result2.type_correctness:.2%}")
    print(f"Register violations: {result2.register_violations}")
    print(f"Immediate violations: {result2.immediate_violations}")
    print(f"Overall satisfaction: {result2.constraint_satisfaction_rate:.2%}")
    print(f"\nViolation details:")
    for detail in result2.details:
        print(f"  - {detail}")
