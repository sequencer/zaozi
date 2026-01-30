"""
Phase 1 Verification Script

Tests:
1. Loading test cases
2. Data class serialization/deserialization
3. Configuration loading
"""

import sys
import os
import json

# Add project root to path
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

from benchmark.test_suite.test_cases import (
    get_all_test_cases,
    get_cases_by_difficulty,
    get_case_by_id,
    SIMPLE_CASES,
    MEDIUM_CASES,
    COMPLEX_CASES
)
from benchmark.test_suite.schemas import (
    TestCase,
    RunResult,
    CorrectnessMetrics,
    EfficiencyMetrics,
    RobustnessMetrics,
    BenchmarkConfig,
    Difficulty,
    FailureMode
)


def test_load_test_cases():
    """Test 1: Verify test cases can be loaded."""
    print("=" * 60)
    print("Test 1: Loading Test Cases")
    print("=" * 60)

    all_cases = get_all_test_cases()
    print(f"✓ Loaded {len(all_cases)} test cases")

    assert len(all_cases) == 15, f"Expected 15 test cases, got {len(all_cases)}"
    assert len(SIMPLE_CASES) == 5, f"Expected 5 simple cases, got {len(SIMPLE_CASES)}"
    assert len(MEDIUM_CASES) == 5, f"Expected 5 medium cases, got {len(MEDIUM_CASES)}"
    assert len(COMPLEX_CASES) == 5, f"Expected 5 complex cases, got {len(COMPLEX_CASES)}"

    print(f"✓ Simple cases: {len(SIMPLE_CASES)}")
    print(f"✓ Medium cases: {len(MEDIUM_CASES)}")
    print(f"✓ Complex cases: {len(COMPLEX_CASES)}")

    # Test get_case_by_id
    tc = get_case_by_id("TC-S01")
    assert tc.id == "TC-S01"
    print(f"✓ Retrieved test case by ID: {tc.id}")

    # Test get_cases_by_difficulty
    simple = get_cases_by_difficulty(Difficulty.SIMPLE)
    assert len(simple) == 5
    print(f"✓ Filtered {len(simple)} simple cases")

    print("\n")


def test_test_case_serialization():
    """Test 2: Verify TestCase serialization/deserialization."""
    print("=" * 60)
    print("Test 2: TestCase Serialization")
    print("=" * 60)

    tc = get_case_by_id("TC-S01")

    # Serialize to dict
    tc_dict = tc.to_dict()
    print(f"✓ Serialized TestCase to dict: {list(tc_dict.keys())}")

    # Verify key fields
    assert tc_dict["id"] == "TC-S01"
    assert tc_dict["difficulty"] == Difficulty.SIMPLE
    assert tc_dict["expected_count"] == 10
    print(f"✓ Verified key fields: id={tc_dict['id']}, count={tc_dict['expected_count']}")

    # Serialize to JSON
    tc_json = json.dumps(tc_dict, default=str)
    print(f"✓ Serialized to JSON ({len(tc_json)} chars)")

    # Deserialize from JSON
    tc_dict_loaded = json.loads(tc_json)
    print(f"✓ Deserialized from JSON")

    print("\n")


def test_run_result_serialization():
    """Test 3: Verify RunResult serialization/deserialization."""
    print("=" * 60)
    print("Test 3: RunResult Serialization")
    print("=" * 60)

    # Create sample metrics
    correctness = CorrectnessMetrics(
        is_valid_syntax=True,
        constraint_satisfaction_rate=0.95,
        count_match=True,
        type_correctness=0.98,
        register_constraint_violations=2,
        immediate_constraint_violations=1,
        correctness_score=0.96
    )

    efficiency = EfficiencyMetrics(
        total_time=2.34,
        llm_time=1.2,
        compilation_time=0.8,
        verification_time=0.3,
        llm_call_count=1,
        total_prompt_tokens=1500,
        total_completion_tokens=500,
        estimated_cost=0.0087,
        retry_count=0
    )

    robustness = RobustnessMetrics(
        is_success=True,
        failure_mode=FailureMode.NONE,
        timed_out=False,
        first_attempt_success=True
    )

    # Create RunResult
    result = RunResult(
        test_id="TC-S01",
        method="agent",
        success=True,
        assembly="0: addi x1 x0 10\n1: addi x2 x0 20",
        correctness=correctness,
        efficiency=efficiency,
        robustness=robustness,
        raw_output="Full output...",
        error_log="",
        metadata={"version": "1.0"}
    )

    # Serialize to dict
    result_dict = result.to_dict()
    print(f"✓ Serialized RunResult to dict")
    print(f"  Keys: {list(result_dict.keys())}")

    # Serialize to JSON
    result_json = json.dumps(result_dict)
    print(f"✓ Serialized to JSON ({len(result_json)} chars)")

    # Deserialize from JSON
    result_dict_loaded = json.loads(result_json)
    result_loaded = RunResult.from_dict(result_dict_loaded)
    print(f"✓ Deserialized from JSON")

    # Verify
    assert result_loaded.test_id == "TC-S01"
    assert result_loaded.success is True
    assert result_loaded.correctness.correctness_score == 0.96
    assert result_loaded.efficiency.total_time == 2.34
    assert result_loaded.robustness.is_success is True
    print(f"✓ Verified deserialized data matches original")

    print("\n")


def test_benchmark_config():
    """Test 4: Verify BenchmarkConfig serialization."""
    print("=" * 60)
    print("Test 4: BenchmarkConfig Serialization")
    print("=" * 60)

    config = BenchmarkConfig(
        llm_model="gpt-4o",
        llm_temperature=0.0,
        timeout_seconds=300,
        num_repetitions=3
    )

    # Serialize
    config_dict = config.to_dict()
    print(f"✓ Serialized BenchmarkConfig to dict")
    print(f"  Model: {config_dict['llm_model']}")
    print(f"  Temperature: {config_dict['llm_temperature']}")
    print(f"  Timeout: {config_dict['timeout_seconds']}s")

    # Serialize to JSON
    config_json = json.dumps(config_dict)
    print(f"✓ Serialized to JSON ({len(config_json)} chars)")

    # Deserialize
    config_dict_loaded = json.loads(config_json)
    config_loaded = BenchmarkConfig.from_dict(config_dict_loaded)
    print(f"✓ Deserialized from JSON")

    assert config_loaded.llm_model == "gpt-4o"
    assert config_loaded.llm_temperature == 0.0
    print(f"✓ Verified deserialized config matches original")

    print("\n")


def test_metrics_serialization():
    """Test 5: Verify individual metrics serialization."""
    print("=" * 60)
    print("Test 5: Individual Metrics Serialization")
    print("=" * 60)

    # CorrectnessMetrics
    correctness = CorrectnessMetrics(
        is_valid_syntax=True,
        constraint_satisfaction_rate=0.95,
        count_match=True,
        type_correctness=0.98,
        register_constraint_violations=2,
        immediate_constraint_violations=1,
        correctness_score=0.96
    )
    correctness_dict = correctness.to_dict()
    print(f"✓ CorrectnessMetrics: {list(correctness_dict.keys())}")

    # EfficiencyMetrics
    efficiency = EfficiencyMetrics(
        total_time=2.34,
        llm_time=1.2,
        llm_call_count=1,
        total_prompt_tokens=1500,
        total_completion_tokens=500
    )
    efficiency_dict = efficiency.to_dict()
    print(f"✓ EfficiencyMetrics: {list(efficiency_dict.keys())}")

    # RobustnessMetrics
    robustness = RobustnessMetrics(
        is_success=True,
        failure_mode=FailureMode.NONE,
        timed_out=False,
        first_attempt_success=True
    )
    robustness_dict = robustness.to_dict()
    print(f"✓ RobustnessMetrics: {list(robustness_dict.keys())}")

    print("\n")


def run_all_tests():
    """Run all Phase 1 verification tests."""
    print("\n" + "=" * 60)
    print("PHASE 1 VERIFICATION")
    print("=" * 60 + "\n")

    try:
        test_load_test_cases()
        test_test_case_serialization()
        test_run_result_serialization()
        test_benchmark_config()
        test_metrics_serialization()

        print("=" * 60)
        print("ALL TESTS PASSED ✓")
        print("=" * 60)
        print("\nPhase 1 implementation is verified and ready!")
        print("\nNext steps:")
        print("  - Phase 2: Implement AgentRunner and DirectLLMRunner")
        print("  - Phase 3: Implement evaluators (parser, checker, metrics)")
        print("\n")

        return True

    except AssertionError as e:
        print(f"\n❌ TEST FAILED: {e}")
        return False
    except Exception as e:
        print(f"\n❌ ERROR: {e}")
        import traceback
        traceback.print_exc()
        return False


if __name__ == "__main__":
    success = run_all_tests()
    sys.exit(0 if success else 1)
