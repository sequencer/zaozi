"""
Phase 2 Verification Script

Tests:
1. DirectLLMRunner can run independently (no_docs variant)
2. DirectLLMRunner can run independently (with_docs variant)
3. Runners return proper RunResult objects
4. Basic metrics are collected correctly
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

# Get model from environment or use default
LLM_MODEL = os.getenv("LLM_MODEL", "gpt-4o")


def test_direct_llm_runner_no_docs():
    """Test 1: DirectLLMRunner without documentation."""
    print("=" * 60)
    print("Test 1: DirectLLMRunner (no_docs variant)")
    print("=" * 60)

    config = BenchmarkConfig(
        llm_model=LLM_MODEL,
        llm_temperature=0.0,
        timeout_seconds=60
    )

    runner = DirectLLMRunner(config, include_docs=False)
    print(f"✓ Created runner: {runner}")

    # Use simplest test case
    test_case = get_case_by_id("TC-S01")
    print(f"✓ Loaded test case: {test_case.id}")
    print(f"  Description: {test_case.description}")

    # Run
    print("\nRunning test case...")
    result = runner.run(test_case)

    # Verify result structure
    assert result is not None, "Result should not be None"
    assert result.test_id == test_case.id, f"Test ID mismatch: {result.test_id}"
    assert result.method == "direct_llm_no_docs", f"Method mismatch: {result.method}"
    print(f"✓ Result structure correct")
    print(f"  Success: {result.success}")
    print(f"  Assembly lines: {len(result.assembly.split(chr(10))) if result.assembly else 0}")

    # Verify efficiency metrics
    assert result.efficiency is not None, "Efficiency metrics should not be None"
    assert result.efficiency.total_time > 0, "Total time should be positive"
    if result.success:
        assert result.efficiency.llm_time > 0, "LLM time should be positive when successful"
        assert result.efficiency.total_prompt_tokens > 0, "Should have prompt tokens when successful"
    assert result.efficiency.llm_call_count == 1, "Should have 1 LLM call"
    print(f"✓ Efficiency metrics present")
    print(f"  Total time: {result.efficiency.total_time:.2f}s")
    print(f"  LLM time: {result.efficiency.llm_time:.2f}s")
    print(f"  Tokens: {result.efficiency.total_prompt_tokens} + {result.efficiency.total_completion_tokens}")

    # Verify robustness metrics
    assert result.robustness is not None, "Robustness metrics should not be None"
    print(f"✓ Robustness metrics present")
    print(f"  Success: {result.robustness.is_success}")
    print(f"  Failure mode: {result.robustness.failure_mode.value}")

    print("\n")
    return result


def test_direct_llm_runner_with_docs():
    """Test 2: DirectLLMRunner with documentation."""
    print("=" * 60)
    print("Test 2: DirectLLMRunner (with_docs variant)")
    print("=" * 60)

    config = BenchmarkConfig(
        llm_model=LLM_MODEL,
        llm_temperature=0.0,
        timeout_seconds=60
    )

    runner = DirectLLMRunner(config, include_docs=True)
    print(f"✓ Created runner: {runner}")

    # Use simplest test case
    test_case = get_case_by_id("TC-S01")
    print(f"✓ Loaded test case: {test_case.id}")

    # Run
    print("\nRunning test case...")
    result = runner.run(test_case)

    # Verify
    assert result is not None, "Result should not be None"
    assert result.method == "direct_llm_with_docs", f"Method mismatch: {result.method}"
    print(f"✓ Result structure correct")
    print(f"  Success: {result.success}")
    print(f"  Assembly lines: {len(result.assembly.split(chr(10))) if result.assembly else 0}")

    # Compare token usage (with_docs should have more prompt tokens)
    print(f"✓ Metrics collected")
    print(f"  Prompt tokens: {result.efficiency.total_prompt_tokens}")
    print(f"  Completion tokens: {result.efficiency.total_completion_tokens}")
    print(f"  Cost: ${result.efficiency.estimated_cost:.6f}")

    print("\n")
    return result


def test_result_serialization():
    """Test 3: Verify RunResult can be serialized."""
    print("=" * 60)
    print("Test 3: RunResult Serialization")
    print("=" * 60)

    config = BenchmarkConfig(llm_model=LLM_MODEL, llm_temperature=0.0)
    runner = DirectLLMRunner(config, include_docs=False)
    test_case = get_case_by_id("TC-S01")

    result = runner.run(test_case)

    # Serialize to dict
    result_dict = result.to_dict()
    print(f"✓ Serialized to dict")
    print(f"  Keys: {list(result_dict.keys())}")

    # Verify key fields present
    assert "test_id" in result_dict
    assert "method" in result_dict
    assert "success" in result_dict
    assert "efficiency" in result_dict
    print(f"✓ All key fields present")

    # Serialize to JSON
    import json
    result_json = json.dumps(result_dict)
    print(f"✓ Serialized to JSON ({len(result_json)} chars)")

    # Deserialize
    result_dict_loaded = json.loads(result_json)
    from benchmark.test_suite.schemas import RunResult
    result_loaded = RunResult.from_dict(result_dict_loaded)
    print(f"✓ Deserialized from JSON")

    assert result_loaded.test_id == result.test_id
    assert result_loaded.method == result.method
    print(f"✓ Deserialized data matches original")

    print("\n")


def compare_variants():
    """Test 4: Compare no_docs vs with_docs variants."""
    print("=" * 60)
    print("Test 4: Compare Variants")
    print("=" * 60)

    config = BenchmarkConfig(llm_model=LLM_MODEL, llm_temperature=0.0)
    test_case = get_case_by_id("TC-S01")

    # Run both variants
    runner_no_docs = DirectLLMRunner(config, include_docs=False)
    result_no_docs = runner_no_docs.run(test_case)

    runner_with_docs = DirectLLMRunner(config, include_docs=True)
    result_with_docs = runner_with_docs.run(test_case)

    print("\nComparison:")
    print(f"  no_docs:")
    print(f"    Success: {result_no_docs.success}")
    print(f"    Time: {result_no_docs.efficiency.total_time:.2f}s")
    print(f"    Prompt tokens: {result_no_docs.efficiency.total_prompt_tokens}")
    print(f"    Cost: ${result_no_docs.efficiency.estimated_cost:.6f}")

    print(f"\n  with_docs:")
    print(f"    Success: {result_with_docs.success}")
    print(f"    Time: {result_with_docs.efficiency.total_time:.2f}s")
    print(f"    Prompt tokens: {result_with_docs.efficiency.total_prompt_tokens}")
    print(f"    Cost: ${result_with_docs.efficiency.estimated_cost:.6f}")

    # with_docs should have more prompt tokens (includes documentation)
    if result_with_docs.efficiency.total_prompt_tokens > result_no_docs.efficiency.total_prompt_tokens:
        print(f"\n✓ with_docs has more prompt tokens (as expected)")
    else:
        print(f"\n⚠️  with_docs doesn't have more prompt tokens (unexpected but not critical)")

    print("\n")


def run_all_tests():
    """Run all Phase 2 verification tests."""
    print("\n" + "=" * 60)
    print("PHASE 2 VERIFICATION")
    print("=" * 60 + "\n")

    try:
        # Note: We skip AgentRunner test as it requires Mill compilation
        # which may not be set up in all environments
        test_direct_llm_runner_no_docs()
        test_direct_llm_runner_with_docs()
        test_result_serialization()
        compare_variants()

        print("=" * 60)
        print("ALL TESTS PASSED ✓")
        print("=" * 60)
        print("\nPhase 2 implementation is verified and ready!")
        print("\nNext steps:")
        print("  - Phase 3: Implement evaluators (assembly parser, constraint checker)")
        print("  - Phase 4: Implement benchmark orchestrator")
        print("\nNote: AgentRunner test skipped (requires Mill setup)")
        print("      Run manually with: python -m benchmark.runners.agent_runner")
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
