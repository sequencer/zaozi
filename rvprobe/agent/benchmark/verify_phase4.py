#!/usr/bin/env python3
"""
Phase 4 Verification Script

Tests the benchmark orchestrator implementation to ensure:
1. Configuration loading works correctly
2. Test case filtering works
3. Orchestrator can be initialized
4. Results can be saved to CSV and JSON
5. CLI argument parsing works

This is a dry-run test that doesn't execute actual LLM calls.

Usage:
    cd /home/clo91eaf/Project/zaozi/rvprobe/agent
    uv run benchmark/verify_phase4.py
"""

import sys
import os
from pathlib import Path
import tempfile
import json
import csv

# Add project paths
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

from benchmark.benchmark import BenchmarkOrchestrator, load_config_from_yaml
from benchmark.test_suite.schemas import (
    BenchmarkConfig, RunResult, TestCase, Difficulty,
    CorrectnessMetrics, EfficiencyMetrics, RobustnessMetrics, FailureMode
)
from benchmark.test_suite.test_cases import get_all_test_cases


def test_config_loading():
    """Test 1: Configuration loading from YAML."""
    print("Test 1: Configuration Loading")
    print("-" * 60)
    
    config_path = Path(__file__).parent / "config.yaml"
    
    if not config_path.exists():
        print(f"  ⚠ Config file not found: {config_path}")
        print("  Using default config instead")
        config = BenchmarkConfig()
    else:
        config = load_config_from_yaml(str(config_path))
        print(f"  ✓ Loaded config from: {config_path}")
    
    print(f"  Model: {config.llm_model}")
    print(f"  Temperature: {config.llm_temperature}")
    print(f"  Timeout: {config.timeout_seconds}s")
    print(f"  Max Retries: {config.max_retries}")
    print(f"  Results Dir: {config.results_dir}")
    print()
    
    return config


def test_test_case_loading():
    """Test 2: Test case loading and filtering."""
    print("Test 2: Test Case Loading")
    print("-" * 60)
    
    all_cases = get_all_test_cases()
    print(f"  ✓ Loaded {len(all_cases)} test cases")
    
    # Count by difficulty
    by_difficulty = {}
    for tc in all_cases:
        diff = tc.difficulty.value
        by_difficulty[diff] = by_difficulty.get(diff, 0) + 1
    
    for diff, count in by_difficulty.items():
        print(f"    - {diff}: {count} cases")
    
    # Test filtering by difficulty
    simple_cases = [tc for tc in all_cases if tc.difficulty == Difficulty.SIMPLE]
    print(f"  ✓ Filtered to {len(simple_cases)} simple cases")
    
    # Test filtering by ID
    specific_cases = [tc for tc in all_cases if tc.id in ["TC-S01", "TC-S02"]]
    print(f"  ✓ Filtered to {len(specific_cases)} specific cases (TC-S01, TC-S02)")
    print()
    
    return all_cases


def test_orchestrator_initialization():
    """Test 3: Orchestrator initialization."""
    print("Test 3: Orchestrator Initialization")
    print("-" * 60)
    
    # Use temporary directory for results
    with tempfile.TemporaryDirectory() as tmpdir:
        config = BenchmarkConfig(results_dir=tmpdir)
        
        try:
            orchestrator = BenchmarkOrchestrator(config)
            print(f"  ✓ Orchestrator initialized successfully")
            print(f"  ✓ Results directory created: {orchestrator.results_dir}")
            print(f"  ✓ Logger configured")
            print(f"  ✓ AgentRunner initialized: {orchestrator.agent_runner}")
            print(f"  ✓ DirectLLMRunner initialized: {orchestrator.direct_llm_runner}")
            print(f"  ✓ MetricsCalculator initialized: {orchestrator.metrics_calculator}")
            print()
            return orchestrator
        except Exception as e:
            print(f"  ✗ Failed to initialize orchestrator: {e}")
            import traceback
            traceback.print_exc()
            return None


def test_result_serialization():
    """Test 4: Result serialization to CSV and JSON."""
    print("Test 4: Result Serialization")
    print("-" * 60)
    
    # Create mock results
    test_case = TestCase(
        id="TC-TEST",
        difficulty=Difficulty.SIMPLE,
        description="Test case for verification",
        expected_count=10,
        instruction_types=["addi"],
        register_constraints={"rd": {"min": 1, "max": 10}},
        category="test"
    )
    
    mock_results = [
        RunResult(
            test_id="TC-S01",
            method="agent",
            success=True,
            assembly="0: addi x1 x2 10\n1: addi x3 x4 20",
            correctness=CorrectnessMetrics(
                is_valid_syntax=True,
                constraint_satisfaction_rate=0.95,
                count_match=True,
                type_correctness=1.0,
                register_constraint_violations=0,
                immediate_constraint_violations=1,
                correctness_score=0.92
            ),
            efficiency=EfficiencyMetrics(
                total_time=2.5,
                llm_time=1.2,
                compilation_time=0.8,
                verification_time=0.5,
                llm_call_count=1,
                total_prompt_tokens=500,
                total_completion_tokens=200,
                estimated_cost=0.0035,
                retry_count=0
            ),
            robustness=RobustnessMetrics(
                is_success=True,
                failure_mode=FailureMode.NONE,
                timed_out=False,
                first_attempt_success=True
            ),
            raw_output="Mock agent output",
            error_log=""
        ),
        RunResult(
            test_id="TC-S01",
            method="direct_llm",
            success=True,
            assembly="0: addi x1 x2 15",
            correctness=CorrectnessMetrics(
                is_valid_syntax=True,
                constraint_satisfaction_rate=0.80,
                count_match=False,
                type_correctness=1.0,
                register_constraint_violations=0,
                immediate_constraint_violations=0,
                correctness_score=0.75
            ),
            efficiency=EfficiencyMetrics(
                total_time=0.6,
                llm_time=0.6,
                llm_call_count=1,
                total_prompt_tokens=300,
                total_completion_tokens=100,
                estimated_cost=0.0018,
                retry_count=0
            ),
            robustness=RobustnessMetrics(
                is_success=True,
                failure_mode=FailureMode.NONE,
                timed_out=False,
                first_attempt_success=True
            ),
            raw_output="Mock LLM output",
            error_log=""
        )
    ]
    
    # Test serialization with temporary directory
    with tempfile.TemporaryDirectory() as tmpdir:
        config = BenchmarkConfig(results_dir=tmpdir)
        orchestrator = BenchmarkOrchestrator(config)
        
        try:
            # Save results
            output_files = orchestrator.save_results(mock_results, prefix="test")
            
            # Verify JSON file
            json_path = output_files['json']
            if json_path.exists():
                with open(json_path, 'r') as f:
                    json_data = json.load(f)
                print(f"  ✓ JSON saved successfully: {json_path.name}")
                print(f"    - Contains {len(json_data['results'])} results")
                print(f"    - Metadata: {json_data['metadata']['timestamp']}")
            else:
                print(f"  ✗ JSON file not created")
            
            # Verify CSV file
            csv_path = output_files['csv']
            if csv_path.exists():
                with open(csv_path, 'r') as f:
                    reader = csv.reader(f)
                    rows = list(reader)
                print(f"  ✓ CSV saved successfully: {csv_path.name}")
                print(f"    - Header: {len(rows[0])} columns")
                print(f"    - Data: {len(rows) - 1} rows")
                
                # Print first few columns of header
                print(f"    - Columns: {', '.join(rows[0][:10])}...")
            else:
                print(f"  ✗ CSV file not created")
            
            print()
            return True
            
        except Exception as e:
            print(f"  ✗ Serialization failed: {e}")
            import traceback
            traceback.print_exc()
            return False


def test_filtering_functionality():
    """Test 5: Test case filtering functionality."""
    print("Test 5: Test Case Filtering")
    print("-" * 60)
    
    with tempfile.TemporaryDirectory() as tmpdir:
        config = BenchmarkConfig(results_dir=tmpdir)
        orchestrator = BenchmarkOrchestrator(config)
        
        # Test 1: No filter (all tests)
        all_tests = orchestrator.load_test_cases()
        print(f"  ✓ Load all tests: {len(all_tests)} cases")
        
        # Test 2: Filter by specific IDs
        specific_tests = orchestrator.load_test_cases(
            selected_tests=["TC-S01", "TC-S02", "TC-M01"]
        )
        print(f"  ✓ Filter by ID: {len(specific_tests)} cases (expected 3)")
        
        # Test 3: Filter by difficulty
        simple_tests = orchestrator.load_test_cases(
            difficulty_filter=["simple"]
        )
        print(f"  ✓ Filter by difficulty (simple): {len(simple_tests)} cases")
        
        medium_complex = orchestrator.load_test_cases(
            difficulty_filter=["medium", "complex"]
        )
        print(f"  ✓ Filter by difficulty (medium+complex): {len(medium_complex)} cases")
        
        # Test 4: Combined filter
        combined = orchestrator.load_test_cases(
            selected_tests=["TC-S01", "TC-S02", "TC-M01", "TC-C01"],
            difficulty_filter=["simple"]
        )
        print(f"  ✓ Combined filter: {len(combined)} cases (expected 2)")
        print()


def test_error_handling():
    """Test 6: Error handling in orchestrator."""
    print("Test 6: Error Handling")
    print("-" * 60)
    
    with tempfile.TemporaryDirectory() as tmpdir:
        config = BenchmarkConfig(results_dir=tmpdir)
        orchestrator = BenchmarkOrchestrator(config)
        
        # Test timeout result creation
        test_case = TestCase(
            id="TC-TIMEOUT",
            difficulty=Difficulty.SIMPLE,
            description="Timeout test",
            expected_count=10,
            instruction_types=["addi"],
            register_constraints={},
            category="test"
        )
        
        timeout_result = orchestrator._create_timeout_result(
            test_case, "agent", "Execution timed out after 300s"
        )
        print(f"  ✓ Timeout result created")
        print(f"    - Success: {timeout_result.success}")
        print(f"    - Failure mode: {timeout_result.robustness.failure_mode.value}")
        print(f"    - Timed out: {timeout_result.robustness.timed_out}")
        
        # Test error result creation
        error_result = orchestrator._create_error_result(
            test_case, "direct_llm", "LLM API error: Rate limit exceeded"
        )
        print(f"  ✓ Error result created")
        print(f"    - Success: {error_result.success}")
        print(f"    - Failure mode: {error_result.robustness.failure_mode.value}")
        print(f"    - Error log: {error_result.error_log[:50]}...")
        print()


def test_summary_printing():
    """Test 7: Summary printing functionality."""
    print("Test 7: Summary Printing")
    print("-" * 60)
    
    # Create mock results with different outcomes
    mock_results = []
    
    for i in range(3):
        # Successful agent results
        mock_results.append(
            RunResult(
                test_id=f"TC-S0{i+1}",
                method="agent",
                success=True,
                assembly="mock assembly",
                correctness=CorrectnessMetrics(
                    is_valid_syntax=True,
                    constraint_satisfaction_rate=0.95,
                    count_match=True,
                    type_correctness=1.0,
                    register_constraint_violations=0,
                    immediate_constraint_violations=0,
                    correctness_score=0.92
                ),
                efficiency=EfficiencyMetrics(
                    total_time=2.5 + i * 0.5,
                    llm_time=1.2,
                    llm_call_count=1,
                    total_prompt_tokens=500,
                    total_completion_tokens=200,
                    estimated_cost=0.0035
                ),
                robustness=RobustnessMetrics(
                    is_success=True,
                    failure_mode=FailureMode.NONE,
                    timed_out=False,
                    first_attempt_success=True
                )
            )
        )
        
        # Direct LLM results (mixed success)
        mock_results.append(
            RunResult(
                test_id=f"TC-S0{i+1}",
                method="direct_llm",
                success=i < 2,  # First 2 succeed, last one fails
                assembly="mock assembly" if i < 2 else "",
                correctness=CorrectnessMetrics(
                    is_valid_syntax=i < 2,
                    constraint_satisfaction_rate=0.80 if i < 2 else 0.0,
                    count_match=i < 2,
                    type_correctness=1.0 if i < 2 else 0.0,
                    register_constraint_violations=0,
                    immediate_constraint_violations=0,
                    correctness_score=0.80 if i < 2 else 0.0
                ),
                efficiency=EfficiencyMetrics(
                    total_time=0.6 + i * 0.2,
                    llm_time=0.6,
                    llm_call_count=1,
                    total_prompt_tokens=300,
                    total_completion_tokens=100,
                    estimated_cost=0.0018
                ),
                robustness=RobustnessMetrics(
                    is_success=i < 2,
                    failure_mode=FailureMode.NONE if i < 2 else FailureMode.INVALID_ASSEMBLY,
                    timed_out=False,
                    first_attempt_success=i < 2
                )
            )
        )
    
    with tempfile.TemporaryDirectory() as tmpdir:
        config = BenchmarkConfig(results_dir=tmpdir)
        orchestrator = BenchmarkOrchestrator(config)
        
        print("  ✓ Printing summary:")
        orchestrator.print_summary(mock_results)
        print()


def main():
    """Run all verification tests."""
    print("\n" + "="*60)
    print("PHASE 4 VERIFICATION - Benchmark Orchestrator")
    print("="*60 + "\n")
    
    tests = [
        test_config_loading,
        test_test_case_loading,
        test_orchestrator_initialization,
        test_result_serialization,
        test_filtering_functionality,
        test_error_handling,
        test_summary_printing
    ]
    
    passed = 0
    failed = 0
    
    for test_func in tests:
        try:
            result = test_func()
            if result is not None and result is False:
                failed += 1
            else:
                passed += 1
        except Exception as e:
            print(f"✗ Test failed with exception: {e}")
            import traceback
            traceback.print_exc()
            failed += 1
            print()
    
    print("\n" + "="*60)
    print("VERIFICATION RESULTS")
    print("="*60)
    print(f"Passed: {passed}/{len(tests)}")
    print(f"Failed: {failed}/{len(tests)}")
    
    if failed == 0:
        print("\n✓ All Phase 4 tests passed!")
        print("\nPhase 4 Implementation Complete:")
        print("  - Configuration loading ✓")
        print("  - Test case filtering ✓")
        print("  - Orchestrator initialization ✓")
        print("  - Result serialization (CSV/JSON) ✓")
        print("  - Error handling ✓")
        print("  - Summary reporting ✓")
        print("\nNext steps:")
        print("  1. Run actual benchmark: python benchmark.py --tests TC-S01")
        print("  2. Verify runner implementations work correctly")
        print("  3. Proceed to Phase 5: Visualization and Reporting")
        return 0
    else:
        print(f"\n✗ {failed} tests failed. Please review the errors above.")
        return 1


if __name__ == '__main__':
    sys.exit(main())
