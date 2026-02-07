#!/usr/bin/env python3
"""
Benchmark Orchestrator - Phase 4 Implementation

Main entry point for running the RVProbe Agent benchmark.
Orchestrates test execution across multiple methods and collects comprehensive results.

Usage:
    python benchmark.py                    # Run all tests with default config
    python benchmark.py --config custom.yaml  # Use custom configuration
    python benchmark.py --tests TC-S01 TC-S02  # Run specific tests
    python benchmark.py --difficulty simple    # Run only simple tests
"""

import sys
import os
import argparse
import logging
import time
import json
import csv
from pathlib import Path
from typing import List, Dict, Any, Optional
from datetime import datetime
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import asdict

# Add project paths
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

# Load .env file early so os.getenv picks up LLM_MODEL, LLM_API_KEY, etc.
try:
    from dotenv import load_dotenv
    load_dotenv()
except ImportError:
    pass

# Import from benchmark modules
from benchmark.test_suite.schemas import (
    TestCase, RunResult, BenchmarkConfig, 
    Difficulty, CorrectnessMetrics, EfficiencyMetrics, RobustnessMetrics
)
from benchmark.test_suite.test_cases import get_all_test_cases
from benchmark.runners.agent_runner import AgentRunner
from benchmark.runners.direct_llm_runner import DirectLLMRunner
from benchmark.evaluators.metrics import MetricsCalculator
from benchmark.utils.timing import Timer

# Try to import yaml, provide fallback
try:
    import yaml
except ImportError:
    print("Warning: PyYAML not installed. Using default configuration.")
    yaml = None

# Try to import visualization modules
try:
    from benchmark.visualization.visualizer import BenchmarkVisualizer
    from benchmark.visualization.report_generator import ReportGenerator
    VISUALIZATION_AVAILABLE = True
except ImportError as e:
    print(f"⚠️ Warning: Visualization modules not available: {e}")
    print("   Install matplotlib and numpy for visualization: uv pip install matplotlib numpy")
    VISUALIZATION_AVAILABLE = False


class BenchmarkOrchestrator:
    """
    Main orchestrator for benchmark execution.
    
    Responsibilities:
    - Load configuration and test cases
    - Initialize runners (AgentRunner, DirectLLMRunner)
    - Execute tests sequentially or in parallel
    - Collect and aggregate results
    - Save results to CSV and JSON formats
    - Provide progress reporting
    """
    
    def __init__(self, config: BenchmarkConfig):
        """
        Initialize the orchestrator.
        
        Args:
            config: Benchmark configuration
        """
        self.config = config
        self.results: List[RunResult] = []
        self.logger = self._setup_logging()
        self.metrics_calculator = MetricsCalculator()
        
        # Create results directory
        self.results_dir = Path(config.results_dir)
        self.results_dir.mkdir(parents=True, exist_ok=True)
        
        # Initialize runners
        self.logger.info("Initializing runners...")
        self.agent_runner = AgentRunner(config)
        self.direct_llm_runner = DirectLLMRunner(config)
        
        self.logger.info(f"Orchestrator initialized with config: {config.llm_model}")
    
    def _setup_logging(self) -> logging.Logger:
        """
        Set up logging configuration.
        
        Returns:
            Configured logger instance
        """
        # Create logger
        logger = logging.getLogger("BenchmarkOrchestrator")
        logger.setLevel(getattr(logging, self.config.to_dict().get('log_level', 'INFO')))
        
        # Console handler
        console_handler = logging.StreamHandler(sys.stdout)
        console_handler.setLevel(logging.INFO)
        console_formatter = logging.Formatter(
            '%(asctime)s - %(name)s - %(levelname)s - %(message)s',
            datefmt='%Y-%m-%d %H:%M:%S'
        )
        console_handler.setFormatter(console_formatter)
        logger.addHandler(console_handler)
        
        # File handler
        log_file = self.config.to_dict().get('log_file', './benchmark_results/benchmark.log')
        log_path = Path(log_file)
        log_path.parent.mkdir(parents=True, exist_ok=True)
        
        file_handler = logging.FileHandler(log_file, mode='w')
        file_handler.setLevel(logging.DEBUG)
        file_formatter = logging.Formatter(
            '%(asctime)s - %(name)s - %(levelname)s - %(message)s'
        )
        file_handler.setFormatter(file_formatter)
        logger.addHandler(file_handler)
        
        return logger
    
    def load_test_cases(self, 
                        selected_tests: Optional[List[str]] = None,
                        difficulty_filter: Optional[List[str]] = None) -> List[TestCase]:
        """
        Load test cases with optional filtering.
        
        Args:
            selected_tests: List of test IDs to run (None = all)
            difficulty_filter: List of difficulty levels to include (None = all)
        
        Returns:
            List of TestCase objects to execute
        """
        all_cases = get_all_test_cases()
        
        # Filter by specific test IDs
        if selected_tests:
            all_cases = [tc for tc in all_cases if tc.id in selected_tests]
            self.logger.info(f"Filtered to {len(all_cases)} tests by ID: {selected_tests}")
        
        # Filter by difficulty
        if difficulty_filter:
            difficulty_set = set(d.lower() for d in difficulty_filter)
            all_cases = [tc for tc in all_cases if tc.difficulty.value.lower() in difficulty_set]
            self.logger.info(f"Filtered to {len(all_cases)} tests by difficulty: {difficulty_filter}")
        
        self.logger.info(f"Loaded {len(all_cases)} test cases")
        return all_cases
    
    def run_single_test(self, test_case: TestCase, method: str, repetition: int = 0) -> RunResult:
        """
        Run a single test case with a specific method.
        
        Args:
            test_case: Test case to execute
            method: Method identifier ("agent" or "direct_llm")
            repetition: Repetition number (for statistical validity)
        
        Returns:
            RunResult containing execution results and metrics
        """
        self.logger.info(
            f"Running {test_case.id} with {method} "
            f"(rep {repetition + 1}/{self.config.num_repetitions})"
        )
        
        start_time = time.time()
        
        try:
            # Select appropriate runner
            if method == "agent":
                runner = self.agent_runner
            elif method.startswith("direct_llm"):
                runner = self.direct_llm_runner
            else:
                raise ValueError(f"Unknown method: {method}")
            
            # Execute the test
            with Timer() as timer:
                run_result = runner.run(test_case)
            
            # Calculate correctness metrics
            correctness = self.metrics_calculator.calculate_correctness(
                run_result, test_case
            )
            run_result.correctness = correctness
            
            # Update efficiency metrics with total time
            if run_result.efficiency:
                run_result.efficiency.total_time = timer.elapsed
            
            elapsed = time.time() - start_time
            self.logger.info(
                f"✓ {test_case.id} [{method}] completed in {elapsed:.2f}s - "
                f"Success: {run_result.success}, "
                f"Score: {correctness.correctness_score:.3f}"
            )
            
            return run_result
            
        except TimeoutError as e:
            self.logger.error(f"✗ {test_case.id} [{method}] timed out: {e}")
            return self._create_timeout_result(test_case, method, str(e))
            
        except Exception as e:
            self.logger.error(f"✗ {test_case.id} [{method}] failed: {e}", exc_info=True)
            return self._create_error_result(test_case, method, str(e))
    
    def _create_timeout_result(self, test_case: TestCase, method: str, error: str) -> RunResult:
        """Create a RunResult for timeout case."""
        from benchmark.test_suite.schemas import FailureMode
        
        return RunResult(
            test_id=test_case.id,
            method=method,
            success=False,
            assembly="",
            correctness=CorrectnessMetrics(
                is_valid_syntax=False,
                constraint_satisfaction_rate=0.0,
                count_match=False,
                type_correctness=0.0,
                register_constraint_violations=0,
                immediate_constraint_violations=0,
                correctness_score=0.0
            ),
            efficiency=EfficiencyMetrics(
                total_time=self.config.timeout_seconds,
                llm_time=0.0,
                llm_call_count=0,
                total_prompt_tokens=0,
                total_completion_tokens=0,
                estimated_cost=0.0
            ),
            robustness=RobustnessMetrics(
                is_success=False,
                failure_mode=FailureMode.TIMEOUT,
                timed_out=True,
                first_attempt_success=False
            ),
            error_log=error
        )
    
    def _create_error_result(self, test_case: TestCase, method: str, error: str) -> RunResult:
        """Create a RunResult for error case."""
        from benchmark.test_suite.schemas import FailureMode
        
        return RunResult(
            test_id=test_case.id,
            method=method,
            success=False,
            assembly="",
            correctness=CorrectnessMetrics(
                is_valid_syntax=False,
                constraint_satisfaction_rate=0.0,
                count_match=False,
                type_correctness=0.0,
                register_constraint_violations=0,
                immediate_constraint_violations=0,
                correctness_score=0.0
            ),
            efficiency=EfficiencyMetrics(
                total_time=0.0,
                llm_time=0.0,
                llm_call_count=0,
                total_prompt_tokens=0,
                total_completion_tokens=0,
                estimated_cost=0.0
            ),
            robustness=RobustnessMetrics(
                is_success=False,
                failure_mode=FailureMode.LLM_ERROR,
                timed_out=False,
                first_attempt_success=False
            ),
            error_log=error
        )
    
    def run_all_tests(self, test_cases: List[TestCase]) -> List[RunResult]:
        """
        Run all test cases with all configured methods.
        
        Args:
            test_cases: List of test cases to execute
        
        Returns:
            List of all RunResults
        """
        all_results = []
        total_tests = len(test_cases) * self.config.num_repetitions
        completed = 0
        
        # Methods to test
        methods = []
        if self.config.to_dict().get('method_a', {}).get('enabled', True):
            methods.append('agent')
        if self.config.to_dict().get('method_b', {}).get('enabled', True):
            methods.append('direct_llm')
        
        total_runs = total_tests * len(methods)
        
        self.logger.info(f"Starting benchmark: {len(test_cases)} tests × {len(methods)} methods × {self.config.num_repetitions} reps = {total_runs} runs")
        
        if self.config.parallel_execution:
            # Parallel execution
            all_results = self._run_parallel(test_cases, methods)
        else:
            # Sequential execution
            for repetition in range(self.config.num_repetitions):
                for test_case in test_cases:
                    for method in methods:
                        result = self.run_single_test(test_case, method, repetition)
                        all_results.append(result)
                        completed += 1
                        
                        # Progress update
                        progress = (completed / total_runs) * 100
                        self.logger.info(f"Progress: {completed}/{total_runs} ({progress:.1f}%)")
        
        self.results = all_results
        return all_results
    
    def _run_parallel(self, test_cases: List[TestCase], methods: List[str]) -> List[RunResult]:
        """
        Run tests in parallel using ThreadPoolExecutor.
        
        Args:
            test_cases: List of test cases
            methods: List of method identifiers
        
        Returns:
            List of RunResults
        """
        all_results = []
        tasks = []
        
        # Build task list
        for repetition in range(self.config.num_repetitions):
            for test_case in test_cases:
                for method in methods:
                    tasks.append((test_case, method, repetition))
        
        self.logger.info(f"Running {len(tasks)} tasks in parallel with {self.config.max_workers} workers")
        
        # Execute in parallel
        with ThreadPoolExecutor(max_workers=self.config.max_workers) as executor:
            future_to_task = {
                executor.submit(self.run_single_test, tc, m, r): (tc.id, m, r)
                for tc, m, r in tasks
            }
            
            for future in as_completed(future_to_task):
                task_info = future_to_task[future]
                try:
                    result = future.result()
                    all_results.append(result)
                    self.logger.info(f"Completed task: {task_info}")
                except Exception as e:
                    self.logger.error(f"Task {task_info} failed: {e}")
        
        return all_results
    
    def save_results(self, results: List[RunResult], prefix: str = "results") -> Dict[str, Path]:
        """
        Save results to CSV and JSON formats.
        
        Args:
            results: List of RunResults to save
            prefix: Filename prefix for output files
        
        Returns:
            Dictionary mapping format to file path
        """
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        
        # Save detailed JSON
        json_path = self.results_dir / f"{prefix}_detailed_{timestamp}.json"
        self._save_json(results, json_path)
        
        # Save summary CSV
        csv_path = self.results_dir / f"{prefix}_summary_{timestamp}.csv"
        self._save_csv(results, csv_path)
        
        self.logger.info(f"Results saved:")
        self.logger.info(f"  - JSON: {json_path}")
        self.logger.info(f"  - CSV: {csv_path}")
        
        output_files = {
            'json': json_path,
            'csv': csv_path
        }
        
        # Generate visualizations if enabled
        config_dict = self.config.to_dict()
        viz_config = config_dict.get('visualization', {})
        report_config = config_dict.get('report', {})
        
        if VISUALIZATION_AVAILABLE:
            if viz_config.get('enabled', True):
                try:
                    self.logger.info("Generating visualizations...")
                    visualizer = BenchmarkVisualizer(
                        output_dir=str(self.results_dir),
                        dpi=viz_config.get('dpi', 300),
                        figsize=tuple(viz_config.get('figure_size', [10, 6]))
                    )
                    charts = visualizer.generate_all_charts(results)
                    output_files['charts'] = charts
                except Exception as e:
                    self.logger.warning(f"Failed to generate visualizations: {e}")
            
            if report_config.get('enabled', True):
                try:
                    self.logger.info("Generating report...")
                    report_gen = ReportGenerator(output_dir=str(self.results_dir))
                    
                    # Load metadata from JSON
                    with open(json_path, 'r') as f:
                        data = json.load(f)
                        metadata = data.get('metadata', {})
                    
                    report_path = report_gen.generate_report(
                        results, 
                        metadata,
                        output_filename=report_config.get('output_file', 'REPORT.md'),
                        include_charts=viz_config.get('enabled', True),
                        chart_dir=self.results_dir
                    )
                    output_files['report'] = report_path
                except Exception as e:
                    self.logger.warning(f"Failed to generate report: {e}")
        else:
            if viz_config.get('enabled', True) or report_config.get('enabled', True):
                self.logger.warning("Visualization/reporting requested but dependencies not available")
                self.logger.warning("Install with: uv pip install matplotlib numpy")
        
        return output_files
    
    def _save_json(self, results: List[RunResult], path: Path) -> None:
        """Save results as JSON."""
        data = {
            'metadata': {
                'timestamp': datetime.now().isoformat(),
                'config': self.config.to_dict(),
                'total_results': len(results)
            },
            'results': [r.to_dict() for r in results]
        }
        
        with open(path, 'w', encoding='utf-8') as f:
            json.dump(data, f, indent=2, ensure_ascii=False)
    
    def _save_csv(self, results: List[RunResult], path: Path) -> None:
        """Save results as CSV (flattened format)."""
        with open(path, 'w', newline='', encoding='utf-8') as f:
            writer = csv.writer(f)
            
            # Header
            header = [
                'test_id', 'difficulty', 'method', 'success',
                # Correctness
                'is_valid_syntax', 'constraint_satisfaction_rate', 'count_match',
                'type_correctness', 'register_violations', 'immediate_violations',
                'correctness_score',
                # Efficiency
                'total_time', 'llm_time', 'compilation_time', 'verification_time',
                'llm_call_count', 'prompt_tokens', 'completion_tokens', 'estimated_cost',
                'retry_count',
                # Robustness
                'failure_mode', 'timed_out', 'first_attempt_success'
            ]
            writer.writerow(header)
            
            # Data rows
            for result in results:
                # Get test case info
                test_cases = {tc.id: tc for tc in get_all_test_cases()}
                test_case = test_cases.get(result.test_id)
                difficulty = test_case.difficulty.value if test_case else 'unknown'
                
                # Extract metrics
                c = result.correctness
                e = result.efficiency
                r = result.robustness
                
                row = [
                    result.test_id,
                    difficulty,
                    result.method,
                    result.success,
                    # Correctness
                    c.is_valid_syntax if c else False,
                    f"{c.constraint_satisfaction_rate:.3f}" if c else "0.000",
                    c.count_match if c else False,
                    f"{c.type_correctness:.3f}" if c else "0.000",
                    c.register_constraint_violations if c else 0,
                    c.immediate_constraint_violations if c else 0,
                    f"{c.correctness_score:.3f}" if c else "0.000",
                    # Efficiency
                    f"{e.total_time:.3f}" if e else "0.000",
                    f"{e.llm_time:.3f}" if e else "0.000",
                    f"{e.compilation_time:.3f}" if e and e.compilation_time else "N/A",
                    f"{e.verification_time:.3f}" if e and e.verification_time else "N/A",
                    e.llm_call_count if e else 0,
                    e.total_prompt_tokens if e else 0,
                    e.total_completion_tokens if e else 0,
                    f"${e.estimated_cost:.4f}" if e else "$0.0000",
                    e.retry_count if e else 0,
                    # Robustness
                    r.failure_mode.value if r else "",
                    r.timed_out if r else False,
                    r.first_attempt_success if r else False
                ]
                writer.writerow(row)
    
    def print_summary(self, results: List[RunResult]) -> None:
        """
        Print a summary of results to console.
        
        Args:
            results: List of RunResults
        """
        print("\n" + "="*80)
        print("BENCHMARK SUMMARY")
        print("="*80)
        
        # Group by method
        by_method = {}
        for result in results:
            method = result.method
            if method not in by_method:
                by_method[method] = []
            by_method[method].append(result)
        
        for method, method_results in by_method.items():
            print(f"\n{method.upper()}:")
            print("-" * 40)
            
            total = len(method_results)
            successful = sum(1 for r in method_results if r.success)
            success_rate = (successful / total * 100) if total > 0 else 0
            
            # Calculate averages
            avg_time = sum(r.efficiency.total_time for r in method_results if r.efficiency) / total
            avg_cost = sum(r.efficiency.estimated_cost for r in method_results if r.efficiency) / total
            avg_correctness = sum(r.correctness.correctness_score for r in method_results if r.correctness) / total
            
            print(f"  Success Rate:     {successful}/{total} ({success_rate:.1f}%)")
            print(f"  Avg Time:         {avg_time:.3f}s")
            print(f"  Avg Cost:         ${avg_cost:.4f}")
            print(f"  Avg Correctness:  {avg_correctness:.3f}")
        
        print("\n" + "="*80)


def load_config_from_yaml(config_path: str) -> BenchmarkConfig:
    """
    Load configuration from YAML file.
    
    Args:
        config_path: Path to YAML configuration file
    
    Returns:
        BenchmarkConfig object
    """
    if yaml is None:
        print("Warning: PyYAML not available, using default config")
        return BenchmarkConfig()
    
    try:
        with open(config_path, 'r') as f:
            config_dict = yaml.safe_load(f)
        
        # Read llm_model from environment variable LLM_MODEL, not from config.yaml
        llm_model = os.getenv('LLM_MODEL', os.getenv('OPENAI_MODEL', 'gpt-4o'))
        
        # Convert to BenchmarkConfig
        return BenchmarkConfig(
            llm_model=llm_model,
            llm_temperature=config_dict.get('llm_temperature', 0.0),
            llm_max_tokens=config_dict.get('llm_max_tokens', 4000),
            timeout_seconds=config_dict.get('timeout_seconds', 300),
            max_retries=config_dict.get('max_retries', 3),
            prompt_token_cost=config_dict.get('prompt_token_cost', 0.0025),
            completion_token_cost=config_dict.get('completion_token_cost', 0.010),
            results_dir=config_dict.get('results_dir', './benchmark_results'),
            save_raw_outputs=config_dict.get('save_raw_outputs', True),
            parallel_execution=config_dict.get('parallel_execution', False),
            max_workers=config_dict.get('max_workers', 4),
            num_repetitions=config_dict.get('num_repetitions', 1)
        )
    except FileNotFoundError:
        print(f"Config file not found: {config_path}, using defaults")
        llm_model = os.getenv('LLM_MODEL', os.getenv('OPENAI_MODEL', 'gpt-4o'))
        return BenchmarkConfig(llm_model=llm_model)
    except Exception as e:
        print(f"Error loading config: {e}, using defaults")
        llm_model = os.getenv('LLM_MODEL', os.getenv('OPENAI_MODEL', 'gpt-4o'))
        return BenchmarkConfig(llm_model=llm_model)


def main():
    """Main entry point for the benchmark."""
    parser = argparse.ArgumentParser(
        description="RVProbe Agent Benchmark - Compare instruction generation methods",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s                              # Run all tests with default config
  %(prog)s --config custom.yaml         # Use custom configuration
  %(prog)s --tests TC-S01 TC-S02        # Run specific tests
  %(prog)s --difficulty simple          # Run only simple tests
  %(prog)s --repetitions 3              # Run each test 3 times
  %(prog)s --parallel --workers 8       # Parallel execution with 8 workers
        """
    )
    
    parser.add_argument(
        '--config', '-c',
        default='config.yaml',
        help='Path to configuration YAML file (default: config.yaml)'
    )
    
    parser.add_argument(
        '--tests', '-t',
        nargs='+',
        help='Specific test IDs to run (e.g., TC-S01 TC-S02)'
    )
    
    parser.add_argument(
        '--difficulty', '-d',
        choices=['simple', 'medium', 'complex'],
        help='Filter tests by difficulty level'
    )
    
    parser.add_argument(
        '--repetitions', '-r',
        type=int,
        help='Number of times to run each test (overrides config)'
    )
    
    parser.add_argument(
        '--parallel', '-p',
        action='store_true',
        help='Enable parallel execution (overrides config)'
    )
    
    parser.add_argument(
        '--workers', '-w',
        type=int,
        help='Number of parallel workers (requires --parallel)'
    )
    
    parser.add_argument(
        '--output-dir', '-o',
        help='Output directory for results (overrides config)'
    )
    
    args = parser.parse_args()
    
    # Load configuration
    config = load_config_from_yaml(args.config)
    
    # Override config with CLI arguments
    if args.repetitions is not None:
        config.num_repetitions = args.repetitions
    if args.parallel:
        config.parallel_execution = True
    if args.workers is not None:
        config.max_workers = args.workers
    if args.output_dir is not None:
        config.results_dir = args.output_dir
    
    # Create orchestrator
    orchestrator = BenchmarkOrchestrator(config)
    
    # Load test cases
    difficulty_filter = [args.difficulty] if args.difficulty else []
    test_cases = orchestrator.load_test_cases(
        selected_tests=args.tests,
        difficulty_filter=difficulty_filter
    )
    
    if not test_cases:
        print("Error: No test cases selected!")
        return 1
    
    # Run benchmark
    print(f"\nStarting benchmark with {len(test_cases)} test cases...")
    print(f"Configuration: {config.llm_model}, repetitions={config.num_repetitions}\n")
    
    try:
        results = orchestrator.run_all_tests(test_cases)
        
        # Save results
        output_files = orchestrator.save_results(results)
        
        # Print summary
        orchestrator.print_summary(results)
        
        print(f"\n✓ Benchmark completed successfully!")
        print(f"  Results saved to: {config.results_dir}")
        
        # List output files
        if 'charts' in output_files:
            print(f"\n  Visualizations:")
            for name, path in output_files['charts'].items():
                print(f"    - {name}: {path.name}")
        
        if 'report' in output_files:
            print(f"\n  Report: {output_files['report'].name}")
        
        return 0
        
    except KeyboardInterrupt:
        print("\n\nBenchmark interrupted by user!")
        if orchestrator.results:
            print("Saving partial results...")
            orchestrator.save_results(orchestrator.results, prefix="partial_results")
        return 130
    
    except Exception as e:
        print(f"\n✗ Benchmark failed: {e}")
        import traceback
        traceback.print_exc()
        return 1


if __name__ == '__main__':
    sys.exit(main())
