"""
Report Generator - Create comprehensive Markdown reports for benchmark results.

Generates detailed analysis reports including:
- Executive summary
- Method comparison tables
- Performance breakdown by difficulty
- Statistical analysis (P50/P95/P99)
- Failure analysis
- Recommendations
"""

import sys
import os
from pathlib import Path
from typing import List, Dict, Any, Optional
from datetime import datetime
from collections import defaultdict
import json

# Add project paths
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '../..')))

from benchmark.test_suite.schemas import RunResult, Difficulty
from benchmark.test_suite.test_cases import get_all_test_cases

import numpy as np
NUMPY_AVAILABLE = True


class ReportGenerator:
    """
    Generate comprehensive Markdown reports for benchmark results.
    
    Creates a detailed analysis report suitable for documentation,
    papers, or technical presentations.
    """
    
    def __init__(self, output_dir: str = "./benchmark_results"):
        """
        Initialize report generator.
        
        Args:
            output_dir: Directory to save reports
        """
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)
        
        # Map test IDs to test cases
        self.test_cases = {tc.id: tc for tc in get_all_test_cases()}
    
    def load_results_from_json(self, json_path: str) -> tuple:
        """
        Load results from JSON file.
        
        Args:
            json_path: Path to JSON results file
        
        Returns:
            Tuple of (results, metadata)
        """
        with open(json_path, 'r') as f:
            data = json.load(f)
        
        results = []
        for result_dict in data['results']:
            result = RunResult.from_dict(result_dict)
            results.append(result)
        
        return results, data.get('metadata', {})
    
    def _calculate_statistics(self, values: List[float]) -> Dict[str, float]:
        """Calculate statistical metrics."""
        if not values:
            return {'mean': 0, 'median': 0, 'p50': 0, 'p95': 0, 'p99': 0, 
                   'std': 0, 'min': 0, 'max': 0}
        
        if NUMPY_AVAILABLE:
            return {
                'mean': np.mean(values),
                'median': np.median(values),
                'p50': np.percentile(values, 50),
                'p95': np.percentile(values, 95),
                'p99': np.percentile(values, 99),
                'std': np.std(values),
                'min': np.min(values),
                'max': np.max(values)
            }
        else:
            sorted_vals = sorted(values)
            n = len(sorted_vals)
            return {
                'mean': sum(values) / n,
                'median': sorted_vals[n // 2],
                'p50': sorted_vals[n // 2],
                'p95': sorted_vals[int(n * 0.95)] if n > 1 else sorted_vals[0],
                'p99': sorted_vals[int(n * 0.99)] if n > 1 else sorted_vals[0],
                'std': 0,  # Not calculated without numpy
                'min': min(values),
                'max': max(values)
            }
    
    def _group_by_method(self, results: List[RunResult]) -> Dict[str, List[RunResult]]:
        """Group results by method."""
        grouped = defaultdict(list)
        for result in results:
            grouped[result.method].append(result)
        return dict(grouped)
    
    def _group_by_difficulty(self, results: List[RunResult]) -> Dict[str, List[RunResult]]:
        """Group results by difficulty."""
        grouped = defaultdict(list)
        for result in results:
            test_case = self.test_cases.get(result.test_id)
            if test_case:
                grouped[test_case.difficulty.value].append(result)
        return dict(grouped)
    
    def generate_executive_summary(self, results: List[RunResult]) -> str:
        """Generate executive summary section."""
        lines = ["## Executive Summary\n"]
        
        by_method = self._group_by_method(results)
        
        for method, method_results in sorted(by_method.items()):
            lines.append(f"### {method.replace('_', ' ').title()}\n")
            
            total = len(method_results)
            successful = sum(1 for r in method_results if r.success)
            success_rate = (successful / total * 100) if total > 0 else 0
            
            # Calculate averages
            times = [r.efficiency.total_time for r in method_results if r.efficiency]
            costs = [r.efficiency.estimated_cost for r in method_results if r.efficiency]
            scores = [r.correctness.correctness_score for r in method_results if r.correctness]
            
            avg_time = sum(times) / len(times) if times else 0
            total_cost = sum(costs)
            avg_score = sum(scores) / len(scores) if scores else 0
            
            lines.append(f"- **Overall Success Rate**: {successful}/{total} ({success_rate:.1f}%)")
            lines.append(f"- **Average Execution Time**: {avg_time:.3f}s")
            lines.append(f"- **Total API Cost**: ${total_cost:.4f}")
            lines.append(f"- **Average Correctness Score**: {avg_score:.3f}")
            
            # Retry info for agent
            if 'agent' in method.lower():
                retry_counts = [r.efficiency.retry_count for r in method_results if r.efficiency]
                avg_retries = sum(retry_counts) / len(retry_counts) if retry_counts else 0
                lines.append(f"- **Average Retry Count**: {avg_retries:.2f}")
            
            lines.append("")
        
        return "\n".join(lines)
    
    def generate_comparison_table(self, results: List[RunResult]) -> str:
        """Generate method comparison table."""
        lines = ["## Method Comparison\n"]
        
        by_method = self._group_by_method(results)
        
        # Table header
        lines.append("| Metric | " + " | ".join(m.replace('_', ' ').title() for m in sorted(by_method.keys())) + " | Winner |")
        lines.append("|--------|" + "|".join("--------" for _ in by_method) + "|--------|")
        
        # Success Rate
        success_rates = {}
        for method, method_results in by_method.items():
            total = len(method_results)
            successful = sum(1 for r in method_results if r.success)
            success_rates[method] = (successful / total * 100) if total > 0 else 0
        
        winner = max(success_rates, key=success_rates.get)
        row = "| Success Rate (%) | " + " | ".join(f"{success_rates[m]:.1f}" for m in sorted(by_method.keys()))
        row += f" | **{winner.replace('_', ' ').title()}** |"
        lines.append(row)
        
        # Average Time
        avg_times = {}
        for method, method_results in by_method.items():
            times = [r.efficiency.total_time for r in method_results if r.efficiency]
            avg_times[method] = sum(times) / len(times) if times else 0
        
        winner = min(avg_times, key=avg_times.get)
        row = "| Avg Time (s) | " + " | ".join(f"{avg_times[m]:.3f}" for m in sorted(by_method.keys()))
        row += f" | **{winner.replace('_', ' ').title()}** |"
        lines.append(row)
        
        # Total Cost
        total_costs = {}
        for method, method_results in by_method.items():
            costs = [r.efficiency.estimated_cost for r in method_results if r.efficiency]
            total_costs[method] = sum(costs)
        
        winner = min(total_costs, key=total_costs.get)
        row = "| Total Cost ($) | " + " | ".join(f"${total_costs[m]:.4f}" for m in sorted(by_method.keys()))
        row += f" | **{winner.replace('_', ' ').title()}** |"
        lines.append(row)
        
        # Avg Correctness
        avg_correctness = {}
        for method, method_results in by_method.items():
            scores = [r.correctness.correctness_score for r in method_results if r.correctness]
            avg_correctness[method] = sum(scores) / len(scores) if scores else 0
        
        winner = max(avg_correctness, key=avg_correctness.get)
        row = "| Avg Correctness | " + " | ".join(f"{avg_correctness[m]:.3f}" for m in sorted(by_method.keys()))
        row += f" | **{winner.replace('_', ' ').title()}** |"
        lines.append(row)
        
        lines.append("")
        return "\n".join(lines)
    
    def generate_difficulty_breakdown(self, results: List[RunResult]) -> str:
        """Generate breakdown by difficulty level."""
        lines = ["## Results by Difficulty Level\n"]
        
        by_difficulty = self._group_by_difficulty(results)
        
        for difficulty in ['simple', 'medium', 'complex']:
            if difficulty not in by_difficulty:
                continue
            
            lines.append(f"### {difficulty.title()} Tests\n")
            
            diff_results = by_difficulty[difficulty]
            by_method = self._group_by_method(diff_results)
            
            # Table
            lines.append("| Method | Success Rate | Avg Time (s) | Avg Correctness |")
            lines.append("|--------|--------------|--------------|-----------------|")
            
            for method, method_results in sorted(by_method.items()):
                total = len(method_results)
                successful = sum(1 for r in method_results if r.success)
                success_rate = (successful / total * 100) if total > 0 else 0
                
                times = [r.efficiency.total_time for r in method_results if r.efficiency]
                avg_time = sum(times) / len(times) if times else 0
                
                scores = [r.correctness.correctness_score for r in method_results if r.correctness]
                avg_score = sum(scores) / len(scores) if scores else 0
                
                lines.append(f"| {method.replace('_', ' ').title()} | "
                           f"{success_rate:.1f}% ({successful}/{total}) | "
                           f"{avg_time:.3f} | "
                           f"{avg_score:.3f} |")
            
            lines.append("")
        
        return "\n".join(lines)
    
    def generate_performance_analysis(self, results: List[RunResult]) -> str:
        """Generate statistical performance analysis."""
        lines = ["## Performance Analysis\n"]
        
        by_method = self._group_by_method(results)
        
        for method, method_results in sorted(by_method.items()):
            lines.append(f"### {method.replace('_', ' ').title()}\n")
            
            # Execution time statistics
            times = [r.efficiency.total_time for r in method_results if r.efficiency]
            if times:
                stats = self._calculate_statistics(times)
                lines.append("**Execution Time Statistics:**\n")
                lines.append(f"- Mean: {stats['mean']:.3f}s")
                lines.append(f"- Median (P50): {stats['p50']:.3f}s")
                lines.append(f"- P95: {stats['p95']:.3f}s")
                lines.append(f"- P99: {stats['p99']:.3f}s")
                lines.append(f"- Range: [{stats['min']:.3f}s, {stats['max']:.3f}s]")
                if NUMPY_AVAILABLE:
                    lines.append(f"- Std Dev: {stats['std']:.3f}s")
                lines.append("")
            
            # Correctness score statistics
            scores = [r.correctness.correctness_score for r in method_results if r.correctness]
            if scores:
                stats = self._calculate_statistics(scores)
                lines.append("**Correctness Score Statistics:**\n")
                lines.append(f"- Mean: {stats['mean']:.3f}")
                lines.append(f"- Median: {stats['median']:.3f}")
                lines.append(f"- Range: [{stats['min']:.3f}, {stats['max']:.3f}]")
                lines.append("")
        
        return "\n".join(lines)
    
    def generate_failure_analysis(self, results: List[RunResult]) -> str:
        """Generate failure analysis section."""
        lines = ["## Failure Analysis\n"]
        
        by_method = self._group_by_method(results)
        
        for method, method_results in sorted(by_method.items()):
            failed = [r for r in method_results if not r.success]
            
            if not failed:
                lines.append(f"### {method.replace('_', ' ').title()}\n")
                lines.append("✓ No failures recorded\n")
                continue
            
            lines.append(f"### {method.replace('_', ' ').title()}\n")
            lines.append(f"**Total Failures**: {len(failed)}/{len(method_results)} "
                        f"({len(failed)/len(method_results)*100:.1f}%)\n")
            
            # Count failure modes
            failure_modes = defaultdict(int)
            for r in failed:
                if r.robustness:
                    mode = r.robustness.failure_mode
                    if hasattr(mode, 'value'):
                        mode = mode.value
                    mode = mode or 'unknown'
                    failure_modes[mode] += 1
            
            if failure_modes:
                lines.append("**Failure Modes:**\n")
                for mode, count in sorted(failure_modes.items(), key=lambda x: x[1], reverse=True):
                    pct = count / len(failed) * 100
                    lines.append(f"- {mode.replace('_', ' ').title()}: {count} ({pct:.1f}%)")
                lines.append("")
            
            # List failed test cases
            lines.append("**Failed Test Cases:**\n")
            for r in failed[:10]:  # Show up to 10
                test_case = self.test_cases.get(r.test_id)
                difficulty = test_case.difficulty.value if test_case else 'unknown'
                mode = r.robustness.failure_mode
                if hasattr(mode, 'value'):
                    mode = mode.value
                mode = mode or 'unknown'
                lines.append(f"- `{r.test_id}` ({difficulty}) - {mode}")
            
            if len(failed) > 10:
                lines.append(f"- ... and {len(failed) - 10} more")
            
            lines.append("")
            
            # Show detailed failure information with generated code
            if 'agent' in method.lower() and failed:
                lines.append("**Detailed Failure Cases:**\n")
                for r in failed[:5]:  # Show detailed info for up to 5 failures
                    test_case = self.test_cases.get(r.test_id)
                    lines.append(f"#### {r.test_id} - {test_case.description if test_case else 'N/A'}\n")
                    
                    # Test case parameters
                    if test_case:
                        lines.append(f"- **Expected Count**: {test_case.expected_count}")
                        lines.append(f"- **Instruction Types**: {', '.join(test_case.instruction_types[:5])}{'...' if len(test_case.instruction_types) > 5 else ''}")
                        if test_case.register_constraints:
                            lines.append(f"- **Register Constraints**: {test_case.register_constraints}")
                        if test_case.immediate_constraints:
                            lines.append(f"- **Immediate Constraints**: {test_case.immediate_constraints}")
                    
                    # Failure information
                    if r.robustness:
                        failure_mode = r.robustness.failure_mode
                        if hasattr(failure_mode, 'value'):
                            failure_mode = failure_mode.value
                        lines.append(f"- **Failure Mode**: {failure_mode}")
                        lines.append(f"- **Retry Count**: {r.efficiency.retry_count if r.efficiency else 0}")
                    
                    # Show generated DSL code if available
                    if hasattr(r, 'metadata') and r.metadata and 'dsl_code' in r.metadata:
                        dsl_code = r.metadata['dsl_code']
                        if dsl_code:
                            lines.append("\n**Generated DSL Code:**\n")
                            lines.append("```scala")
                            lines.append(dsl_code)
                            lines.append("```\n")
                    
                    # Show error log excerpt if available
                    if hasattr(r, 'error_log') and r.error_log:
                        # Extract compilation error from log
                        error_lines = r.error_log.split('\n')
                        error_section = []
                        in_error = False
                        for line in error_lines:
                            if '[error]' in line.lower():
                                in_error = True
                                error_section.append(line)
                            elif in_error:
                                if line.strip() and not line.startswith('['):
                                    error_section.append(line)
                                elif line.startswith('[') and '[error]' not in line.lower():
                                    break
                        
                        if error_section:
                            lines.append("**Compilation Error:**\n")
                            lines.append("```")
                            lines.append('\n'.join(error_section[:10]))  # First 10 error lines
                            if len(error_section) > 10:
                                lines.append("... (truncated)")
                            lines.append("```\n")
                    
                    lines.append("---\n")
        
        return "\n".join(lines)
    
    def generate_recommendations(self, results: List[RunResult]) -> str:
        """Generate recommendations based on results."""
        lines = ["## Recommendations\n"]
        
        by_method = self._group_by_method(results)
        
        # Calculate key metrics
        metrics = {}
        for method, method_results in by_method.items():
            total = len(method_results)
            successful = sum(1 for r in method_results if r.success)
            success_rate = (successful / total * 100) if total > 0 else 0
            
            times = [r.efficiency.total_time for r in method_results if r.efficiency]
            avg_time = sum(times) / len(times) if times else 0
            
            costs = [r.efficiency.estimated_cost for r in method_results if r.efficiency]
            total_cost = sum(costs)
            
            scores = [r.correctness.correctness_score for r in method_results if r.correctness]
            avg_score = sum(scores) / len(scores) if scores else 0
            
            metrics[method] = {
                'success_rate': success_rate,
                'avg_time': avg_time,
                'total_cost': total_cost,
                'avg_score': avg_score
            }
        
        # Generate recommendations
        lines.append("### When to Use Each Method\n")
        
        best_accuracy = max(metrics.items(), key=lambda x: x[1]['success_rate'])
        best_speed = min(metrics.items(), key=lambda x: x[1]['avg_time'])
        best_cost = min(metrics.items(), key=lambda x: x[1]['total_cost'])
        
        lines.append(f"**For Maximum Accuracy**: Use **{best_accuracy[0].replace('_', ' ').title()}**")
        lines.append(f"- Success rate: {best_accuracy[1]['success_rate']:.1f}%")
        lines.append(f"- Average correctness: {best_accuracy[1]['avg_score']:.3f}")
        lines.append("")
        
        lines.append(f"**For Fastest Execution**: Use **{best_speed[0].replace('_', ' ').title()}**")
        lines.append(f"- Average time: {best_speed[1]['avg_time']:.3f}s")
        lines.append("")
        
        lines.append(f"**For Lowest Cost**: Use **{best_cost[0].replace('_', ' ').title()}**")
        lines.append(f"- Total cost: ${best_cost[1]['total_cost']:.4f}")
        lines.append("")
        
        lines.append("### General Recommendations\n")
        
        # Add specific recommendations based on results
        if len(by_method) >= 2:
            methods = list(by_method.keys())
            m1, m2 = methods[0], methods[1]
            
            if metrics[m1]['success_rate'] > metrics[m2]['success_rate'] + 10:
                lines.append(f"- {m1.replace('_', ' ').title()} shows significantly higher success rate "
                           f"({metrics[m1]['success_rate']:.1f}% vs {metrics[m2]['success_rate']:.1f}%), "
                           f"suggesting verification is valuable")
            
            if metrics[m1]['avg_time'] > metrics[m2]['avg_time'] * 2:
                lines.append(f"- {m2.replace('_', ' ').title()} is {metrics[m1]['avg_time']/metrics[m2]['avg_time']:.1f}× faster, "
                           f"making it suitable for time-sensitive applications")
            
            lines.append("- Consider using faster method for simple cases and verified method for complex constraints")
            lines.append("- Implement timeout mechanisms for production use")
            lines.append("- Monitor API costs in production environments")
        
        lines.append("")
        return "\n".join(lines)
    
    def generate_report(self, results: List[RunResult], 
                       metadata: Dict[str, Any],
                       output_filename: str = "REPORT.md",
                       include_charts: bool = True,
                       chart_dir: Optional[Path] = None) -> Path:
        """
        Generate complete Markdown report.
        
        Args:
            results: List of RunResult objects
            metadata: Benchmark metadata
            output_filename: Output filename
            include_charts: Whether to include chart references
            chart_dir: Directory containing charts (relative paths)
        
        Returns:
            Path to generated report
        """
        lines = []
        
        # Title and metadata
        lines.append("# RVProbe Agent Benchmark Report\n")
        lines.append(f"**Generated**: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n")
        
        if metadata:
            lines.append("**Configuration:**")
            config = metadata.get('config', {})
            lines.append(f"- Model: {config.get('llm_model', 'N/A')}")
            lines.append(f"- Temperature: {config.get('llm_temperature', 'N/A')}")
            lines.append(f"- Timeout: {config.get('timeout_seconds', 'N/A')}s")
            lines.append(f"- Total Results: {metadata.get('total_results', len(results))}")
            lines.append("")
        
        # Table of Contents
        lines.append("## Table of Contents\n")
        lines.append("1. [Executive Summary](#executive-summary)")
        lines.append("2. [Method Comparison](#method-comparison)")
        lines.append("3. [Results by Difficulty Level](#results-by-difficulty-level)")
        lines.append("4. [Performance Analysis](#performance-analysis)")
        lines.append("5. [Failure Analysis](#failure-analysis)")
        lines.append("6. [Recommendations](#recommendations)")
        if include_charts:
            lines.append("7. [Visualizations](#visualizations)")
        lines.append("\n---\n")
        
        # Generate sections
        lines.append(self.generate_executive_summary(results))
        lines.append(self.generate_comparison_table(results))
        lines.append(self.generate_difficulty_breakdown(results))
        lines.append(self.generate_performance_analysis(results))
        lines.append(self.generate_failure_analysis(results))
        lines.append(self.generate_recommendations(results))
        
        # Add chart references
        if include_charts and chart_dir:
            lines.append("## Visualizations\n")
            
            chart_files = [
                ("success_rate_by_difficulty.png", "Success Rate by Difficulty"),
                ("time_distribution.png", "Execution Time Distribution"),
                ("cost_comparison.png", "API Cost Comparison"),
                ("correctness_scores.png", "Correctness Score Distribution"),
                ("failure_modes.png", "Failure Mode Distribution")
            ]
            
            for filename, title in chart_files:
                chart_path = chart_dir / filename
                if chart_path.exists():
                    lines.append(f"### {title}\n")
                    lines.append(f"![{title}]({filename})\n")
        
        # Footer
        lines.append("\n---\n")
        lines.append("*Report generated by RVProbe Benchmark Framework*\n")
        
        # Write report
        report_path = self.output_dir / output_filename
        with open(report_path, 'w', encoding='utf-8') as f:
            f.write("\n".join(lines))
        
        print(f"✓ Report generated: {report_path}")
        return report_path


def main():
    """Test report generator with sample data."""
    import argparse
    
    parser = argparse.ArgumentParser(description="Generate benchmark report")
    parser.add_argument('json_file', help='Path to JSON results file')
    parser.add_argument('--output-dir', '-o', default='./benchmark_results',
                       help='Output directory for report')
    parser.add_argument('--output-file', '-f', default='REPORT.md',
                       help='Output filename')
    parser.add_argument('--include-charts', action='store_true',
                       help='Include chart references in report')
    
    args = parser.parse_args()
    
    # Create report generator
    generator = ReportGenerator(output_dir=args.output_dir)
    
    # Load results
    print(f"Loading results from: {args.json_file}")
    results, metadata = generator.load_results_from_json(args.json_file)
    print(f"Loaded {len(results)} results")
    
    # Generate report
    chart_dir = Path(args.output_dir) if args.include_charts else None
    report_path = generator.generate_report(
        results, metadata, 
        output_filename=args.output_file,
        include_charts=args.include_charts,
        chart_dir=chart_dir
    )
    
    print(f"\n✓ Report complete: {report_path}")


if __name__ == '__main__':
    main()
