"""
Visualizer - Generate charts and graphs for benchmark results.

Creates publication-quality visualizations comparing different methods across
various metrics: success rate, time distribution, cost, failure modes, etc.
"""

import sys
import os
from pathlib import Path
from typing import List, Dict, Any, Optional
import json

# Add project paths
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '../..')))

from benchmark.test_suite.schemas import RunResult, Difficulty

# Try to import plotting libraries
import matplotlib
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
from matplotlib.gridspec import GridSpec
import numpy as np
import pandas as pd


matplotlib.use('Agg')  # Non-interactive backend for server environments
MATPLOTLIB_AVAILABLE = True
PANDAS_AVAILABLE = True

class BenchmarkVisualizer:
    """
    Generate visualizations for benchmark results.
    
    Creates multiple charts:
    1. Success rate comparison by difficulty
    2. Time distribution histograms
    3. Cost comparison bar chart
    4. Failure mode pie chart
    5. Correctness score box plots
    """
    
    def __init__(self, output_dir: str = "./benchmark_results", 
                 dpi: int = 300,
                 figsize: tuple = (10, 6),
                 style: str = 'seaborn-v0_8-darkgrid'):
        """
        Initialize visualizer.
        
        Args:
            output_dir: Directory to save charts
            dpi: Resolution for output images
            figsize: Default figure size (width, height) in inches
            style: Matplotlib style to use
        """
        if not MATPLOTLIB_AVAILABLE:
            raise RuntimeError("matplotlib is required for visualization")
        
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)
        
        self.dpi = dpi
        self.figsize = figsize
        
        # Set style
        try:
            plt.style.use(style)
        except:
            plt.style.use('default')
        
        # Color scheme
        self.colors = {
            'agent': '#2E86AB',      # Blue
            'direct_llm': '#A23B72', # Purple
            'simple': '#06A77D',     # Green
            'medium': '#F18F01',     # Orange
            'complex': '#C73E1D'     # Red
        }
    
    def load_results_from_json(self, json_path: str) -> List[RunResult]:
        """
        Load results from JSON file.
        
        Args:
            json_path: Path to JSON results file
        
        Returns:
            List of RunResult objects
        """
        with open(json_path, 'r') as f:
            data = json.load(f)
        
        results = []
        for result_dict in data['results']:
            result = RunResult.from_dict(result_dict)
            results.append(result)
        
        return results
    
    def plot_success_rate_by_difficulty(self, results: List[RunResult], 
                                        output_filename: str = "success_rate_by_difficulty.png"):
        """
        Plot success rate comparison grouped by difficulty level.
        
        Args:
            results: List of RunResult objects
            output_filename: Output filename
        """
        from benchmark.test_suite.test_cases import get_all_test_cases
        
        # Map test IDs to difficulty
        test_cases = {tc.id: tc for tc in get_all_test_cases()}
        
        # Group results by method and difficulty
        grouped = {}
        for result in results:
            method = result.method
            test_case = test_cases.get(result.test_id)
            if not test_case:
                continue
            
            difficulty = test_case.difficulty.value
            
            key = (method, difficulty)
            if key not in grouped:
                grouped[key] = {'total': 0, 'success': 0}
            
            grouped[key]['total'] += 1
            if result.success:
                grouped[key]['success'] += 1
        
        # Calculate success rates
        data = {}
        difficulties = ['simple', 'medium', 'complex']
        methods = sorted(set(m for m, d in grouped.keys()))
        
        for method in methods:
            data[method] = []
            for difficulty in difficulties:
                key = (method, difficulty)
                if key in grouped:
                    rate = grouped[key]['success'] / grouped[key]['total'] * 100
                    data[method].append(rate)
                else:
                    data[method].append(0)
        
        # Plot
        fig, ax = plt.subplots(figsize=self.figsize, dpi=self.dpi)
        
        x = np.arange(len(difficulties))
        width = 0.35
        
        for i, (method, rates) in enumerate(data.items()):
            offset = width * (i - len(data) / 2 + 0.5)
            bars = ax.bar(x + offset, rates, width, 
                         label=method.replace('_', ' ').title(),
                         color=self.colors.get(method, f'C{i}'))
            
            # Add value labels on bars
            for bar in bars:
                height = bar.get_height()
                ax.text(bar.get_x() + bar.get_width() / 2., height,
                       f'{height:.1f}%',
                       ha='center', va='bottom', fontsize=9)
        
        ax.set_xlabel('Difficulty Level', fontsize=12, fontweight='bold')
        ax.set_ylabel('Success Rate (%)', fontsize=12, fontweight='bold')
        ax.set_title('Success Rate Comparison by Difficulty', 
                    fontsize=14, fontweight='bold', pad=20)
        ax.set_xticks(x)
        ax.set_xticklabels([d.title() for d in difficulties])
        ax.set_ylim(0, 110)
        ax.legend(loc='upper right')
        ax.grid(axis='y', alpha=0.3)
        
        plt.tight_layout()
        output_path = self.output_dir / output_filename
        plt.savefig(output_path, dpi=self.dpi, bbox_inches='tight')
        plt.close()
        
        print(f"  ✓ Success rate chart saved: {output_path}")
        return output_path
    
    def plot_time_distribution(self, results: List[RunResult],
                               output_filename: str = "time_distribution.png"):
        """
        Plot time distribution histograms for each method.
        
        Args:
            results: List of RunResult objects
            output_filename: Output filename
        """
        # Group times by method
        times_by_method = {}
        for result in results:
            if not result.efficiency:
                continue
            
            method = result.method
            if method not in times_by_method:
                times_by_method[method] = []
            
            times_by_method[method].append(result.efficiency.total_time)
        
        # Plot
        fig, axes = plt.subplots(1, len(times_by_method), 
                                figsize=(self.figsize[0] * len(times_by_method) / 2, self.figsize[1]),
                                dpi=self.dpi)
        
        if len(times_by_method) == 1:
            axes = [axes]
        
        for ax, (method, times) in zip(axes, times_by_method.items()):
            ax.hist(times, bins=20, color=self.colors.get(method, 'steelblue'),
                   alpha=0.7, edgecolor='black')
            
            # Add statistics
            mean_time = np.mean(times)
            median_time = np.median(times)
            
            ax.axvline(mean_time, color='red', linestyle='--', linewidth=2, 
                      label=f'Mean: {mean_time:.2f}s')
            ax.axvline(median_time, color='green', linestyle='-.', linewidth=2,
                      label=f'Median: {median_time:.2f}s')
            
            ax.set_xlabel('Time (seconds)', fontsize=11, fontweight='bold')
            ax.set_ylabel('Frequency', fontsize=11, fontweight='bold')
            ax.set_title(f'{method.replace("_", " ").title()}', 
                        fontsize=12, fontweight='bold')
            ax.legend()
            ax.grid(axis='y', alpha=0.3)
        
        fig.suptitle('Execution Time Distribution', 
                    fontsize=14, fontweight='bold', y=1.02)
        
        plt.tight_layout()
        output_path = self.output_dir / output_filename
        plt.savefig(output_path, dpi=self.dpi, bbox_inches='tight')
        plt.close()
        
        print(f"  ✓ Time distribution chart saved: {output_path}")
        return output_path
    
    def plot_cost_comparison(self, results: List[RunResult],
                            output_filename: str = "cost_comparison.png"):
        """
        Plot cost comparison bar chart.
        
        Args:
            results: List of RunResult objects
            output_filename: Output filename
        """
        # Calculate total cost per method
        costs_by_method = {}
        for result in results:
            if not result.efficiency:
                continue
            
            method = result.method
            if method not in costs_by_method:
                costs_by_method[method] = 0
            
            costs_by_method[method] += result.efficiency.estimated_cost
        
        # Plot
        fig, ax = plt.subplots(figsize=(8, 6), dpi=self.dpi)
        
        methods = list(costs_by_method.keys())
        costs = list(costs_by_method.values())
        colors = [self.colors.get(m, f'C{i}') for i, m in enumerate(methods)]
        
        bars = ax.bar(methods, costs, color=colors, alpha=0.7, edgecolor='black')
        
        # Add value labels
        for bar, cost in zip(bars, costs):
            height = bar.get_height()
            ax.text(bar.get_x() + bar.get_width() / 2., height,
                   f'${cost:.4f}',
                   ha='center', va='bottom', fontsize=11, fontweight='bold')
        
        ax.set_xlabel('Method', fontsize=12, fontweight='bold')
        ax.set_ylabel('Total Cost (USD)', fontsize=12, fontweight='bold')
        ax.set_title('Total API Cost Comparison', 
                    fontsize=14, fontweight='bold', pad=20)
        ax.set_xticklabels([m.replace('_', ' ').title() for m in methods])
        ax.grid(axis='y', alpha=0.3)
        
        plt.tight_layout()
        output_path = self.output_dir / output_filename
        plt.savefig(output_path, dpi=self.dpi, bbox_inches='tight')
        plt.close()
        
        print(f"  ✓ Cost comparison chart saved: {output_path}")
        return output_path
    
    def plot_failure_modes(self, results: List[RunResult],
                          output_filename: str = "failure_modes.png"):
        """
        Plot failure mode pie chart.
        
        Args:
            results: List of RunResult objects
            output_filename: Output filename
        """
        # Count failure modes
        failure_counts = {}
        for result in results:
            if result.success:
                continue
            
            if not result.robustness:
                continue
            
            mode = result.robustness.failure_mode.value
            if not mode:
                mode = 'unknown'
            
            failure_counts[mode] = failure_counts.get(mode, 0) + 1
        
        if not failure_counts:
            print("  ⚠ No failures to plot")
            return None
        
        # Plot
        fig, ax = plt.subplots(figsize=(8, 8), dpi=self.dpi)
        
        labels = [m.replace('_', ' ').title() for m in failure_counts.keys()]
        sizes = list(failure_counts.values())
        colors = plt.cm.Set3(range(len(labels)))
        
        wedges, texts, autotexts = ax.pie(sizes, labels=labels, autopct='%1.1f%%',
                                          colors=colors, startangle=90)
        
        # Enhance text
        for text in texts:
            text.set_fontsize(11)
            text.set_fontweight('bold')
        
        for autotext in autotexts:
            autotext.set_color('white')
            autotext.set_fontsize(10)
            autotext.set_fontweight('bold')
        
        ax.set_title('Failure Mode Distribution', 
                    fontsize=14, fontweight='bold', pad=20)
        
        plt.tight_layout()
        output_path = self.output_dir / output_filename
        plt.savefig(output_path, dpi=self.dpi, bbox_inches='tight')
        plt.close()
        
        print(f"  ✓ Failure modes chart saved: {output_path}")
        return output_path
    
    def plot_correctness_scores(self, results: List[RunResult],
                               output_filename: str = "correctness_scores.png"):
        """
        Plot correctness score box plots by method.
        
        Args:
            results: List of RunResult objects
            output_filename: Output filename
        """
        # Group scores by method
        scores_by_method = {}
        for result in results:
            if not result.correctness:
                continue
            
            method = result.method
            if method not in scores_by_method:
                scores_by_method[method] = []
            
            scores_by_method[method].append(result.correctness.correctness_score)
        
        # Plot
        fig, ax = plt.subplots(figsize=(8, 6), dpi=self.dpi)
        
        methods = list(scores_by_method.keys())
        data = [scores_by_method[m] for m in methods]
        
        bp = ax.boxplot(data, labels=[m.replace('_', ' ').title() for m in methods],
                       patch_artist=True, notch=True, showmeans=True)
        
        # Color boxes
        for patch, method in zip(bp['boxes'], methods):
            patch.set_facecolor(self.colors.get(method, 'lightblue'))
            patch.set_alpha(0.7)
        
        ax.set_xlabel('Method', fontsize=12, fontweight='bold')
        ax.set_ylabel('Correctness Score', fontsize=12, fontweight='bold')
        ax.set_title('Correctness Score Distribution', 
                    fontsize=14, fontweight='bold', pad=20)
        ax.set_ylim(0, 1.05)
        ax.grid(axis='y', alpha=0.3)
        
        plt.tight_layout()
        output_path = self.output_dir / output_filename
        plt.savefig(output_path, dpi=self.dpi, bbox_inches='tight')
        plt.close()
        
        print(f"  ✓ Correctness scores chart saved: {output_path}")
        return output_path
    
    def generate_all_charts(self, results: List[RunResult]) -> Dict[str, Path]:
        """
        Generate all visualization charts.
        
        Args:
            results: List of RunResult objects
        
        Returns:
            Dictionary mapping chart name to file path
        """
        print("\nGenerating visualization charts...")
        print("=" * 60)
        
        charts = {}
        
        try:
            charts['success_rate'] = self.plot_success_rate_by_difficulty(results)
        except Exception as e:
            print(f"  ✗ Failed to generate success rate chart: {e}")
        
        try:
            charts['time_dist'] = self.plot_time_distribution(results)
        except Exception as e:
            print(f"  ✗ Failed to generate time distribution chart: {e}")
        
        try:
            charts['cost'] = self.plot_cost_comparison(results)
        except Exception as e:
            print(f"  ✗ Failed to generate cost comparison chart: {e}")
        
        try:
            charts['failures'] = self.plot_failure_modes(results)
        except Exception as e:
            print(f"  ✗ Failed to generate failure modes chart: {e}")
        
        try:
            charts['correctness'] = self.plot_correctness_scores(results)
        except Exception as e:
            print(f"  ✗ Failed to generate correctness scores chart: {e}")
        
        print("=" * 60)
        print(f"✓ Generated {len([v for v in charts.values() if v])} charts\n")
        
        return {k: v for k, v in charts.items() if v is not None}


def main():
    """Test visualizer with sample data."""
    import argparse
    
    parser = argparse.ArgumentParser(description="Generate benchmark visualization charts")
    parser.add_argument('json_file', help='Path to JSON results file')
    parser.add_argument('--output-dir', '-o', default='./benchmark_results',
                       help='Output directory for charts')
    parser.add_argument('--dpi', type=int, default=300,
                       help='Image resolution (DPI)')
    
    args = parser.parse_args()
    
    # Create visualizer
    visualizer = BenchmarkVisualizer(output_dir=args.output_dir, dpi=args.dpi)
    
    # Load results
    print(f"Loading results from: {args.json_file}")
    results = visualizer.load_results_from_json(args.json_file)
    print(f"Loaded {len(results)} results")
    
    # Generate all charts
    charts = visualizer.generate_all_charts(results)
    
    print(f"\n✓ Visualization complete! Charts saved to: {args.output_dir}")
    for name, path in charts.items():
        print(f"  - {name}: {path.name}")


if __name__ == '__main__':
    main()
