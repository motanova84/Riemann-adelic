#!/usr/bin/env python3
"""
Performance monitoring and benchmarking utility for Riemann-Adelic validation.

This script:
1. Runs validation with different parameter sets
2. Tracks execution time and memory usage
3. Records accuracy metrics and convergence behavior
4. Generates performance reports and trends
5. Helps optimize computational parameters for CI/CD

Usage:
    python utils/performance_monitor.py [--benchmark] [--profile] [--report]
"""

import os
import sys
import time
import json
import psutil
import datetime
from typing import Dict, List, Tuple, Optional
from dataclasses import dataclass, asdict
import subprocess
import tempfile

# Add project root to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import mpmath as mp

# Import functions only when needed to avoid circular imports
def _import_validation_functions():
    """Lazy import to avoid circular dependency."""
    try:
        from validate_explicit_formula import prime_sum, archimedean_sum, zero_sum_limited, weil_explicit_formula
        from utils.mellin import truncated_gaussian
        return prime_sum, archimedean_sum, zero_sum_limited, weil_explicit_formula, truncated_gaussian
    except ImportError:
        return None, None, None, None, None

@dataclass
class PerformanceMetrics:
    """Container for performance metrics."""
    timestamp: str
    test_name: str
    parameters: Dict
    execution_time: float
    memory_peak_mb: float
    memory_average_mb: float
    arithmetic_result: str
    zero_result: str
    absolute_error: str
    relative_error: str
    convergence_rate: Optional[float] = None
    stability_score: Optional[float] = None

class PerformanceMonitor:
    """Performance monitoring and benchmarking utility."""
    
    def __init__(self, output_dir: str = "logs/performance"):
        self.output_dir = output_dir
        os.makedirs(output_dir, exist_ok=True)
        self.process = psutil.Process()
        self.baseline_memory = self.process.memory_info().rss / 1024 / 1024  # MB
        
    def monitor_memory(self, interval: float = 0.1) -> List[float]:
        """Monitor memory usage during execution."""
        memory_samples = []
        start_time = time.time()
        
        while time.time() - start_time < 1.0:  # Monitor for 1 second max
            try:
                mem_info = self.process.memory_info()
                memory_mb = mem_info.rss / 1024 / 1024
                memory_samples.append(memory_mb - self.baseline_memory)
                time.sleep(interval)
            except (psutil.NoSuchProcess, psutil.AccessDenied):
                break
                
        return memory_samples
    
    def benchmark_validation(self, test_name: str, params: Dict) -> PerformanceMetrics:
        """Benchmark a validation run with given parameters."""
        print(f"🔬 Benchmarking: {test_name}")
        print(f"📊 Parameters: {params}")
        
        # Set precision
        mp.mp.dps = params.get('precision_dps', 15)
        
        # Extract parameters
        P = params.get('max_primes', 100)
        K = params.get('prime_powers', 5) 
        max_zeros = params.get('max_zeros', 100)
        T = params.get('integration_t', 10)
        sigma0 = params.get('sigma0', 2.0)
        lim_u = params.get('lim_u', 3.0)
        
        # Import functions lazily to avoid circular imports
        prime_sum, archimedean_sum, zero_sum_limited, weil_explicit_formula, truncated_gaussian = _import_validation_functions()
        
        if not all([prime_sum, archimedean_sum, zero_sum_limited, truncated_gaussian]):
            print("  ⚠️ Validation functions not available, skipping benchmark")
            return PerformanceMetrics(
                timestamp=datetime.now().isoformat(),
                test_name=test_name,
                parameters=params,
                execution_time=0.0,
                memory_peak=0.0,
                memory_samples=[],
                error_metrics={},
                convergence_data={},
                metadata={"status": "skipped", "reason": "circular_import_avoidance"}
            )
        
        f = truncated_gaussian
        zeros_file = "zeros/zeros_t1e8.txt"
        
        # Start monitoring
        start_time = time.time()
        start_memory = self.process.memory_info().rss / 1024 / 1024
        memory_samples = []
        
        try:
            # Computation with memory monitoring
            print("  🧮 Computing arithmetic side...")
            mem_before = self.process.memory_info().rss / 1024 / 1024
            prime_part = prime_sum(f, P, K)
            arch_part = archimedean_sum(f, sigma0, T, lim_u)
            arithmetic_result = prime_part + arch_part
            mem_after_arith = self.process.memory_info().rss / 1024 / 1024
            memory_samples.append(mem_after_arith)
            
            print("  🔢 Computing zero side...")
            if os.path.exists(zeros_file):
                zero_result = zero_sum_limited(f, zeros_file, max_zeros, lim_u)
            else:
                print("  ⚠️ Zeros file not found, using approximate zeros")
                # Use approximate zeros for testing
                approx_zeros = [14.134725 + i * 2.5 for i in range(max_zeros)]
                zero_result = sum(f(mp.mpc(0, rho)) for rho in approx_zeros[:10])  # Limit for speed
            
            mem_after_zeros = self.process.memory_info().rss / 1024 / 1024
            memory_samples.append(mem_after_zeros)
            
        except Exception as e:
            print(f"  ❌ Benchmark failed: {e}")
            return None
        
        # Calculate metrics
        end_time = time.time()
        execution_time = end_time - start_time
        
        absolute_error = abs(arithmetic_result - zero_result)
        relative_error = absolute_error / abs(arithmetic_result) if abs(arithmetic_result) > 0 else float('inf')
        
        memory_peak = max(memory_samples) if memory_samples else start_memory
        memory_average = sum(memory_samples) / len(memory_samples) if memory_samples else start_memory
        
        print(f"  ⏱️ Time: {execution_time:.2f}s")
        print(f"  💾 Memory peak: {memory_peak - self.baseline_memory:.1f}MB")
        print(f"  📏 Relative error: {float(relative_error):.2e}")
        
        # Create metrics object
        metrics = PerformanceMetrics(
            timestamp=datetime.datetime.now().isoformat(),
            test_name=test_name,
            parameters=params,
            execution_time=execution_time,
            memory_peak_mb=memory_peak - self.baseline_memory,
            memory_average_mb=memory_average - self.baseline_memory,
            arithmetic_result=str(arithmetic_result),
            zero_result=str(zero_result),
            absolute_error=str(absolute_error),
            relative_error=str(relative_error)
        )
        
        return metrics
    
    def run_benchmark_suite(self) -> List[PerformanceMetrics]:
        """Run comprehensive benchmark suite."""
        print("🚀 Starting comprehensive benchmark suite...")
        
        benchmark_configs = [
            {
                "name": "quick_test",
                "params": {"max_primes": 50, "max_zeros": 50, "precision_dps": 15, "integration_t": 5}
            },
            {
                "name": "standard_ci",
                "params": {"max_primes": 100, "max_zeros": 100, "precision_dps": 25, "integration_t": 10}
            },
            {
                "name": "medium_precision",
                "params": {"max_primes": 200, "max_zeros": 200, "precision_dps": 30, "integration_t": 20}
            },
            {
                "name": "high_accuracy",
                "params": {"max_primes": 500, "max_zeros": 500, "precision_dps": 40, "integration_t": 50}
            }
        ]
        
        results = []
        for config in benchmark_configs:
            try:
                metrics = self.benchmark_validation(config["name"], config["params"])
                if metrics:
                    results.append(metrics)
                    # Small delay between tests
                    time.sleep(1)
            except KeyboardInterrupt:
                print("\n⏹️ Benchmark interrupted by user")
                break
            except Exception as e:
                print(f"❌ Benchmark {config['name']} failed: {e}")
                continue
        
        return results
    
    def save_results(self, results: List[PerformanceMetrics], suffix: str = ""):
        """Save benchmark results to JSON file."""
        timestamp = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
        filename = f"benchmark_results_{timestamp}{suffix}.json"
        filepath = os.path.join(self.output_dir, filename)
        
        # Convert results to serializable format
        data = {
            "metadata": {
                "timestamp": datetime.datetime.now().isoformat(),
                "python_version": sys.version,
                "platform": sys.platform,
                "cpu_count": os.cpu_count(),
                "total_memory_gb": psutil.virtual_memory().total / (1024**3)
            },
            "results": [asdict(result) for result in results]
        }
        
        try:
            with open(filepath, 'w') as f:
                json.dump(data, f, indent=2)
            
            print(f"📊 Benchmark results saved: {filepath}")
            return filepath
        except Exception as e:
            print(f"❌ Failed to save results: {e}")
            return None
    
    def generate_report(self, results: List[PerformanceMetrics]) -> str:
        """Generate human-readable performance report."""
        if not results:
            return "No benchmark results available."
        
        report_lines = [
            "# 🧮 Riemann-Adelic Performance Report",
            f"Generated: {datetime.datetime.now().strftime('%Y-%m-%d %H:%M:%S')}",
            "",
            "## 📊 Benchmark Summary",
            ""
        ]
        
        # Summary table
        report_lines.append("| Test Name | Execution Time | Memory Peak | Relative Error |")
        report_lines.append("|-----------|----------------|-------------|----------------|")
        
        for result in results:
            report_lines.append(
                f"| {result.test_name} | {result.execution_time:.2f}s | "
                f"{result.memory_peak_mb:.1f}MB | {float(result.relative_error):.2e} |"
            )
        
        report_lines.extend([
            "",
            "## 🎯 Performance Analysis",
            ""
        ])
        
        # Analysis
        execution_times = [r.execution_time for r in results]
        memory_peaks = [r.memory_peak_mb for r in results]
        errors = [float(r.relative_error) for r in results if float(r.relative_error) != float('inf')]
        
        if execution_times:
            report_lines.extend([
                f"- **Fastest execution:** {min(execution_times):.2f}s",
                f"- **Slowest execution:** {max(execution_times):.2f}s",
                f"- **Average execution time:** {sum(execution_times)/len(execution_times):.2f}s"
            ])
        
        if memory_peaks:
            report_lines.extend([
                f"- **Peak memory usage:** {max(memory_peaks):.1f}MB",
                f"- **Average memory usage:** {sum(memory_peaks)/len(memory_peaks):.1f}MB"
            ])
        
        if errors:
            report_lines.extend([
                f"- **Best accuracy:** {min(errors):.2e} relative error",
                f"- **Worst accuracy:** {max(errors):.2e} relative error"
            ])
        
        report_lines.extend([
            "",
            "## 💡 Recommendations",
            "",
            "- For **CI/CD**: Use `standard_ci` parameters for good balance of speed vs accuracy",
            "- For **research**: Use `high_accuracy` parameters for publication-quality results", 
            "- For **development**: Use `quick_test` parameters for rapid iteration",
            "",
            "## 🔧 Parameter Optimization",
            ""
        ])
        
        # Find optimal parameters
        if len(results) > 1:
            # Find best speed/accuracy tradeoff
            scores = []
            for r in results:
                error = float(r.relative_error)
                if error != float('inf') and error > 0:
                    # Score = 1 / (time * log10(error))
                    score = 1.0 / (r.execution_time * abs(mp.log10(error)))
                    scores.append((r.test_name, score))
            
            if scores:
                best_config = max(scores, key=lambda x: x[1])
                report_lines.append(f"**Recommended configuration:** `{best_config[0]}` (best speed/accuracy balance)")
        
        return "\n".join(report_lines)

def profile_validation_script():
    """Profile the main validation script using cProfile."""
    print("🔍 Profiling main validation script...")
    
    try:
        import cProfile
        import pstats
        import io
        
        # Create a temporary profile file
        with tempfile.NamedTemporaryFile(suffix='.prof', delete=False) as f:
            profile_file = f.name
        
        # Run validation with profiling
        cmd = [
            sys.executable, '-m', 'cProfile', '-o', profile_file,
            'validate_explicit_formula.py',
            '--max_primes', '100', '--max_zeros', '100', '--precision_dps', '15'
        ]
        
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=120)
        
        if result.returncode == 0:
            # Load and analyze profile
            stats = pstats.Stats(profile_file)
            stats.sort_stats('cumulative')
            
            # Capture profile output
            s = io.StringIO()
            stats.print_stats(20)  # Top 20 functions
            profile_output = s.getvalue()
            
            print("📊 Profiling Results (Top 20 functions):")
            print(profile_output)
            
            # Save profile report
            os.makedirs('logs/profiling', exist_ok=True)
            report_file = f"logs/profiling/profile_report_{datetime.datetime.now().strftime('%Y%m%d_%H%M%S')}.txt"
            
            with open(report_file, 'w') as f:
                f.write("# Riemann-Adelic Validation Profile Report\n\n")
                f.write(f"Generated: {datetime.datetime.now()}\n\n")
                f.write("## Command executed:\n")
                f.write(" ".join(cmd) + "\n\n")
                f.write("## Profile results:\n")
                f.write(profile_output)
            
            print(f"📁 Profile report saved: {report_file}")
            
        else:
            print(f"❌ Profiling failed: {result.stderr}")
        
        # Clean up
        if os.path.exists(profile_file):
            os.remove(profile_file)
            
    except Exception as e:
        print(f"❌ Profiling error: {e}")

def main():
    """Main performance monitoring interface."""
    import argparse
    
    parser = argparse.ArgumentParser(description='Performance monitoring for Riemann-Adelic validation')
    parser.add_argument('--benchmark', action='store_true', help='Run benchmark suite')
    parser.add_argument('--profile', action='store_true', help='Profile validation script')
    parser.add_argument('--quick', action='store_true', help='Run only quick benchmarks')
    parser.add_argument('--report', type=str, help='Generate report from existing results file')
    parser.add_argument('--output-dir', default='logs/performance', help='Output directory for results')
    
    args = parser.parse_args()
    
    if args.report:
        try:
            with open(args.report, 'r') as f:
                data = json.load(f)
            
            # Convert back to PerformanceMetrics objects
            results = [PerformanceMetrics(**result_data) for result_data in data['results']]
            monitor = PerformanceMonitor(args.output_dir)
            report = monitor.generate_report(results)
            
            print(report)
            
            # Save report
            report_file = args.report.replace('.json', '_report.md')
            with open(report_file, 'w') as f:
                f.write(report)
            print(f"\n📄 Report saved: {report_file}")
            
        except Exception as e:
            print(f"❌ Error generating report: {e}")
            return 1
    
    monitor = PerformanceMonitor(args.output_dir)
    
    if args.profile:
        profile_validation_script()
    
    if args.benchmark or args.quick:
        if args.quick:
            # Run only quick benchmarks
            quick_config = {
                "name": "quick_test",
                "params": {"max_primes": 50, "max_zeros": 50, "precision_dps": 15, "integration_t": 5}
            }
            metrics = monitor.benchmark_validation(quick_config["name"], quick_config["params"])
            results = [metrics] if metrics else []
        else:
            results = monitor.run_benchmark_suite()
        
        if results:
            # Save results
            results_file = monitor.save_results(results)
            
            # Generate and display report
            report = monitor.generate_report(results)
            print("\n" + "="*80)
            print(report)
            print("="*80)
            
            # Save report
            if results_file:
                report_file = results_file.replace('.json', '_report.md')
                with open(report_file, 'w') as f:
                    f.write(report)
                print(f"\n📄 Report saved: {report_file}")
        else:
            print("❌ No benchmark results collected")
            return 1
    
    if not any([args.benchmark, args.profile, args.quick, args.report]):
        print("🔧 No action specified. Use --help for options.")
        parser.print_help()
        return 1
    
    return 0

if __name__ == "__main__":
    sys.exit(main())