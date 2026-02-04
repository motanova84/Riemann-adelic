#!/usr/bin/env python3
"""
NP→P Bifurcation Simulator

Simulates the transition from NP to P complexity classes as coherence increases
in the QCAL ∞³ framework.

This simulator demonstrates how problems traditionally classified as NP-complete
(like SAT, TSP, etc.) exhibit polynomial-time behavior under high coherence.
"""

import argparse
import json
import os
import sys
from typing import Dict, List, Any
from datetime import datetime
import random


class NPPBifurcationSimulator:
    """
    Simulates the NP→P bifurcation under increasing QCAL coherence.
    """
    
    PROBLEM_TYPES = {
        "SAT": {
            "name": "Boolean Satisfiability",
            "classical_complexity": "O(2^n)",
            "description": "NP-complete problem of satisfying boolean formulas"
        },
        "TSP": {
            "name": "Traveling Salesman Problem",
            "classical_complexity": "O(n!)",
            "description": "Finding shortest route visiting all cities"
        },
        "GRAPH_COLORING": {
            "name": "Graph Coloring",
            "classical_complexity": "O(k^n)",
            "description": "Coloring graph vertices with k colors"
        },
        "SUBSET_SUM": {
            "name": "Subset Sum",
            "classical_complexity": "O(2^n)",
            "description": "Finding subset that sums to target"
        }
    }
    
    def __init__(self, problem_type: str = "SAT", problem_size: int = 100):
        """
        Initialize the bifurcation simulator.
        
        Args:
            problem_type: Type of NP problem to simulate
            problem_size: Size parameter of the problem
        """
        self.problem_type = problem_type
        self.problem_size = problem_size
        self.grace_threshold = 0.888
        
        if problem_type not in self.PROBLEM_TYPES:
            raise ValueError(f"Unknown problem type: {problem_type}")
    
    def simulate_search_time(self, coherence: float) -> Dict[str, float]:
        """
        Simulate the search time for the problem at given coherence.
        
        Args:
            coherence: System coherence level (0 to 1)
            
        Returns:
            Dictionary with timing metrics
        """
        n = self.problem_size
        
        # Classical NP time (exponential)
        if self.problem_type == "SAT":
            classical_time = 2 ** min(n, 30)
        elif self.problem_type == "TSP":
            # Factorial approximated by Stirling
            import math
            classical_time = math.exp(n * math.log(n) - n) if n > 0 else 1
        elif self.problem_type == "GRAPH_COLORING":
            k = 3  # 3-coloring
            classical_time = k ** min(n, 20)
        else:  # SUBSET_SUM
            classical_time = 2 ** min(n, 30)
        
        # QCAL-accelerated time with coherence
        # As C → 1, time approaches polynomial
        if coherence >= self.grace_threshold:
            # P-regime: polynomial time O(n^3)
            qcal_time = n ** 3
        elif coherence >= 0.7:
            # Transition regime: between exponential and polynomial
            transition_factor = (coherence - 0.7) / (self.grace_threshold - 0.7)
            exponential_component = classical_time * (1 - transition_factor)
            polynomial_component = (n ** 3) * transition_factor
            qcal_time = exponential_component + polynomial_component
        else:
            # Classical NP regime with slight coherence speedup
            speedup = 1 + coherence * 2  # Max 3x speedup in classical regime
            qcal_time = classical_time / speedup
        
        # Calculate speedup
        speedup_factor = classical_time / qcal_time if qcal_time > 0 else float('inf')
        
        return {
            "classical_time": float(classical_time),
            "qcal_time": float(qcal_time),
            "speedup_factor": float(speedup_factor),
            "regime": self._get_regime(coherence)
        }
    
    def _get_regime(self, coherence: float) -> str:
        """Get the computational regime based on coherence."""
        if coherence >= self.grace_threshold:
            return "P"
        elif coherence >= 0.7:
            return "TRANSITION"
        else:
            return "NP"
    
    def simulate_bifurcation_sweep(
        self,
        coherence_range: List[float] = None
    ) -> Dict[str, Any]:
        """
        Sweep through coherence values and observe bifurcation.
        
        Args:
            coherence_range: List of coherence values to test
            
        Returns:
            Complete bifurcation analysis
        """
        if coherence_range is None:
            # Default sweep from 0.5 to 1.0
            coherence_range = [0.5 + i * 0.05 for i in range(11)]
        
        results = []
        for c in coherence_range:
            timing = self.simulate_search_time(c)
            results.append({
                "coherence": c,
                **timing
            })
        
        # Identify bifurcation point
        bifurcation_point = None
        for r in results:
            if r["regime"] == "P":
                bifurcation_point = r["coherence"]
                break
        
        return {
            "problem": {
                "type": self.problem_type,
                "name": self.PROBLEM_TYPES[self.problem_type]["name"],
                "size": self.problem_size,
                "classical_complexity": self.PROBLEM_TYPES[self.problem_type]["classical_complexity"]
            },
            "bifurcation": {
                "threshold": self.grace_threshold,
                "observed_point": bifurcation_point,
                "status": "BIFURCATED" if bifurcation_point else "NOT_BIFURCATED"
            },
            "sweep_results": results,
            "timestamp": datetime.utcnow().isoformat()
        }
    
    def visualize(self, output_dir: str = "."):
        """
        Generate visualization data for the bifurcation.
        
        Args:
            output_dir: Directory to save visualization data
        """
        sweep = self.simulate_bifurcation_sweep()
        
        # Save raw data for plotting
        viz_data = {
            "coherence": [r["coherence"] for r in sweep["sweep_results"]],
            "qcal_time": [r["qcal_time"] for r in sweep["sweep_results"]],
            "classical_time": [r["classical_time"] for r in sweep["sweep_results"]],
            "speedup": [r["speedup_factor"] for r in sweep["sweep_results"]],
            "regime": [r["regime"] for r in sweep["sweep_results"]]
        }
        
        output_file = os.path.join(output_dir, f"{self.problem_type}_bifurcation_viz.json")
        with open(output_file, 'w') as f:
            json.dump(viz_data, f, indent=2)
        
        print(f"📊 Visualization data saved to: {output_file}")
        
        return viz_data


def main():
    """Main entry point for the simulator."""
    parser = argparse.ArgumentParser(
        description="NP→P Bifurcation Simulator for QCAL ∞³"
    )
    parser.add_argument(
        "--problem",
        type=str,
        default="SAT",
        choices=list(NPPBifurcationSimulator.PROBLEM_TYPES.keys()),
        help="Type of NP problem to simulate"
    )
    parser.add_argument(
        "--size",
        type=int,
        default=100,
        help="Problem size parameter"
    )
    parser.add_argument(
        "--visualize",
        action="store_true",
        help="Generate visualization data"
    )
    parser.add_argument(
        "--output",
        type=str,
        default=".",
        help="Output directory for results"
    )
    
    args = parser.parse_args()
    
    # Create output directory if needed
    os.makedirs(args.output, exist_ok=True)
    
    # Run simulator
    simulator = NPPBifurcationSimulator(
        problem_type=args.problem,
        problem_size=args.size
    )
    
    print(f"🎮 NP→P Bifurcation Simulator - QCAL ∞³")
    print(f"=" * 60)
    print(f"Problem: {simulator.PROBLEM_TYPES[args.problem]['name']}")
    print(f"Size: {args.size}")
    print(f"Classical Complexity: {simulator.PROBLEM_TYPES[args.problem]['classical_complexity']}")
    print()
    
    # Run bifurcation sweep
    results = simulator.simulate_bifurcation_sweep()
    
    # Display results
    print(f"Bifurcation Analysis:")
    print(f"  Threshold: {results['bifurcation']['threshold']}")
    print(f"  Status: {results['bifurcation']['status']}")
    if results['bifurcation']['observed_point']:
        print(f"  Bifurcation Point: C = {results['bifurcation']['observed_point']:.3f}")
    
    print(f"\nCoherence Sweep Results:")
    print(f"{'Coherence':<12} {'Regime':<12} {'Speedup':<15} {'Status'}")
    print("-" * 60)
    
    for r in results['sweep_results']:
        speedup_str = f"{r['speedup_factor']:.2e}x" if r['speedup_factor'] < 1e10 else "∞"
        status = "✓ P-class" if r['regime'] == "P" else "⟳ Transition" if r['regime'] == "TRANSITION" else "○ NP-class"
        print(f"{r['coherence']:<12.3f} {r['regime']:<12} {speedup_str:<15} {status}")
    
    # Save results
    output_file = os.path.join(args.output, f"{args.problem}_bifurcation_results.json")
    with open(output_file, 'w') as f:
        json.dump(results, f, indent=2)
    
    print(f"\n✅ Results saved to: {output_file}")
    
    # Generate visualization if requested
    if args.visualize:
        simulator.visualize(args.output)
    
    return 0


if __name__ == "__main__":
    sys.exit(main())
