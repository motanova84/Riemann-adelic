#!/usr/bin/env python3
"""
Riemann Hypothesis Demonstration Protocol

Implements the 4-stage protocol for demonstrating RH as a coherence condition:
    1. Input: Select region in complex plane
    2. Processing: Calculate Ψ(s) for all points
    3. Criteria: Apply resonance threshold Ψ(s) ≥ threshold
    4. Result: Verify all resonant points have Re(s) = 1/2

Reformulation:
    RH is true ⟺ Ψ(s) = 1 only when Re(s) = 1/2
"""

from typing import Dict, List, Tuple
import sys

try:
    import numpy as np
except ImportError as e:
    print(f"Error: Required module not found: {e}")
    print("Please install: pip install numpy")
    sys.exit(1)

# Import from local modules
try:
    from .zeta_coherence import ZetaCoherence
except ImportError:
    # Fallback for standalone execution
    import os
    sys.path.insert(0, os.path.dirname(__file__))
    from zeta_coherence import ZetaCoherence


class RiemannProver:
    """
    Protocol for demonstrating the Riemann Hypothesis through coherence.
    
    Attributes:
        coherence_calculator (ZetaCoherence): Coherence function calculator
        coherence_threshold (float): Threshold for perfect resonance
    """
    
    def __init__(self, coherence_threshold: float = 0.999999):
        """
        Initialize the prover.
        
        Args:
            coherence_threshold: Minimum Ψ(s) for resonance detection
        """
        self.coherence_calculator = ZetaCoherence(precision=30)
        self.coherence_threshold = coherence_threshold
    
    def stage1_input(self, sigma_range: Tuple[float, float],
                    t_range: Tuple[float, float]) -> Dict[str, any]:
        """
        Stage 1: Define input region in complex plane.
        
        Args:
            sigma_range: (min, max) for real part
            t_range: (min, max) for imaginary part
            
        Returns:
            Region specification
        """
        return {
            "sigma": {"min": sigma_range[0], "max": sigma_range[1]},
            "t": {"min": t_range[0], "max": t_range[1]},
            "description": f"Region: σ ∈ [{sigma_range[0]}, {sigma_range[1]}], "
                          f"t ∈ [{t_range[0]}, {t_range[1]}]"
        }
    
    def stage2_processing(self, region: Dict[str, any],
                         resolution: int = 100) -> Dict[str, any]:
        """
        Stage 2: Process region by calculating Ψ(s).
        
        Args:
            region: Region from stage 1
            resolution: Grid resolution
            
        Returns:
            Processing results with Ψ values
        """
        sigma_min = region["sigma"]["min"]
        sigma_max = region["sigma"]["max"]
        t_min = region["t"]["min"]
        t_max = region["t"]["max"]
        
        sigmas = np.linspace(sigma_min, sigma_max, resolution)
        ts = np.linspace(t_min, t_max, resolution)
        
        psi_values = []
        points = []
        
        for sigma in sigmas:
            for t in ts:
                s = complex(sigma, t)
                result = self.coherence_calculator.calculate_psi(s)
                psi_values.append(result["psi"])
                points.append(s)
        
        return {
            "points": points,
            "psi_values": psi_values,
            "grid_size": resolution,
            "total_points": len(points)
        }
    
    def stage3_criteria(self, processing_results: Dict[str, any]) -> Dict[str, any]:
        """
        Stage 3: Apply resonance criteria.
        
        Args:
            processing_results: Results from stage 2
            
        Returns:
            Points meeting resonance criteria
        """
        points = processing_results["points"]
        psi_values = processing_results["psi_values"]
        
        resonant_points = []
        resonant_psi = []
        
        for point, psi in zip(points, psi_values):
            if psi >= self.coherence_threshold:
                resonant_points.append(point)
                resonant_psi.append(psi)
        
        return {
            "resonant_points": resonant_points,
            "resonant_psi": resonant_psi,
            "resonance_count": len(resonant_points),
            "threshold": self.coherence_threshold
        }
    
    def stage4_result(self, criteria_results: Dict[str, any]) -> Dict[str, any]:
        """
        Stage 4: Verify RH condition.
        
        Check that all resonant points have Re(s) = 1/2.
        
        Args:
            criteria_results: Results from stage 3
            
        Returns:
            Verification results
        """
        resonant_points = criteria_results["resonant_points"]
        
        on_critical_line = []
        deviations = []
        
        for point in resonant_points:
            sigma = point.real
            deviation = abs(sigma - 0.5)
            on_line = deviation < 1e-4  # Tolerance for numerical precision
            
            on_critical_line.append(on_line)
            deviations.append(deviation)
        
        all_on_line = all(on_critical_line)
        
        return {
            "all_on_critical_line": all_on_line,
            "on_critical_count": sum(on_critical_line),
            "off_critical_count": len(on_critical_line) - sum(on_critical_line),
            "max_deviation": max(deviations) if deviations else 0,
            "mean_deviation": np.mean(deviations) if deviations else 0,
            "rh_validated": all_on_line,
            "conclusion": "RH validated in region" if all_on_line 
                         else "RH violation detected"
        }
    
    def run_protocol(self, sigma_range: Tuple[float, float],
                    t_range: Tuple[float, float],
                    resolution: int = 100) -> Dict[str, any]:
        """
        Run the complete 4-stage protocol.
        
        Args:
            sigma_range: (min, max) for real part
            t_range: (min, max) for imaginary part  
            resolution: Grid resolution
            
        Returns:
            Complete protocol results
        """
        # Stage 1
        region = self.stage1_input(sigma_range, t_range)
        
        # Stage 2
        processing = self.stage2_processing(region, resolution)
        
        # Stage 3
        criteria = self.stage3_criteria(processing)
        
        # Stage 4
        result = self.stage4_result(criteria)
        
        return {
            "stage1_input": region,
            "stage2_processing": {
                "total_points": processing["total_points"],
                "grid_size": processing["grid_size"]
            },
            "stage3_criteria": {
                "resonance_count": criteria["resonance_count"],
                "threshold": criteria["threshold"]
            },
            "stage4_result": result
        }


def main():
    """Demonstration of RH protocol."""
    import argparse
    
    parser = argparse.ArgumentParser(
        description="Riemann Hypothesis Demonstration Protocol"
    )
    parser.add_argument("--sigma-min", type=float, default=0.49,
                       help="Minimum real part")
    parser.add_argument("--sigma-max", type=float, default=0.51,
                       help="Maximum real part")
    parser.add_argument("--t-min", type=float, default=14.0,
                       help="Minimum imaginary part")
    parser.add_argument("--t-max", type=float, default=15.0,
                       help="Maximum imaginary part")
    parser.add_argument("--resolution", type=int, default=50,
                       help="Grid resolution")
    
    args = parser.parse_args()
    
    print("=" * 70)
    print("RIEMANN HYPOTHESIS DEMONSTRATION PROTOCOL")
    print("=" * 70)
    print()
    
    prover = RiemannProver(coherence_threshold=0.999999)
    
    print(f"Region: σ ∈ [{args.sigma_min}, {args.sigma_max}], "
          f"t ∈ [{args.t_min}, {args.t_max}]")
    print(f"Resolution: {args.resolution}×{args.resolution}")
    print(f"Threshold: Ψ(s) ≥ {prover.coherence_threshold}")
    print()
    
    print("Running protocol...")
    results = prover.run_protocol(
        (args.sigma_min, args.sigma_max),
        (args.t_min, args.t_max),
        args.resolution
    )
    
    print()
    print("RESULTS:")
    print(f"  Stage 1 - Input: {results['stage1_input']['description']}")
    print(f"  Stage 2 - Processing: {results['stage2_processing']['total_points']} points")
    print(f"  Stage 3 - Criteria: {results['stage3_criteria']['resonance_count']} resonant points")
    print(f"  Stage 4 - Result: {results['stage4_result']['conclusion']}")
    print()
    
    if results['stage4_result']['rh_validated']:
        print("✅ RH VALIDATED: All resonant points on critical line Re(s) = 1/2")
    else:
        print("❌ RH VIOLATION: Some resonant points off critical line")
    
    print()
    print("=" * 70)
    print("Reformulation: RH ⟺ [Ψ(s) = 1 ⟺ Re(s) = 1/2]")
    print("=" * 70)


if __name__ == "__main__":
    main()
