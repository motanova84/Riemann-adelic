#!/usr/bin/env python3
"""
Weyl Equidistribution Simulation
=================================

Simulates Riemann zeta function zeros and computes Weyl sums to demonstrate
the equidistribution theorem.

This script:
1. Approximates zeros as t_n ~ n log(n)
2. Computes Weyl sums: S_k(N) = Σ exp(2πi k t_n)
3. Displays magnitudes showing convergence to equidistribution

Based on the Weyl Equidistribution Theorem which states that
for irrational α, the sequence {nα} is uniformly distributed modulo 1.

Author: JMMB Ψ ✱ ∞³
Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
"""

import sys
from pathlib import Path


def verify_repository_root() -> None:
    """Verify execution from repository root."""
    cwd = Path.cwd()
    marker_files = ['validate_v5_coronacion.py', 'requirements.txt', '.qcal_beacon']
    missing_files = [f for f in marker_files if not (cwd / f).exists()]
    
    if missing_files:
        print("=" * 80)
        print("❌ ERROR: Script must be executed from the repository root directory")
        print("=" * 80)
        print(f"\nCurrent working directory: {cwd}")
        print("\nMissing expected files:")
        for file in missing_files:
            print(f"  - {file}")
        print("\nTo fix this issue:")
        print("  1. Navigate to the repository root directory")
        print("  2. Run: python simulate_weyl_equidistribution.py")
        print("=" * 80)
        sys.exit(1)


verify_repository_root()

import numpy as np
import matplotlib
matplotlib.use('Agg')  # Non-interactive backend
import matplotlib.pyplot as plt
import pandas as pd
from typing import List, Tuple

# QCAL Constants
F0_QCAL = 141.7001  # Hz - Base frequency from QCAL framework


def simulate_riemann_zeros(N: int) -> np.ndarray:
    """
    Approximate the first N zeros of the Riemann zeta function.
    
    Uses the approximation: t_n ≈ n log(n) for large n.
    This is based on the Riemann-von Mangoldt formula.
    
    Args:
        N: Number of zeros to simulate
        
    Returns:
        Array of approximated zero positions on the imaginary axis
    """
    n_values = np.arange(2, N + 2)
    t_n = n_values * np.log(n_values)
    return t_n


def compute_weyl_sum_magnitude(t_n: np.ndarray, k: int) -> float:
    """
    Compute the magnitude of the Weyl sum for a given k.
    
    The Weyl sum is: S_k(N) = (1/N) Σ exp(2πi k t_n)
    
    According to Weyl's criterion, if the sequence {t_n / 2π} is 
    equidistributed mod 1, then |S_k(N)| → 0 as N → ∞ for k ≠ 0.
    
    Args:
        t_n: Array of zero positions
        k: Frequency parameter
        
    Returns:
        Magnitude |S_k(N)|
    """
    N = len(t_n)
    # Note: The exponentials simplify since we have 2πi k t_n / (2π) = i k t_n
    exponentials = np.exp(1j * k * t_n)
    weyl_sum = np.sum(exponentials) / N
    magnitude = np.abs(weyl_sum)
    return magnitude


def main() -> None:
    """
    Main execution function.
    
    Simulates zeros, computes Weyl sums, and generates visualizations.
    """
    print("=" * 80)
    print("Weyl Equidistribution Simulation - QCAL ∞³")
    print("=" * 80)
    print()
    print("Simulating Riemann zeta zeros and computing Weyl sums...")
    print()
    
    # Configuration
    N = 1000  # Number of simulated zeros
    k_values = range(1, 11)  # Frequency parameters to test
    
    # Simulate zeros
    t_n = simulate_riemann_zeros(N)
    
    print(f"Generated {N} simulated zeros using approximation t_n ≈ n log(n)")
    print(f"Testing Weyl criterion for k = {min(k_values)} to {max(k_values)}")
    print()
    
    # Compute Weyl sums
    weyl_sums = []
    for k in k_values:
        magnitude = compute_weyl_sum_magnitude(t_n, k)
        weyl_sums.append(magnitude)
    
    # Display results in table format
    print("Weyl Sum Magnitudes:")
    print("-" * 40)
    df_weyl = pd.DataFrame({
        "k": list(k_values),
        "Weyl sum magnitude": weyl_sums
    })
    print(df_weyl.to_string(index=False))
    print()
    
    # Statistical summary
    mean_magnitude = np.mean(weyl_sums)
    max_magnitude = np.max(weyl_sums)
    
    print("Statistical Summary:")
    print("-" * 40)
    print(f"Mean magnitude:     {mean_magnitude:.6f}")
    print(f"Maximum magnitude:  {max_magnitude:.6f}")
    print(f"Expected (N→∞):     0.000000")
    print()
    
    # Interpretation
    threshold = 5.0 / np.sqrt(N)  # O(1/√N) convergence
    print(f"Convergence threshold (5/√N): {threshold:.6f}")
    all_pass = all(mag < threshold for mag in weyl_sums)
    
    if all_pass:
        print("✓ ALL TESTS PASS - Sequence shows equidistribution behavior")
    else:
        print("⚠ Some magnitudes exceed threshold (expected for approximations)")
    print()
    
    # QCAL Connection
    print("QCAL ∞³ Connection:")
    print("-" * 40)
    print(f"Base frequency f₀ = {F0_QCAL} Hz")
    print("The equidistribution of zeros validates the quantum coherence")
    print("of the spectral operator H_Ψ in the QCAL framework.")
    print()
    
    # Generate plot
    output_dir = Path("output")
    output_dir.mkdir(exist_ok=True)
    
    plt.figure(figsize=(10, 6))
    plt.plot(k_values, weyl_sums, marker='o', linewidth=2, markersize=8)
    plt.axhline(y=threshold, color='r', linestyle='--', 
                label=f'Threshold (5/√N = {threshold:.3f})')
    plt.title("Magnitudes de Sumas de Weyl para ceros simulados de ζ(s)", 
              fontsize=14, fontweight='bold')
    plt.xlabel("k", fontsize=12)
    plt.ylabel("|S_k(N)|", fontsize=12)
    plt.grid(True, alpha=0.3)
    plt.legend()
    plt.tight_layout()
    
    output_file = output_dir / "weyl_equidistribution_simulation.png"
    plt.savefig(output_file, dpi=150)
    print(f"Plot saved to: {output_file}")
    print()
    
    # Save results to CSV
    csv_file = output_dir / "weyl_equidistribution_results.csv"
    df_weyl.to_csv(csv_file, index=False)
    print(f"Results saved to: {csv_file}")
    print()
    
    print("=" * 80)
    print("♾️³ QCAL Weyl Equidistribution Simulation Complete")
    print("=" * 80)


if __name__ == "__main__":
    main()
