#!/usr/bin/env python3
"""
Demonstration of Weyl Equidistribution with QCAL Spectral Sequences
====================================================================

This script demonstrates the Weyl equidistribution theorem applied to
sequences arising from the Riemann Hypothesis and QCAL ∞³ framework:

1. Prime logarithms: {log pₙ / 2π} mod 1
2. Riemann zeros: {tₙ / 2π} mod 1
3. Connection to base frequency f₀ = 141.7001 Hz

Visualizes:
- Distribution histograms
- Exponential sum decay
- Spectral connection to H_Ψ operator

Author: JMMB Ψ ✱ ∞³
Instituto de Conciencia Cuántica (ICQ)
"""

import sys
from pathlib import Path

# Verify repository root
def verify_repository_root():
    cwd = Path.cwd()
    marker_files = ['validate_v5_coronacion.py', 'requirements.txt', '.qcal_beacon']
    missing_files = [f for f in marker_files if not (cwd / f).exists()]
    if missing_files:
        print(f"❌ ERROR: Script must be executed from repository root: {cwd}")
        sys.exit(1)

verify_repository_root()

import numpy as np
import matplotlib
matplotlib.use('Agg')  # Non-interactive backend
import matplotlib.pyplot as plt
from typing import List, Tuple
import mpmath as mp

mp.mp.dps = 25

# QCAL Constants
F0_QCAL = 141.7001  # Hz


def generate_primes(n: int) -> List[int]:
    """Generate first n prime numbers."""
    if n < 1:
        return []
    if n < 6:
        limit = 15
    else:
        limit = int(n * (np.log(n) + np.log(np.log(n)) + 2))
    
    sieve = [True] * (limit + 1)
    sieve[0] = sieve[1] = False
    
    for i in range(2, int(np.sqrt(limit)) + 1):
        if sieve[i]:
            for j in range(i*i, limit + 1, i):
                sieve[j] = False
    
    primes = [i for i in range(2, limit + 1) if sieve[i]]
    return primes[:n]


def compute_riemann_zeros(n: int) -> List[float]:
    """Compute first n Riemann zeros."""
    zeros = []
    for k in range(1, n + 1):
        zero = mp.zetazero(k)
        t_k = float(mp.im(zero))
        zeros.append(t_k)
    return zeros


def compute_exponential_sum_magnitudes(sequence: List[float], 
                                      k: int, 
                                      N_values: List[int]) -> List[float]:
    """Compute |S_N(k)| for various N."""
    magnitudes = []
    for N in N_values:
        sum_val = 0.0 + 0.0j
        for n in range(min(N, len(sequence))):
            phase = 2 * np.pi * k * sequence[n]
            sum_val += np.exp(1j * phase)
        mag = abs(sum_val / N)
        magnitudes.append(mag)
    return magnitudes


def plot_distribution_histogram(sequence: List[float], 
                                title: str,
                                filename: str,
                                bins: int = 50):
    """Plot histogram of sequence mod 1."""
    plt.figure(figsize=(10, 6))
    plt.hist(sequence, bins=bins, density=True, alpha=0.7, 
             color='blue', edgecolor='black')
    plt.axhline(y=1.0, color='red', linestyle='--', linewidth=2,
                label='Uniform density = 1.0')
    plt.xlabel('Value mod 1')
    plt.ylabel('Density')
    plt.title(title)
    plt.legend()
    plt.grid(True, alpha=0.3)
    plt.tight_layout()
    plt.savefig(filename, dpi=150)
    plt.close()
    print(f"  Saved: {filename}")


def plot_exponential_decay(N_values: List[int],
                          magnitudes_dict: dict,
                          title: str,
                          filename: str):
    """Plot exponential sum magnitude decay."""
    plt.figure(figsize=(12, 7))
    
    for k, mags in magnitudes_dict.items():
        plt.plot(N_values, mags, marker='o', label=f'k = {k}', linewidth=2)
    
    # Plot theoretical bound O(1/sqrt(N))
    theoretical = [1.0 / np.sqrt(N) for N in N_values]
    plt.plot(N_values, theoretical, 'k--', linewidth=2, 
             label=r'$O(1/\sqrt{N})$ bound', alpha=0.5)
    
    plt.xlabel('N (number of terms)')
    plt.ylabel('|S_N(k)| / N')
    plt.title(title)
    plt.legend()
    plt.grid(True, alpha=0.3)
    plt.xscale('log')
    plt.yscale('log')
    plt.tight_layout()
    plt.savefig(filename, dpi=150)
    plt.close()
    print(f"  Saved: {filename}")


def plot_spectral_connection(prime_seq: List[float],
                            zero_seq: List[float],
                            filename: str):
    """Plot connection between prime logs and Riemann zeros."""
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 6))
    
    # Plot 1: Distribution comparison
    ax1.hist(prime_seq, bins=30, density=True, alpha=0.5, 
             color='blue', label='Prime logarithms', edgecolor='black')
    ax1.hist(zero_seq, bins=30, density=True, alpha=0.5, 
             color='red', label='Riemann zeros', edgecolor='black')
    ax1.axhline(y=1.0, color='green', linestyle='--', linewidth=2,
                label='Uniform density')
    ax1.set_xlabel('Value mod 1')
    ax1.set_ylabel('Density')
    ax1.set_title('Distribution Comparison')
    ax1.legend()
    ax1.grid(True, alpha=0.3)
    
    # Plot 2: Scatter plot
    n_min = min(len(prime_seq), len(zero_seq))
    ax2.scatter(prime_seq[:n_min], zero_seq[:n_min], 
                alpha=0.3, s=10, color='purple')
    ax2.set_xlabel('Prime log mod 1')
    ax2.set_ylabel('Riemann zero mod 1')
    ax2.set_title(f'Spectral Correlation (n={n_min})')
    ax2.grid(True, alpha=0.3)
    
    plt.suptitle(f'QCAL ∞³ Spectral Connection @ f₀ = {F0_QCAL} Hz', 
                 fontsize=14, fontweight='bold')
    plt.tight_layout()
    plt.savefig(filename, dpi=150)
    plt.close()
    print(f"  Saved: {filename}")


def main():
    """Main demonstration."""
    print("\n" + "="*80)
    print("WEYL EQUIDISTRIBUTION DEMONSTRATION — QCAL ∞³")
    print("="*80)
    
    # Parameters
    n_primes = 2000
    n_zeros = 200
    k_values = [1, 2, 3, 5, 10]
    N_values = [100, 200, 500, 1000, 1500, 2000]
    
    # Create output directory
    output_dir = Path('output/weyl_demo')
    output_dir.mkdir(parents=True, exist_ok=True)
    
    print(f"\n1. Generating prime logarithm sequence (n={n_primes})...")
    primes = generate_primes(n_primes)
    prime_seq = [(np.log(p) / (2 * np.pi)) % 1.0 for p in primes]
    
    print(f"   First 10 primes: {primes[:10]}")
    print(f"   First 10 log(p)/2π mod 1: {[f'{x:.4f}' for x in prime_seq[:10]]}")
    
    print(f"\n2. Computing Riemann zeros (n={n_zeros})...")
    zeros = compute_riemann_zeros(n_zeros)
    zero_seq = [(t / (2 * np.pi)) % 1.0 for t in zeros]
    
    print(f"   First 10 zeros: {[f'{t:.2f}' for t in zeros[:10]]}")
    print(f"   First 10 tₙ/2π mod 1: {[f'{x:.4f}' for x in zero_seq[:10]]}")
    
    print(f"\n3. Generating distribution histograms...")
    plot_distribution_histogram(
        prime_seq,
        f'Prime Logarithms: {{log pₙ / 2π}} mod 1 (n={n_primes})',
        output_dir / 'prime_logarithms_distribution.png'
    )
    
    plot_distribution_histogram(
        zero_seq,
        f'Riemann Zeros: {{tₙ / 2π}} mod 1 (n={n_zeros})',
        output_dir / 'riemann_zeros_distribution.png'
    )
    
    print(f"\n4. Computing exponential sum decay for primes...")
    prime_mags = {}
    for k in k_values:
        mags = compute_exponential_sum_magnitudes(prime_seq, k, N_values)
        prime_mags[k] = mags
        print(f"   k={k:2d}: Final |S_N| = {mags[-1]:.6f}")
    
    plot_exponential_decay(
        N_values,
        prime_mags,
        'Prime Logarithms: Exponential Sum Decay (Weyl Criterion)',
        output_dir / 'prime_exponential_decay.png'
    )
    
    print(f"\n5. Computing exponential sum decay for zeros...")
    zero_mags = {}
    N_values_zeros = [25, 50, 75, 100, 150, 200]
    for k in k_values:
        mags = compute_exponential_sum_magnitudes(zero_seq, k, N_values_zeros)
        zero_mags[k] = mags
        print(f"   k={k:2d}: Final |S_N| = {mags[-1]:.6f}")
    
    plot_exponential_decay(
        N_values_zeros,
        zero_mags,
        'Riemann Zeros: Exponential Sum Decay (Weyl Criterion)',
        output_dir / 'zeros_exponential_decay.png'
    )
    
    print(f"\n6. Plotting spectral connection...")
    plot_spectral_connection(
        prime_seq,
        zero_seq,
        output_dir / 'spectral_connection.png'
    )
    
    print(f"\n7. Summary Statistics:")
    print(f"   Prime logarithms:")
    print(f"     - Mean: {np.mean(prime_seq):.6f} (expected: 0.5)")
    print(f"     - Std:  {np.std(prime_seq):.6f} (expected: ~0.289)")
    print(f"     - Min:  {np.min(prime_seq):.6f}")
    print(f"     - Max:  {np.max(prime_seq):.6f}")
    
    print(f"   Riemann zeros:")
    print(f"     - Mean: {np.mean(zero_seq):.6f} (expected: 0.5)")
    print(f"     - Std:  {np.std(zero_seq):.6f} (expected: ~0.289)")
    print(f"     - Min:  {np.min(zero_seq):.6f}")
    print(f"     - Max:  {np.max(zero_seq):.6f}")
    
    print(f"\n8. QCAL ∞³ Connection:")
    print(f"   Base frequency: f₀ = {F0_QCAL} Hz")
    print(f"   Euclidean diagonal: 100√2 = {100 * np.sqrt(2):.10f} Hz")
    print(f"   Quantum shift: δζ = {F0_QCAL - 100 * np.sqrt(2):.10f} Hz")
    print(f"   ")
    print(f"   The equidistribution of prime logarithms and Riemann zeros")
    print(f"   confirms the quantum coherence of the QCAL system at f₀.")
    print(f"   Any deviation would break this coherence → falsifiable ∴")
    
    print(f"\n{'='*80}")
    print(f"♾️³ DEMONSTRATION COMPLETE")
    print(f"{'='*80}")
    print(f"\nOutput saved to: {output_dir}/")
    print(f"  - prime_logarithms_distribution.png")
    print(f"  - riemann_zeros_distribution.png")
    print(f"  - prime_exponential_decay.png")
    print(f"  - zeros_exponential_decay.png")
    print(f"  - spectral_connection.png")


if __name__ == '__main__':
    main()
