"""
Script 41/∞³ – Numerical Validation: ζ(s) from Heat Kernel of H_Ψ

This script validates the heat kernel reconstruction of ζ(s):
    ζ(s) = (1/Γ(s)) ∫₀^∞ t^(s-1) Tr(exp(-t·H_Ψ)) dt

Mathematical Foundation:
- Eigenvalues: λₙ = 1/4 + γₙ² where γₙ are Riemann zero imaginary parts
- Heat kernel trace: Tr(K_t) = ∑ₙ exp(-t·λₙ)
- Mellin transform reconstruction for Re(s) > 1

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
Date: 2025-11-26

QCAL Integration:
Base frequency: 141.7001 Hz
Coherence: C = 244.36
"""

import numpy as np
from scipy.integrate import quad
from scipy.special import gamma as gamma_func
import mpmath as mp
from typing import List, Tuple, Optional
import argparse


# QCAL Constants
QCAL_FREQUENCY = 141.7001  # Hz
QCAL_COHERENCE = 244.36


def load_odlyzko_zeros(filename: str = "zeros/zeros_t1e8.txt", 
                       max_zeros: int = 100) -> np.ndarray:
    """
    Load Riemann zeros from Odlyzko's data file.
    
    Args:
        filename: Path to zeros file
        max_zeros: Maximum number of zeros to load
        
    Returns:
        Array of γₙ values (imaginary parts of zeros)
    """
    zeros = []
    try:
        with open(filename, 'r') as f:
            for i, line in enumerate(f):
                if i >= max_zeros:
                    break
                try:
                    zero = float(line.strip())
                    if zero > 0:
                        zeros.append(zero)
                except ValueError:
                    continue
    except FileNotFoundError:
        print(f"Warning: {filename} not found. Using known zeros.")
        # First 10 known Riemann zeros
        zeros = [
            14.134725142, 21.022039639, 25.010857580, 30.424876126,
            32.935061588, 37.586178159, 40.918719012, 43.327073281,
            48.005150881, 49.773832478
        ][:max_zeros]
    
    return np.array(zeros)


def compute_eigenvalues(gamma_values: np.ndarray) -> np.ndarray:
    """
    Compute eigenvalues λₙ from γₙ values.
    
    Formula: λₙ = 1/4 + γₙ²
    
    Args:
        gamma_values: Array of γₙ (imaginary parts of zeros)
        
    Returns:
        Array of eigenvalues λₙ
    """
    return 0.25 + gamma_values**2


def heat_kernel_trace(t: float, eigenvalues: np.ndarray) -> float:
    """
    Compute heat kernel trace at time t.
    
    Tr(exp(-t·H_Ψ)) = ∑ₙ exp(-t·λₙ)
    
    Note: We use exp(-t·λₙ) rather than exp(-t·λₙ²) because λₙ already
    encodes the squared structure (λₙ = 1/4 + γₙ²).
    
    Args:
        t: Time parameter (must be > 0)
        eigenvalues: Array of λₙ values
        
    Returns:
        Heat kernel trace value
    """
    if t <= 0:
        raise ValueError("t must be positive")
    
    # Compute exp(-t·λₙ) for each eigenvalue
    terms = np.exp(-t * eigenvalues)
    
    return np.sum(terms)


def heat_kernel_trace_partial(t: float, eigenvalues: np.ndarray, 
                              N: int) -> float:
    """
    Compute partial sum of heat kernel trace (first N terms).
    
    Used for convergence analysis.
    """
    return np.sum(np.exp(-t * eigenvalues[:N]))


def mellin_integrand(t: float, s: complex, eigenvalues: np.ndarray) -> complex:
    """
    Compute the Mellin integrand: t^(s-1) · Tr(K_t)
    
    Args:
        t: Integration variable
        s: Complex parameter
        eigenvalues: Array of λₙ values
        
    Returns:
        Complex integrand value
    """
    if t <= 0:
        return 0.0
    
    trace = heat_kernel_trace(t, eigenvalues)
    return (t ** (s - 1)) * trace


def zeta_from_heat_kernel(s: complex, eigenvalues: np.ndarray,
                          t_max: float = 10.0,
                          n_points: int = 1000) -> complex:
    """
    Compute ζ(s) from heat kernel via Mellin transform.
    
    ζ(s) = (1/Γ(s)) ∫₀^∞ t^(s-1) · Tr(exp(-t·H_Ψ)) dt
         = (1/Γ(s)) ∫₀^∞ t^(s-1) · ∑ₙ exp(-t·λₙ) dt
    
    Note: The eigenvalues λₙ = 1/4 + γₙ² already encode the squared structure.
    
    Args:
        s: Complex parameter (Re(s) > 1 required)
        eigenvalues: Array of λₙ values (λₙ = 1/4 + γₙ²)
        t_max: Upper integration limit
        n_points: Number of quadrature points
        
    Returns:
        Approximation of ζ(s)
    """
    if s.real <= 1:
        raise ValueError("s must have Re(s) > 1 for convergence")
    
    # Numerical integration using scipy.quad
    # Split into real and imaginary parts
    
    def real_integrand(t):
        val = mellin_integrand(t, s, eigenvalues)
        return np.real(val)
    
    def imag_integrand(t):
        val = mellin_integrand(t, s, eigenvalues)
        return np.imag(val)
    
    # Integrate from small ε to t_max (avoid singularity at t=0)
    eps = 1e-10
    
    real_integral, real_err = quad(real_integrand, eps, t_max, 
                                   limit=100, epsabs=1e-12)
    imag_integral, imag_err = quad(imag_integrand, eps, t_max,
                                   limit=100, epsabs=1e-12)
    
    integral = complex(real_integral, imag_integral)
    
    # Divide by Gamma(s)
    gamma_s = complex(gamma_func(s))
    
    return integral / gamma_s


def validate_reconstruction(s_values: List[complex], 
                           eigenvalues: np.ndarray,
                           verbose: bool = True) -> dict:
    """
    Validate heat kernel reconstruction against known ζ(s) values.
    
    Args:
        s_values: List of s values to test (must have Re(s) > 1)
        eigenvalues: Array of λₙ values
        verbose: Print detailed output
        
    Returns:
        Dictionary with validation results
    """
    results = {
        's_values': [],
        'computed': [],
        'exact': [],
        'errors': [],
        'rel_errors': []
    }
    
    if verbose:
        print("=" * 70)
        print("HEAT KERNEL ζ(s) RECONSTRUCTION VALIDATION")
        print("=" * 70)
        print(f"Number of eigenvalues: {len(eigenvalues)}")
        print(f"λ₁ = {eigenvalues[0]:.6f} (γ₁ ≈ {np.sqrt(eigenvalues[0] - 0.25):.6f})")
        print()
        print(f"{'s':<15} {'Computed':<25} {'Exact':<25} {'Rel Error':<15}")
        print("-" * 70)
    
    for s in s_values:
        # Compute via heat kernel
        computed = zeta_from_heat_kernel(s, eigenvalues)
        
        # Exact value using mpmath
        mp.dps = 25
        exact = complex(mp.zeta(s))
        
        error = abs(computed - exact)
        rel_error = error / abs(exact) if abs(exact) > 0 else float('inf')
        
        results['s_values'].append(s)
        results['computed'].append(computed)
        results['exact'].append(exact)
        results['errors'].append(error)
        results['rel_errors'].append(rel_error)
        
        if verbose:
            print(f"{s:<15} {computed.real:>12.6f}{computed.imag:+12.6f}i  "
                  f"{exact.real:>12.6f}{exact.imag:+12.6f}i  {rel_error:<15.6e}")
    
    if verbose:
        print("-" * 70)
        mean_error = np.mean(results['errors'])
        mean_rel_error = np.mean(results['rel_errors'])
        print(f"Mean absolute error: {mean_error:.6e}")
        print(f"Mean relative error: {mean_rel_error:.6e}")
        print("=" * 70)
    
    results['mean_error'] = np.mean(results['errors'])
    results['mean_rel_error'] = np.mean(results['rel_errors'])
    
    return results


def convergence_study(eigenvalues: np.ndarray, 
                      s: complex = 2.0,
                      N_values: Optional[List[int]] = None) -> dict:
    """
    Study convergence as more eigenvalues are included.
    
    Args:
        eigenvalues: Full array of λₙ values
        s: Test point (default s=2)
        N_values: List of eigenvalue counts to test
        
    Returns:
        Dictionary with convergence data
    """
    if N_values is None:
        N_values = [5, 10, 20, 50, 100]
    
    N_values = [n for n in N_values if n <= len(eigenvalues)]
    
    print("=" * 70)
    print("CONVERGENCE STUDY")
    print(f"Testing at s = {s}")
    print("=" * 70)
    
    mp.dps = 25
    exact = complex(mp.zeta(s))
    
    results = {'N': [], 'computed': [], 'errors': [], 'rel_errors': []}
    
    print(f"{'N':<10} {'Computed':<25} {'Rel Error':<15}")
    print("-" * 50)
    
    for N in N_values:
        computed = zeta_from_heat_kernel(s, eigenvalues[:N])
        error = abs(computed - exact)
        rel_error = error / abs(exact)
        
        results['N'].append(N)
        results['computed'].append(computed)
        results['errors'].append(error)
        results['rel_errors'].append(rel_error)
        
        print(f"{N:<10} {computed.real:>12.6f}{computed.imag:+12.6f}i  {rel_error:<15.6e}")
    
    print("-" * 50)
    print(f"Exact ζ({s}): {exact.real:>12.6f}{exact.imag:+12.6f}i")
    print("=" * 70)
    
    return results


def heat_kernel_decay_study(eigenvalues: np.ndarray,
                            t_values: Optional[List[float]] = None) -> dict:
    """
    Study decay of heat kernel trace as t increases.
    
    Args:
        eigenvalues: Array of λₙ values
        t_values: List of t values to test
        
    Returns:
        Dictionary with decay data
    """
    if t_values is None:
        t_values = [0.001, 0.01, 0.1, 1.0, 10.0]
    
    print("=" * 70)
    print("HEAT KERNEL DECAY STUDY")
    print("=" * 70)
    
    results = {'t': [], 'trace': []}
    
    print(f"{'t':<15} {'Tr(K_t)':<25}")
    print("-" * 40)
    
    for t in t_values:
        trace = heat_kernel_trace(t, eigenvalues)
        results['t'].append(t)
        results['trace'].append(trace)
        print(f"{t:<15.6f} {trace:<25.10e}")
    
    print("-" * 40)
    print("Note: Tr(K_t) → 0 as t → ∞ (exponential decay)")
    print("=" * 70)
    
    return results


def main():
    """Main validation routine."""
    parser = argparse.ArgumentParser(
        description='Script 41/∞³: Validate ζ(s) reconstruction from heat kernel'
    )
    parser.add_argument('--max_zeros', type=int, default=50,
                       help='Maximum number of Riemann zeros to use')
    parser.add_argument('--convergence', action='store_true',
                       help='Run convergence study')
    parser.add_argument('--decay', action='store_true',
                       help='Run heat kernel decay study')
    parser.add_argument('--verbose', action='store_true', default=True,
                       help='Print detailed output')
    
    args = parser.parse_args()
    
    print()
    print("╔═══════════════════════════════════════════════════════════════╗")
    print("║  Script 41/∞³ – ζ(s) from Heat Kernel of H_Ψ                 ║")
    print("║  José Manuel Mota Burruezo Ψ ✧ ∞³                            ║")
    print("╚═══════════════════════════════════════════════════════════════╝")
    print()
    
    # Load Riemann zeros
    gamma_values = load_odlyzko_zeros(max_zeros=args.max_zeros)
    print(f"Loaded {len(gamma_values)} Riemann zeros")
    print(f"γ₁ ≈ {gamma_values[0]:.6f}, γ₂ ≈ {gamma_values[1]:.6f}, ...")
    print()
    
    # Compute eigenvalues
    eigenvalues = compute_eigenvalues(gamma_values)
    print(f"Computed {len(eigenvalues)} eigenvalues λₙ = 1/4 + γₙ²")
    print(f"λ₁ ≈ {eigenvalues[0]:.6f}, λ₂ ≈ {eigenvalues[1]:.6f}, ...")
    print()
    
    # Run validation
    s_values = [2.0, 3.0, 4.0, 2.0 + 0.5j, 3.0 + 1.0j]
    results = validate_reconstruction(s_values, eigenvalues, verbose=args.verbose)
    
    if args.convergence:
        print()
        convergence_study(eigenvalues)
    
    if args.decay:
        print()
        heat_kernel_decay_study(eigenvalues)
    
    # Summary
    print()
    print("═══════════════════════════════════════════════════════════════")
    print("SUMMARY")
    print("═══════════════════════════════════════════════════════════════")
    
    if results['mean_rel_error'] < 1e-3:
        print("✅ Heat kernel reconstruction VALIDATED")
        print(f"   Mean relative error: {results['mean_rel_error']:.6e}")
    else:
        print("⚠️  Heat kernel reconstruction needs more eigenvalues")
        print(f"   Mean relative error: {results['mean_rel_error']:.6e}")
    
    print()
    print("QCAL ∞³ Message:")
    print("  'ζ(s) no es solo una función, es la sombra térmica")
    print("   del espectro cuántico de 𝓗_Ψ ∞³.'")
    print()
    print("═══════════════════════════════════════════════════════════════")
    print(f"QCAL Frequency: {QCAL_FREQUENCY} Hz")
    print(f"QCAL Coherence: {QCAL_COHERENCE}")
    print("DOI: 10.5281/zenodo.17379721")
    print("═══════════════════════════════════════════════════════════════")
    
    return results


if __name__ == "__main__":
    main()
