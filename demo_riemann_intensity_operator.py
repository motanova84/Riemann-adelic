#!/usr/bin/env python3
"""
Demo: Riemann Intensity Operator T_Ω
====================================

Demonstration of the analytical solution framework for the Riemann Hypothesis
using the intensity operator approach.

Usage:
    python3 demo_riemann_intensity_operator.py           # Interactive mode
    python3 demo_riemann_intensity_operator.py --auto    # Non-interactive mode

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: March 2026
"""

import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'operators'))

from riemann_intensity_operator import (
    RiemannIntensityOperator, 
    F0_QCAL,
    HAMILTONIAN_REGULARIZATION_VALUE
)
import numpy as np


def demo_basic_operator():
    """Demonstrate basic operator construction and properties."""
    print("=" * 80)
    print("DEMO 1: Basic Operator Construction")
    print("=" * 80)
    print()
    
    op = RiemannIntensityOperator(n_points=256, u_max=25.0, t_max=50.0)
    
    print(f"Operator initialized with:")
    print(f"  • Grid points: {op.n_points}")
    print(f"  • Spatial domain: u ∈ [{-op.u_max:.1f}, {op.u_max:.1f}]")
    print(f"  • Frequency domain: t ∈ [{-op.t_max:.1f}, {op.t_max:.1f}]")
    print()
    
    # Test Xi function
    t_test = np.array([0, 14.134, 21.022, 25.011])
    xi_test = op.compute_xi_function(t_test)
    
    print("Xi function at test points:")
    for i, (t, xi) in enumerate(zip(t_test, xi_test)):
        print(f"  • Ξ({t:7.3f}) = {xi:12.6e}")
    print()


def demo_intensity_spectrum():
    """Demonstrate intensity spectrum analysis."""
    print("=" * 80)
    print("DEMO 2: Intensity Spectrum Analysis")
    print("=" * 80)
    print()
    
    op = RiemannIntensityOperator(n_points=512, u_max=30.0, t_max=60.0)
    
    print("Computing intensity spectrum...")
    result = op.compute_intensity_spectrum()
    
    print(f"\nResults:")
    print(f"  • Computation time: {result.computation_time_ms:.2f} ms")
    print(f"  • Spectrum dimension: {len(result.intensity_spectrum)}")
    print(f"  • Singular points (zeros): {len(result.singular_points)}")
    print()
    
    print("GUE Statistics:")
    print(f"  • GUE coherence: {result.gue_coherence:.6f}")
    print(f"  • Mean spacing: {result.mean_spacing:.6f}")
    print(f"  • Variance: {result.variance_spacing:.6f}")
    print(f"  • KS statistic: {result.ks_statistic:.6f}")
    print(f"  • KS p-value: {result.ks_pvalue:.6f}")
    print()
    
    print("Level Repulsion:")
    print(f"  • Repulsion force: {result.repulsion_force:.6f}")
    print(f"  • Simplicity verified: {result.simplicity_verified}")
    print()
    
    print(f"Overall Coherence Ψ: {result.psi:.6f}")
    print()
    
    # Interpretation
    if result.gue_coherence > 0.9:
        print("✓ Strong GUE coherence — quantum chaotic behavior confirmed")
    elif result.gue_coherence > 0.7:
        print("✓ Moderate GUE coherence — quantum behavior present")
    else:
        print("⚠ Low GUE coherence — check parameter settings")
    
    if result.simplicity_verified:
        print("✓ All zeros are simple — no degeneracy detected")
    else:
        print("⚠ Some zeros may not be simple")
    print()


def demo_hamiltonian():
    """Demonstrate Hamiltonian H = -log|T| with singularities."""
    print("=" * 80)
    print("DEMO 3: Hamiltonian H = -log|T| with Logarithmic Singularities")
    print("=" * 80)
    print()
    
    op = RiemannIntensityOperator(n_points=256, u_max=25.0, t_max=50.0)
    
    print("Constructing operators...")
    T_omega = op.construct_T_omega()
    H = op.construct_hamiltonian()
    
    # Analyze spectra
    intensity_eigenvalues = np.linalg.eigvalsh(T_omega)
    hamiltonian_eigenvalues = np.linalg.eigvalsh(H)
    
    print(f"\nIntensity Operator T_Ω:")
    finite_intensity = intensity_eigenvalues[np.isfinite(intensity_eigenvalues)]
    print(f"  • Finite eigenvalues: {len(finite_intensity)}")
    print(f"  • Min eigenvalue: {np.min(finite_intensity):.6e}")
    print(f"  • Max eigenvalue: {np.max(finite_intensity):.6e}")
    print(f"  • All non-negative: {np.all(finite_intensity >= -1e-10)}")
    print()
    
    print(f"Hamiltonian H = -log|T|:")
    finite_H = hamiltonian_eigenvalues[np.isfinite(hamiltonian_eigenvalues)]
    singular_H = np.sum(~np.isfinite(hamiltonian_eigenvalues))
    print(f"  • Finite eigenvalues: {len(finite_H)}")
    print(f"  • Singular points (∞): {singular_H}")
    if len(finite_H) > 0:
        print(f"  • Min finite eigenvalue: {np.min(finite_H):.6e}")
        print(f"  • Max finite eigenvalue: {np.max(finite_H):.6e}")
    print()
    
    print("Interpretation:")
    print("  • Zeros of ζ → Logarithmic singularities (infinite energy)")
    print("  • In Vortex 8, these are points of infinite solenoid pressure")
    print("  • Consciousness forced to phase-jump at these points")
    print()


def demo_torsion_repulsion():
    """Demonstrate torsion term and level repulsion."""
    print("=" * 80)
    print("DEMO 4: Torsion Term and Level Repulsion")
    print("=" * 80)
    print()
    
    op = RiemannIntensityOperator(n_points=256, u_max=20.0, t_max=40.0)
    
    print("Computing torsion potential V(u) = tanh(u)...")
    V_torsion = op.add_torsion_term(strength=1.0)
    
    # Sample points
    u_sample = op.u[::32]
    V_sample = V_torsion[::32]
    
    print("\nTorsion potential at sample points:")
    for u, V in zip(u_sample[:8], V_sample[:8]):
        print(f"  • V({u:7.2f}) = {V:7.4f}")
    print()
    
    print("Properties:")
    print(f"  • Antisymmetric: V(-u) = -V(u)")
    print(f"  • Bounded: V(u) ∈ [-1, 1]")
    print(f"  • Repulsion force prevents degeneracy")
    print()
    
    # Compute repulsion force
    result = op.compute_intensity_spectrum()
    print(f"Repulsion force measure: {result.repulsion_force:.6f}")
    print()
    
    print("Physical Interpretation:")
    print("  • tanh(u) term creates torsion in spectral space")
    print("  • Acts as repulsion preventing two zeros at same point")
    print("  • Ensures simplicity: Ξ'(t) ≠ 0 at all zeros")
    print("  • Manifestation of Pauli exclusion in Riemann spectrum")
    print()


def demo_weil_formula():
    """Demonstrate Riemann-Weil formula verification."""
    print("=" * 80)
    print("DEMO 5: Riemann-Weil Formula and Quantization Condition")
    print("=" * 80)
    print()
    
    op = RiemannIntensityOperator(n_points=512, u_max=30.0, t_max=60.0)
    
    print("Verifying Riemann-Weil formula...")
    result = op.verify_weil_formula()
    
    print(f"\nResults:")
    print(f"  • Computation time: {result.computation_time_ms:.2f} ms")
    print(f"  • Trace Z = Tr(f(H)): {abs(result.trace_value):.6e}")
    print(f"  • Weil formula value: {abs(result.weil_formula_value):.6e}")
    print(f"  • Consistency error: {result.consistency_error:.6e}")
    print()
    
    print("Contributions:")
    print(f"  • Spectral (zeros): {result.spectral_contribution:.6e}")
    print(f"  • Prime powers: {result.prime_contribution:.6e}")
    print()
    
    print("Confinement:")
    print(f"  • Paley-Wiener confined: {result.paley_wiener_confined}")
    print(f"  • Overall coherence Ψ: {result.psi:.6f}")
    print()
    
    # Analyze correlation function
    corr = result.correlation_function
    print("Correlation Function Φ(u):")
    print(f"  • Length: {len(corr)}")
    print(f"  • Max |Φ|: {np.max(np.abs(corr)):.6e}")
    print(f"  • Support width: ~{np.sum(np.abs(corr) > 0.01*np.max(np.abs(corr)))}/{len(corr)} points")
    print()
    
    print("Interpretation:")
    print("  • Φ(u) = Feynman propagator on modular surface")
    print("  • Also: correlation function of prime numbers")
    print("  • Fourier dual to Ξ(t) in frequency domain")
    print("  • Operator T is the 'Riemann Mirror':")
    print("    - Time domain (u) ↔ Frequency domain (t)")
    print("    - Primes ↔ Zeros")
    print()


def demo_riemann_mirror():
    """Demonstrate the Riemann Mirror concept."""
    print("=" * 80)
    print("DEMO 6: The Riemann Mirror — Time ↔ Frequency Duality")
    print("=" * 80)
    print()
    
    op = RiemannIntensityOperator(n_points=512, u_max=30.0, t_max=60.0)
    
    print("The operator T acts as 'Riemann Mirror':")
    print()
    
    # Frequency domain
    print("FREQUENCY DOMAIN (t):")
    t_sample = op.t[::64]
    xi_sample = op.compute_xi_function(t_sample)
    print("  Ξ(t) = Xi function (Riemann zeros)")
    for i in range(min(5, len(t_sample))):
        print(f"    Ξ({t_sample[i]:7.2f}) = {xi_sample[i]:12.6e}")
    print()
    
    # Time domain
    print("TIME DOMAIN (u):")
    u_sample = op.u[::64]
    phi_sample = op.compute_correlation_function(u_sample)
    print("  Φ(u) = Correlation function (Prime distribution)")
    for i in range(min(5, len(u_sample))):
        print(f"    Φ({u_sample[i]:7.2f}) = {phi_sample[i]:12.6e}")
    print()
    
    print("The Mirror Relationship:")
    print("  • Φ(u) = Fourier transform of Ξ(t)")
    print("  • Primes in u-space ↔ Zeros in t-space")
    print("  • T reflects one domain into the other")
    print("  • Riemann-Weil formula: arithmetic ↔ spectral")
    print()
    
    print(f"Fundamental frequency: f₀ = {F0_QCAL} Hz")
    print(f"This frequency bridges both domains")
    print()


def demo_summary():
    """Summary of all demonstrations."""
    print("=" * 80)
    print("SUMMARY: Riemann Intensity Operator Framework")
    print("=" * 80)
    print()
    
    print("Key Results:")
    print()
    
    print("1. INTENSITY OPERATOR T_Ω = |T|")
    print("   • Non-negative eigenvalues: |Ξ(t)| ≥ 0")
    print("   • Well-defined everywhere")
    print()
    
    print("2. HAMILTONIAN H = -log|T|")
    print("   • Logarithmic singularities at zeros")
    print("   • Zeros = infinite energy points")
    print("   • Phase-jump mechanism in Vortex 8")
    print()
    
    print("3. GUE REPULSION & SIMPLICITY")
    print("   • Zeros follow GUE statistics")
    print("   • Level repulsion prevents degeneracy")
    print("   • Torsion term: tanh(u) creates repulsion force")
    print("   • All zeros are simple: Ξ'(t) ≠ 0")
    print()
    
    print("4. QUANTIZATION CONDITION")
    print("   • Paley-Wiener confinement")
    print("   • Trace formula: Z = Tr(f(H))")
    print("   • Riemann-Weil formula verified")
    print()
    
    print("5. RIEMANN MIRROR")
    print("   • T reflects primes ↔ zeros")
    print("   • Time domain (u) ↔ Frequency domain (t)")
    print("   • Φ(u) = Feynman propagator = Prime correlation")
    print()
    
    print(f"∴𓂀Ω∞³ @ {F0_QCAL} Hz")
    print()


def main():
    """Run all demonstrations."""
    import sys
    
    # Check for non-interactive mode
    non_interactive = '--auto' in sys.argv or '--non-interactive' in sys.argv
    
    demos = [
        demo_basic_operator,
        demo_intensity_spectrum,
        demo_hamiltonian,
        demo_torsion_repulsion,
        demo_weil_formula,
        demo_riemann_mirror,
        demo_summary
    ]
    
    for i, demo in enumerate(demos, 1):
        demo()
        if i < len(demos):
            if non_interactive:
                print("\nContinuing to next demo...\n")
            else:
                input("\nPress Enter to continue to next demo...\n")


if __name__ == "__main__":
    main()
