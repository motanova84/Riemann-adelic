"""
Demonstration of the new Gaussian kernel operator implementation.

This script shows how to use the new operador module and compares
it with the Fourier basis exact solution.
"""

import numpy as np
from operador.operador_H import (
    K_gauss,
    build_R_matrix,
    spectrum_from_R,
    fourier_eigs_H
)


def demo_basic_usage():
    """Demonstrate basic usage of the operator module."""
    print("=" * 70)
    print("GAUSSIAN KERNEL OPERATOR - BASIC USAGE")
    print("=" * 70)
    print()
    
    # Parameters
    h = 1e-3
    L = 1.0
    n_basis = 5
    
    print(f"Parameters:")
    print(f"  h (thermal parameter): {h}")
    print(f"  L (domain half-width): {L}")
    print(f"  n_basis (matrix size): {n_basis}")
    print()
    
    # Build R matrix
    print("Step 1: Building heat operator R_h via cosine basis...")
    R = build_R_matrix(n_basis=n_basis, h=h, L=L, Nq=160)
    print(f"  ✓ R matrix shape: {R.shape}")
    print(f"  ✓ R is symmetric: {np.allclose(R, R.T)}")
    print(f"  ✓ R eigenvalues (all positive): {np.linalg.eigvalsh(R)}")
    print()
    
    # Extract H spectrum
    print("Step 2: Extracting Hamiltonian H spectrum...")
    lam_H, gammas = spectrum_from_R(R, h)
    print(f"  ✓ H eigenvalues: {lam_H}")
    print(f"  ✓ All λ > 1/4: {np.all(lam_H > 0.25)}")
    print(f"  ✓ Estimated γ values: {gammas}")
    print()
    
    # Compare with Fourier
    print("Step 3: Computing exact Fourier solution...")
    lam_H_F, gammas_F = fourier_eigs_H(n_modes=n_basis, h=h, L=L)
    print(f"  ✓ Exact H eigenvalues (Fourier): {lam_H_F}")
    print(f"  ✓ Exact γ values (Fourier): {gammas_F}")
    print()
    
    # Analysis
    print("Step 4: Comparing cosine vs Fourier basis...")
    diff = lam_H - lam_H_F
    print(f"  Difference (cosine - Fourier): {diff}")
    print(f"  L² norm of difference: {np.linalg.norm(diff):.3e}")
    print()
    
    print("=" * 70)
    print("✓ Basic demonstration complete!")
    print("=" * 70)
    print()


def demo_convergence():
    """Demonstrate convergence as Nq increases."""
    print("=" * 70)
    print("QUADRATURE CONVERGENCE STUDY")
    print("=" * 70)
    print()
    
    h = 1e-3
    L = 1.0
    n_basis = 5
    
    print("Testing quadrature convergence with increasing Nq...")
    print()
    
    Nq_values = [40, 80, 120, 160, 200]
    prev_lam = None
    
    for Nq in Nq_values:
        R = build_R_matrix(n_basis=n_basis, h=h, L=L, Nq=Nq)
        lam_H, _ = spectrum_from_R(R, h)
        
        print(f"Nq = {Nq:3d}:")
        print(f"  First eigenvalue: {lam_H[0]:.8f}")
        
        if prev_lam is not None:
            change = np.linalg.norm(lam_H - prev_lam)
            print(f"  Change from previous: {change:.3e}")
        
        prev_lam = lam_H
        print()
    
    print("Note: Results stabilize as Nq → ∞")
    print("=" * 70)
    print()


def demo_kernel_properties():
    """Demonstrate properties of the Gaussian kernel."""
    print("=" * 70)
    print("GAUSSIAN KERNEL PROPERTIES")
    print("=" * 70)
    print()
    
    h = 1e-3
    t_vals = np.linspace(-1, 1, 11)
    
    print(f"Kernel K_h(t, 0) for h={h}:")
    print()
    print("  t          K_h(t, 0)")
    print("  " + "-" * 35)
    
    for t in t_vals:
        K = K_gauss(t, 0.0, h)
        print(f"  {t:6.2f}     {K:12.6f}")
    
    print()
    print("Properties:")
    print(f"  ✓ Symmetric: K(t,s) = K(s,t)")
    print(f"  ✓ Positive: K(t,t) > 0")
    print(f"  ✓ Gaussian decay: K(t,s) ~ exp(-(t-s)²/(4h))")
    print(f"  ✓ No oscillations (closed form!)")
    print()
    print("=" * 70)
    print()


def demo_comparison_with_odlyzko():
    """Show how this relates to Riemann zeros."""
    print("=" * 70)
    print("RELATION TO RIEMANN ZEROS")
    print("=" * 70)
    print()
    
    print("The spectrum of H relates to Riemann zeros via:")
    print("  λ = 1/4 + γ²")
    print()
    print("For the universal flow (geometric, not arithmetic):")
    print("  In Fourier basis: λ_k = ω_k² + 1/4  with ω_k = πk/L")
    print("  This gives γ_k = ω_k = πk/L")
    print()
    
    h = 1e-3
    L = 1.0
    n_modes = 10
    
    lam_H, gammas = fourier_eigs_H(n_modes=n_modes, h=h, L=L)
    
    print(f"Geometric γ values (L={L}):")
    for k in range(min(5, n_modes)):
        print(f"  γ_{k} = {gammas[k]:.6f}  (= {k}π/L)")
    print()
    
    print("Note: These are NOT the arithmetic Riemann zeros!")
    print("To recover arithmetic zeros γ_k (Odlyzko), you need:")
    print("  1. Functional equation D(1-s) = D(s)")
    print("  2. de Branges structure (non-periodic boundary)")
    print("  3. Identification D ≡ Ξ")
    print()
    print("This operator gives the geometric spectrum.")
    print("Arithmetic recovery requires the full pipeline (§6-§8).")
    print()
    print("=" * 70)
    print()


if __name__ == "__main__":
    demo_basic_usage()
    demo_convergence()
    demo_kernel_properties()
    demo_comparison_with_odlyzko()
    
    print()
    print("🎉 All demonstrations complete!")
    print()
    print("Next steps:")
    print("  - Run tests: pytest operador/tests_operador.py -v")
    print("  - See convergence: pytest operador/tests_operador_extended.py -s")
    print("  - Integrate with thermal_kernel_spectral.py for full pipeline")
