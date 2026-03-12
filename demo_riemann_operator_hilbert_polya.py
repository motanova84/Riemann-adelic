#!/usr/bin/env python3
"""
Demo: Riemann Operator Hilbert-Pólya
======================================

9 interactive demonstrations of the Hilbert-Pólya Hamiltonian:

  1. Grid symmetry of L²_even(ℝ, du)
  2. Parity enforcement
  3. Kinetic operator properties
  4. Prime-potential construction
  5. Hermiticity verification
  6. Parity commutation [H, P] = 0
  7. Eigenvalue reality
  8. Comparison with Riemann zeros
  9. Fredholm determinant

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: March 2026
DOI: 10.5281/zenodo.17379721
"""

import os
import sys
import numpy as np

# Headless matplotlib for environments without a display
import matplotlib
if not os.environ.get("DISPLAY"):
    matplotlib.use("Agg")
import matplotlib.pyplot as plt

sys.path.insert(0, os.path.abspath(os.path.dirname(__file__)))

from riemann_operator_hilbert_polya import (
    EvenHilbertSpace,
    HilbertPolyaOperator,
    RIEMANN_ZEROS_KNOWN,
    F0_QCAL,
    C_COHERENCE,
)

LINE = "=" * 65


def demo_1_grid_symmetry():
    """Demo 1 – Grid symmetry of L²_even(ℝ, du)."""
    print(f"\n{LINE}")
    print("DEMO 1: Grid symmetry of L²_even(ℝ, du)")
    print(LINE)

    space = EvenHilbertSpace(N=10, u_max=5.0)
    u = space.u
    print(f"  N = {space.N}, u_max = {space.u_max}")
    print(f"  u[:5]  = {np.round(u[:5], 3)}")
    print(f"  u[-5:] = {np.round(u[-5:], 3)}")
    sym_err = float(np.max(np.abs(u + u[::-1])))
    print(f"  Symmetry error max|u_i + u_(N-1-i)| = {sym_err:.2e}")
    assert sym_err < 1e-12
    print("  ✅ Grid is symmetric.")


def demo_2_parity_enforcement():
    """Demo 2 – Parity enforcement."""
    print(f"\n{LINE}")
    print("DEMO 2: Parity enforcement")
    print(LINE)

    space = EvenHilbertSpace(N=50, u_max=8.0)
    rng = np.random.default_rng(0)
    psi = rng.standard_normal(space.N)

    before_is_even, before_err = space.check_parity(psi)
    psi_even = space.enforce_parity(psi)
    after_is_even, after_err = space.check_parity(psi_even)

    print(f"  Before enforce_parity: is_even={before_is_even}, error={before_err:.3e}")
    print(f"  After  enforce_parity: is_even={after_is_even},  error={after_err:.3e}")
    assert after_is_even
    print("  ✅ Parity successfully enforced.")


def demo_3_kinetic_operator():
    """Demo 3 – Kinetic operator H_kin = -d²/du² + tanh²(u)/2."""
    print(f"\n{LINE}")
    print("DEMO 3: Kinetic operator H_kin = -d²/du² + tanh²(u)/2")
    print(LINE)

    space = EvenHilbertSpace(N=60, u_max=10.0)
    op = HilbertPolyaOperator(space, num_primes=0, max_k=1)  # no potential
    H = op.matrix
    sym_err = float(np.max(np.abs(H - H.T)))
    print(f"  H_kin symmetry error: {sym_err:.2e}")
    print(f"  H_kin diagonal max: {np.max(np.diag(H)):.4f}")
    print(f"  H_kin off-diagonal structure: tridiagonal + periodic BC")
    assert sym_err < 1e-12
    print("  ✅ Kinetic operator is symmetric.")


def demo_4_prime_potential():
    """Demo 4 – Prime-potential V(u) = Σ (ln p / p^{k/2}) δ(u - k ln p)."""
    print(f"\n{LINE}")
    print("DEMO 4: Prime potential V(u)")
    print(LINE)

    space = EvenHilbertSpace(N=200, u_max=15.0)
    # Isolate potential as difference: H_full - H_kin_only
    op_full = HilbertPolyaOperator(space, num_primes=10, max_k=4)
    op_kin = HilbertPolyaOperator(space, num_primes=0, max_k=1)
    V_diag = np.diag(op_full.matrix) - np.diag(op_kin.matrix)

    u = space.u
    print(f"  Number of primes used: 10")
    print(f"  Max V(u): {V_diag.max():.4f}  at u={u[np.argmax(V_diag)]:.3f}")
    print(f"  Symmetry check max|V(u)-V(-u)|: "
          f"{float(np.max(np.abs(V_diag - V_diag[::-1]))):.2e}")

    # Plot
    fig, ax = plt.subplots(figsize=(8, 3))
    ax.plot(u, V_diag, lw=0.8, color="steelblue")
    ax.set_xlabel("u"); ax.set_ylabel("V(u)")
    ax.set_title("Prime potential V(u) (symmetric)")
    ax.set_xlim(-15, 15)
    fig.tight_layout()
    fig.savefig("/tmp/demo4_potential.png", dpi=80)
    plt.close(fig)
    print("  ✅ Potential saved to /tmp/demo4_potential.png")


def demo_5_hermiticity():
    """Demo 5 – Hermiticity verification H† = H."""
    print(f"\n{LINE}")
    print("DEMO 5: Hermiticity verification")
    print(LINE)

    space = EvenHilbertSpace(N=100, u_max=12.0)
    op = HilbertPolyaOperator(space, num_primes=15, max_k=5)
    is_herm, err = op.check_hermiticity()
    print(f"  ||H - H†||_F = {err:.2e}")
    print(f"  is_hermitian = {is_herm}")
    assert is_herm
    print("  ✅ Operator is Hermitian (self-adjoint).")


def demo_6_parity_commutation():
    """Demo 6 – Parity commutation [H, P] = 0."""
    print(f"\n{LINE}")
    print("DEMO 6: Parity commutation [H, P] = 0")
    print(LINE)

    space = EvenHilbertSpace(N=80, u_max=12.0)
    op = HilbertPolyaOperator(space, num_primes=12, max_k=5)
    commutes, err = op.check_parity_commutation()
    print(f"  ||[H, P]||_F = {err:.2e}")
    print(f"  Commutes: {commutes}")
    assert commutes
    print("  ✅ [H, P] = 0  (parity symmetry preserved).")


def demo_7_eigenvalue_reality():
    """Demo 7 – All eigenvalues are real."""
    print(f"\n{LINE}")
    print("DEMO 7: Eigenvalue reality")
    print(LINE)

    space = EvenHilbertSpace(N=80, u_max=12.0)
    op = HilbertPolyaOperator(space, num_primes=12, max_k=5)
    vals = op.eigenvalues()
    max_imag = float(np.max(np.abs(np.imag(vals))))
    print(f"  Total eigenvalues: {len(vals)}")
    print(f"  max|Im(λ)|        = {max_imag:.2e}")
    print(f"  First 5 positive eigenvalues: {np.sort(vals[vals > 0])[:5].round(3)}")
    assert max_imag < 1e-10
    print("  ✅ All eigenvalues are real.")


def demo_8_zeta_zeros_comparison():
    """Demo 8 – Compare eigenvalues with known Riemann zeros."""
    print(f"\n{LINE}")
    print("DEMO 8: Comparison with Riemann zeros γ_n")
    print(LINE)

    space = EvenHilbertSpace(N=200, u_max=15.0)
    op = HilbertPolyaOperator(space, num_primes=20, max_k=6)
    result = op.compare_with_zeta_zeros(n_zeros=10)

    evals = result["eigenvalues"]
    zeros = result["riemann_zeros"]
    corr = result["correlation"]
    mean_err = result["mean_error"]

    n = min(len(evals), len(zeros))
    print(f"  {'n':>3}  {'λ_n (operator)':>18}  {'γ_n (Riemann)':>16}")
    print(f"  {'-'*42}")
    for i in range(n):
        print(f"  {i+1:>3}  {evals[i]:>18.6f}  {zeros[i]:>16.6f}")

    print(f"\n  Pearson correlation r = {corr:.4f}")
    print(f"  Mean |λ_n - γ_n|     = {mean_err:.4f}")

    # Plot
    fig, axes = plt.subplots(1, 2, figsize=(10, 4))
    axes[0].scatter(zeros, evals[:n], s=30, color="steelblue")
    lim = max(float(zeros.max()), float(evals.max())) + 2
    axes[0].plot([0, lim], [0, lim], "r--", lw=0.8)
    axes[0].set_xlabel("γ_n (Riemann zeros)")
    axes[0].set_ylabel("λ_n (eigenvalues)")
    axes[0].set_title(f"Correlation r = {corr:.3f}")

    axes[1].bar(range(1, n + 1), np.abs(evals[:n] - zeros), color="tomato")
    axes[1].set_xlabel("n"); axes[1].set_ylabel("|λ_n - γ_n|")
    axes[1].set_title("Absolute error per zero")

    fig.tight_layout()
    fig.savefig("/tmp/demo8_zeros.png", dpi=80)
    plt.close(fig)
    print("  ✅ Plot saved to /tmp/demo8_zeros.png")


def demo_9_fredholm_determinant():
    """Demo 9 – Fredholm determinant det(s - H)."""
    print(f"\n{LINE}")
    print("DEMO 9: Fredholm determinant det(s - H)")
    print(LINE)

    space = EvenHilbertSpace(N=60, u_max=10.0)
    op = HilbertPolyaOperator(space, num_primes=10, max_k=4)

    s_values = [complex(0.5, gamma) for gamma in [10.0, 14.134725, 21.022040, 30.0]]
    print(f"  {'s':>30}  {'|det(s-H)|':>14}")
    print(f"  {'-'*48}")
    for s in s_values:
        det = op.fredholm_determinant(s, reg=1e-2)
        print(f"  {str(s):>30}  {abs(det):>14.6f}")

    print("  ✅ Fredholm determinants computed.")


def main():
    """Run all 9 demonstrations."""
    print(f"\n{'*'*65}")
    print("  Riemann Operator Hilbert-Pólya — Interactive Demonstrations")
    print(f"  f₀ = {F0_QCAL} Hz  |  C = {C_COHERENCE}  |  DOI: 10.5281/zenodo.17379721")
    print(f"{'*'*65}")

    demos = [
        demo_1_grid_symmetry,
        demo_2_parity_enforcement,
        demo_3_kinetic_operator,
        demo_4_prime_potential,
        demo_5_hermiticity,
        demo_6_parity_commutation,
        demo_7_eigenvalue_reality,
        demo_8_zeta_zeros_comparison,
        demo_9_fredholm_determinant,
    ]

    passed = 0
    for demo in demos:
        try:
            demo()
            passed += 1
        except Exception as exc:
            print(f"  ❌ {demo.__name__} FAILED: {exc}")

    print(f"\n{LINE}")
    print(f"  {passed}/{len(demos)} demonstrations completed successfully.")
    if passed == len(demos):
        print("  ✅ QCAL-Evolution Complete – all demos passed.")
    print(LINE)


if __name__ == "__main__":
    main()
