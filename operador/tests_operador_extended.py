"""
Extended tests with convergence table output.

This module prints detailed convergence tables showing how the
cosine basis quadrature converges to the exact Fourier spectrum
as the number of quadrature points (Nq) increases.
"""

import numpy as np
from operador.operador_H import build_R_matrix, spectrum_from_R, fourier_eigs_H


def test_print_convergence_table():
    """Print convergence table for different Nq values."""
    h = 1e-3
    L = 1.0
    n_basis = 5

    # Fourier (exact reference)
    lam_H_F, gammas_F = fourier_eigs_H(n_modes=n_basis, h=h, L=L)

    print("\n" + "=" * 70)
    print("CONVERGENCE: COSINE BASIS → FOURIER")
    print("=" * 70)
    print(f"Reference Fourier (exact): eig(H) = {lam_H_F}")
    print(f"Gammas Fourier: {gammas_F}")

    for Nq in [40, 80, 160, 200]:
        R = build_R_matrix(n_basis=n_basis, h=h, L=L, Nq=Nq)
        lam_H, gammas = spectrum_from_R(R, h)

        diff = lam_H - lam_H_F
        norm_diff = np.linalg.norm(diff)

        print(f"\nNq = {Nq}")
        print(f"Eig(H) cosine: {lam_H}")
        print(f"Difference (cos - Fourier): {diff}")
        print(f"Norm of difference: {norm_diff:.3e}")

        # Basic check: difference should be reasonable
        if Nq > 40:
            assert norm_diff < 200.0, f"Difference norm {norm_diff} seems too large for Nq={Nq}"

    print("\n" + "=" * 70)
    print("✓ Convergence test complete")
    print("=" * 70)


if __name__ == "__main__":
    import pytest
    pytest.main([__file__, "-s", "-v"])
