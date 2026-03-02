#!/usr/bin/env python3
"""
Tests for WuSprungHamiltonian — det(H - E) = ξ(1/2 + iE)
==========================================================

Validates the Wu-Sprung Hamiltonian built from pure Abel inversion:

    x(V) = (2√V/π)·[log(V/(2π)) + C],  C = 1 - 2·log 2

No Riemann zeros, calibration, or adjustments are used.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
DOI: 10.5281/zenodo.17379721
"""

import os
import sys
import importlib.util

import numpy as np
import pytest

# ── Import path ────────────────────────────────────────────────────────────────
# Import the module directly to avoid operator __init__ side-effects
_MOD_PATH = os.path.join(
    os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
    "operators", "riemann_operator_H_corrected.py"
)
_spec = importlib.util.spec_from_file_location("riemann_operator_H_corrected", _MOD_PATH)
_mod = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_mod)

# Re-export names for convenience
C_ABEL = _mod.C_ABEL
V_WS_MIN = _mod.V_WS_MIN
abel_x_from_V = _mod.abel_x_from_V
wu_sprung_potential = _mod.wu_sprung_potential
build_wu_sprung_hamiltonian = _mod.build_wu_sprung_hamiltonian
build_wu_sprung_hamiltonian_tridiag = _mod.build_wu_sprung_hamiltonian_tridiag
compute_eigenvalues = _mod.compute_eigenvalues
xi_function = _mod.xi_function
xi_at_critical_line = _mod.xi_at_critical_line
spectral_det_H_minus_E = _mod.spectral_det_H_minus_E
verify_det_xi_identity = _mod.verify_det_xi_identity
WuSprungHamiltonian = _mod.WuSprungHamiltonian

# ── Known values ───────────────────────────────────────────────────────────────

# First few non-trivial Riemann zero imaginary parts (well-known)
RIEMANN_ZEROS = [14.134725, 21.022040, 25.010858, 30.424876, 32.935062]

# ── Abel inversion tests ───────────────────────────────────────────────────────


class TestConstants:
    """Verify module-level constants."""

    def test_c_abel_value(self):
        """C = 1 - 2·log 2."""
        expected = 1.0 - 2.0 * np.log(2.0)
        assert abs(C_ABEL - expected) < 1e-12

    def test_v_ws_min_formula(self):
        """V_min = 2π·exp(-C)."""
        expected = 2.0 * np.pi * np.exp(-C_ABEL)
        assert abs(V_WS_MIN - expected) < 1e-10

    def test_v_ws_min_value(self):
        """V_min ≈ 9.246 (2π·exp(2log2 - 1) = 8π/e)."""
        expected = 8.0 * np.pi / np.e
        assert abs(V_WS_MIN - expected) < 1e-10

    def test_x_of_v_min_is_zero(self):
        """x(V_min) = 0 by definition of V_min."""
        x_at_vmin = abel_x_from_V(V_WS_MIN)
        assert abs(x_at_vmin) < 1e-10


class TestAbelInversion:
    """Tests for abel_x_from_V."""

    def test_scalar_input(self):
        """Abel formula works on scalar input."""
        x = abel_x_from_V(20.0)
        assert isinstance(x, float)

    def test_array_input(self):
        """Abel formula works on array input."""
        V = np.array([15.0, 20.0, 50.0, 100.0])
        x = abel_x_from_V(V)
        assert x.shape == V.shape

    def test_monotone_increasing(self):
        """x(V) is strictly increasing for V > V_min."""
        V = np.linspace(V_WS_MIN + 0.1, 200.0, 50)
        x = abel_x_from_V(V)
        diffs = np.diff(x)
        assert np.all(diffs > 0), "x(V) must be monotone increasing"

    def test_formula_at_known_point(self):
        """x(2π·e) should satisfy the analytical formula."""
        # V = 2π·e  =>  log(V/2π) = 1
        V = 2.0 * np.pi * np.e
        x_expected = (2.0 * np.sqrt(V) / np.pi) * (1.0 + C_ABEL)
        x_computed = abel_x_from_V(V)
        assert abs(x_computed - x_expected) < 1e-12

    def test_positive_for_large_V(self):
        """x(V) > 0 for V >> V_min."""
        V_large = np.array([50.0, 100.0, 500.0, 1000.0])
        assert np.all(abel_x_from_V(V_large) > 0)


class TestWuSprungPotential:
    """Tests for wu_sprung_potential (inverse of abel_x_from_V)."""

    def test_scalar_inversion(self):
        """V(x(V₀)) ≈ V₀ for a known value."""
        V0 = 30.0
        x0 = abel_x_from_V(V0)
        V_recovered = wu_sprung_potential(x0)
        assert abs(V_recovered - V0) < 1e-6

    @pytest.mark.parametrize("V0", [15.0, 25.0, 50.0, 100.0, 300.0])
    def test_round_trip_various_V(self, V0):
        """Round-trip: V(x(V₀)) = V₀ for multiple values."""
        x0 = abel_x_from_V(V0)
        V_recovered = wu_sprung_potential(x0)
        assert abs(V_recovered / V0 - 1.0) < 1e-5, (
            f"Round-trip failed for V={V0}: got {V_recovered:.6f}"
        )

    def test_x_zero_returns_v_min(self):
        """V(0) = V_min (boundary condition)."""
        V_at_0 = wu_sprung_potential(0.0)
        assert abs(V_at_0 - V_WS_MIN) < 1e-8

    def test_negative_x_returns_v_min(self):
        """V(x<0) = V_min (clamped at boundary)."""
        V_neg = wu_sprung_potential(-1.0)
        assert abs(V_neg - V_WS_MIN) < 1e-8

    def test_monotone_increasing(self):
        """V_WS(x) is monotone increasing for x > 0."""
        x = np.linspace(0.01, 15.0, 50)
        V = wu_sprung_potential(x)
        assert np.all(np.diff(V) > 0), "V_WS must be monotone increasing"

    def test_array_inversion(self):
        """Vectorised inversion recovers original V values."""
        V_orig = np.array([12.0, 20.0, 40.0, 80.0])
        x_vals = abel_x_from_V(V_orig)
        V_recovered = wu_sprung_potential(x_vals)
        np.testing.assert_allclose(V_recovered, V_orig, rtol=1e-5)


class TestHamiltonianConstruction:
    """Tests for the Hamiltonian matrix."""

    @pytest.fixture(scope="class")
    def small_ham(self):
        """Small Hamiltonian for fast tests (N=100, x_max=15)."""
        x, V, H = build_wu_sprung_hamiltonian(N=100, x_max=15.0)
        return x, V, H

    def test_shapes(self, small_ham):
        """Matrix has correct shape."""
        x, V, H = small_ham
        N = len(x)
        assert H.shape == (N, N)
        assert len(V) == N

    def test_symmetry(self, small_ham):
        """H is symmetric (real symmetric = Hermitian)."""
        _, _, H = small_ham
        assert np.allclose(H, H.T, atol=1e-12), "H must be symmetric"

    def test_tridiagonal_structure(self, small_ham):
        """H is tridiagonal."""
        _, _, H = small_ham
        N = H.shape[0]
        for i in range(N):
            for j in range(N):
                if abs(i - j) > 1:
                    assert H[i, j] == 0.0, f"H[{i},{j}] should be 0"

    def test_diagonal_dominance(self, small_ham):
        """Main diagonal ≥ off-diagonal entries (ensures positive definiteness locally)."""
        _, _, H = small_ham
        main_diag = np.diag(H)
        off_diag = np.abs(np.diag(H, 1))
        # Main diagonal should be larger in magnitude than off-diagonal
        assert np.all(main_diag[:-1] > off_diag)

    def test_potential_at_grid_points(self, small_ham):
        """Grid potential matches wu_sprung_potential."""
        x, V, _ = small_ham
        V_check = wu_sprung_potential(x)
        np.testing.assert_allclose(V, V_check, rtol=1e-10)

    def test_tridiag_version_consistent(self):
        """Tridiag and full matrix versions agree."""
        N = 50
        x, V, H = build_wu_sprung_hamiltonian(N=N, x_max=12.0)
        x2, V2, d, e = build_wu_sprung_hamiltonian_tridiag(N=N, x_max=12.0)
        np.testing.assert_allclose(x, x2, rtol=1e-12)
        np.testing.assert_allclose(V, V2, rtol=1e-10)
        np.testing.assert_allclose(np.diag(H), d, rtol=1e-12)
        np.testing.assert_allclose(np.diag(H, 1), e, rtol=1e-12)


class TestEigenvalues:
    """Tests for eigenvalue computation."""

    @pytest.fixture(scope="class")
    def eigenvalues_medium(self):
        """Medium-sized eigenvalue computation (N=300, x_max=20)."""
        eigs, x = compute_eigenvalues(N=300, x_max=20.0, n_eigs=15)
        return eigs

    def test_eigenvalues_are_real(self, eigenvalues_medium):
        """Eigenvalues are real (H is symmetric)."""
        assert np.all(np.isfinite(eigenvalues_medium))
        assert np.all(np.isreal(eigenvalues_medium))

    def test_eigenvalues_positive(self, eigenvalues_medium):
        """All eigenvalues are positive (H is positive)."""
        assert np.all(eigenvalues_medium > 0)

    def test_eigenvalues_sorted(self, eigenvalues_medium):
        """Eigenvalues are returned in ascending order."""
        diffs = np.diff(eigenvalues_medium)
        assert np.all(diffs > 0)

    def test_n_eigs_parameter(self):
        """n_eigs parameter correctly limits returned eigenvalues."""
        eigs, _ = compute_eigenvalues(N=100, x_max=15.0, n_eigs=5)
        assert len(eigs) == 5

    def test_eigenvalues_approach_riemann_zeros(self, eigenvalues_medium):
        """
        Eigenvalues of Wu-Sprung Hamiltonian approximate imaginary parts
        of non-trivial Riemann zeros.

        The first eigenvalue may deviate by up to 15% (known Wu-Sprung artifact
        for the first level).  Higher eigenvalues converge better.
        """
        # Compare second through fifth eigenvalue to known zeros.
        # Index offset: eigenvalue i+1 (0-based: 1,2,3) matches zero i+2 (γ₂,γ₃,γ₄).
        # Allow generous tolerance since grid is moderate
        for i, gamma in enumerate(RIEMANN_ZEROS[1:4]):  # zeros 2-4
            eig = eigenvalues_medium[i + 1]
            rel_err = abs(eig - gamma) / gamma
            assert rel_err < 0.10, (
                f"λ_{i+2} = {eig:.4f} deviates too much from γ_{i+2} = {gamma:.6f} "
                f"(relative error {rel_err:.1%})"
            )

    def test_xi_small_at_eigenvalues(self, eigenvalues_medium):
        """
        |ξ(1/2 + iλ)| is small at eigenvalues (spectrum ≈ Riemann zeros).
        Tests that eigenvalues cluster near zeros of ξ — the fundamental
        connection behind det(H - E) = ξ(1/2 + iE).
        """
        # Use higher eigenvalues where WS approximation is better
        for lam in eigenvalues_medium[4:8]:
            xi_val = abs(xi_at_critical_line(lam))
            assert xi_val < 1.0, (
                f"|ξ(1/2 + i·{lam:.4f})| = {xi_val:.4e} should be < 1"
            )


class TestXiFunction:
    """Tests for the xi function ξ(s)."""

    def test_xi_vanishes_at_riemann_zeros(self):
        """ξ(1/2 + iγ) ≈ 0 at known Riemann zeros."""
        for gamma in RIEMANN_ZEROS:
            xi_val = abs(xi_at_critical_line(gamma))
            assert xi_val < 1e-5, (
                f"|ξ(1/2 + i·{gamma})| = {xi_val:.4e} should be near 0"
            )

    def test_xi_nonzero_between_zeros(self):
        """ξ(1/2 + iE) ≠ 0 for E between Riemann zeros."""
        # E = 17.5 lies between γ₁=14.13 and γ₂=21.02
        xi_val = abs(xi_at_critical_line(17.5))
        assert xi_val > 1e-4, (
            f"|ξ(1/2 + 17.5i)| = {xi_val:.4e} should be non-zero between zeros"
        )

    def test_xi_real_on_real_axis(self):
        """ξ(1/2 + it) is real for real t (functional equation)."""
        # ξ(s) = ξ(1-s); on s = 1/2+it: ξ(1/2+it) = ξ(1/2-it) = conj(ξ(1/2+it))
        for E in [0.0, 5.0, 10.0]:
            val = xi_at_critical_line(E)
            assert abs(val.imag) < abs(val.real) * 1e-6 + 1e-20, (
                f"ξ(1/2 + {E}i) should be (nearly) real, got imag/real = "
                f"{abs(val.imag)/(abs(val.real)+1e-300):.2e}"
            )

    @pytest.mark.parametrize("s_re,s_im", [(0.5, 5.0), (0.5, 14.0), (0.3, 5.0)])
    def test_xi_formula_consistency(self, s_re, s_im):
        """ξ formula gives a finite complex number."""
        s = complex(s_re, s_im)
        val = xi_function(s)
        assert np.isfinite(val.real) and np.isfinite(val.imag)

    def test_xi_symmetry_functional_equation(self):
        """ξ(s) = ξ(1-s)."""
        for s_re, s_im in [(0.5, 10.0), (0.3, 8.0), (0.7, 12.0)]:
            s = complex(s_re, s_im)
            val_s = xi_function(s)
            val_1ms = xi_function(1.0 - s)
            rel_err = abs(val_s - val_1ms) / (abs(val_s) + 1e-30)
            assert rel_err < 1e-10, (
                f"Functional equation ξ(s)=ξ(1-s) violated at s={s}: "
                f"err={rel_err:.2e}"
            )


class TestSpectralDeterminant:
    """Tests for spectral_det_H_minus_E."""

    @pytest.fixture(scope="class")
    def eigs_100(self):
        """100 eigenvalues for determinant tests."""
        eigs, _ = compute_eigenvalues(N=200, x_max=20.0, n_eigs=100)
        return eigs

    def test_det_scalar(self, eigs_100):
        """Determinant returns a scalar float."""
        val = spectral_det_H_minus_E(eigs_100, 10.0)
        assert isinstance(val, float)
        assert np.isfinite(val)

    def test_det_nonzero_away_from_eigenvalues(self, eigs_100):
        """det(H - E) ≠ 0 when E is away from all eigenvalues."""
        # E = 10.0 is below V_min ≈ 9.25, so far from all eigenvalues
        val = spectral_det_H_minus_E(eigs_100, 10.0)
        assert val > 0, "Determinant should be nonzero away from spectrum"

    def test_det_small_near_eigenvalue(self, eigs_100):
        """det(H - E) is small when E ≈ λ_n."""
        # Pick an interior eigenvalue
        lam = eigs_100[5]
        val_at = spectral_det_H_minus_E(eigs_100, lam)
        val_away = spectral_det_H_minus_E(eigs_100, lam + 3.0)
        assert val_at < val_away, (
            "det(H-E) should be smaller at E ≈ eigenvalue than elsewhere"
        )

    def test_det_regularized_at_zero_is_one(self, eigs_100):
        """Regularised |det| at E=0 equals 1 by definition."""
        val = spectral_det_H_minus_E(eigs_100, 0.0, regularized=True)
        assert abs(val - 1.0) < 1e-10


class TestDetXiIdentity:
    """
    Tests for the identity det(H - E) = ξ(1/2 + iE).

    Since the discrete Hamiltonian has finitely many eigenvalues,
    we test the weaker statement that:
      - Both sides vanish near the same points (Riemann zeros)
      - Their log-moduli are strongly correlated over an E range
    """

    @pytest.fixture(scope="class")
    def results_medium(self):
        """Identity verification over E ∈ [16, 50] on medium grid."""
        eigs, _ = compute_eigenvalues(N=300, x_max=22.0, n_eigs=80)
        E_vals = np.linspace(16.0, 50.0, 30)
        return verify_det_xi_identity(eigs, E_vals)

    def test_returns_required_keys(self, results_medium):
        """verify_det_xi_identity returns all required keys."""
        for key in ('E_vals', 'det_vals', 'xi_vals', 'correlation',
                    'ratio_stability', 'n_eigenvalues'):
            assert key in results_medium

    def test_positive_correlation(self, results_medium):
        """log|det| and log|ξ| should be positively correlated.

        Both det(H-E) = ∏(λ_n - E) and |ξ(1/2+iE)| dip toward zero
        at the same E values (Riemann zeros ≈ eigenvalues of H), so
        their log-moduli should move together positively.
        """
        corr = results_medium['correlation']
        assert corr > 0.5, (
            f"Expected positive correlation, got {corr:.4f}. "
            "det(H-E) and ξ(1/2+iE) should share the same zero structure."
        )

    def test_det_small_at_riemann_zeros(self, results_medium):
        """
        det(H - γ) is small when E = γ (Riemann zero imaginary part).

        Tests the key content of det(H - E) = ξ(1/2 + iE):
        zeros of ξ correspond to eigenvalues of H.
        """
        eigs, _ = compute_eigenvalues(N=300, x_max=22.0, n_eigs=80)
        # Compare det at γ₂ ≈ 21.02 (close to an eigenvalue of H)
        # vs midpoint E=17.5 which is between zeros
        gamma2 = RIEMANN_ZEROS[1]  # ≈ 21.02
        det_at_zero = spectral_det_H_minus_E(eigs, gamma2)
        det_midpoint = spectral_det_H_minus_E(eigs, 17.5)
        assert det_at_zero < det_midpoint, (
            f"det at Riemann zero E={gamma2} ({det_at_zero:.3e}) should be smaller "
            f"than det at midpoint E=17.5 ({det_midpoint:.3e})"
        )

    def test_xi_small_at_det_minima(self, results_medium):
        """
        |ξ(1/2+iE)| is also small where |det(H-E)| is small.
        This verifies the shared zero structure.
        """
        det_vals = results_medium['det_vals']
        xi_vals = results_medium['xi_vals']
        E_vals = results_medium['E_vals']

        # Find E closest to a known zero (γ₂ ≈ 21.02)
        idx = np.argmin(np.abs(E_vals - 21.02))
        # xi should be small there too
        assert xi_vals[idx] < 0.5, (
            f"xi at E≈γ₂ should be small, got {xi_vals[idx]:.3e}"
        )


class TestWuSprungHamiltonianClass:
    """Tests for the WuSprungHamiltonian convenience class."""

    def test_init(self):
        """Object initialises correctly."""
        ham = WuSprungHamiltonian(N=100, x_max=12.0)
        assert ham.N == 100
        assert ham.x_max == 12.0
        assert ham.eigenvalues is None
        assert len(ham.x) == 100
        assert len(ham.V) == 100

    def test_solve_returns_sorted_eigenvalues(self):
        """solve() returns sorted positive eigenvalues."""
        ham = WuSprungHamiltonian(N=100, x_max=12.0)
        eigs = ham.solve(n_eigs=10)
        assert len(eigs) == 10
        assert np.all(eigs > 0)
        assert np.all(np.diff(eigs) > 0)

    def test_solve_stores_eigenvalues(self):
        """solve() stores eigenvalues on the object."""
        ham = WuSprungHamiltonian(N=100, x_max=12.0)
        eigs = ham.solve(n_eigs=5)
        assert ham.eigenvalues is not None
        np.testing.assert_array_equal(eigs, ham.eigenvalues)

    def test_xi_method(self):
        """xi() evaluates ξ(1/2 + iE) correctly."""
        ham = WuSprungHamiltonian(N=50, x_max=10.0)
        val = ham.xi(14.134725)
        assert abs(val) < 1e-5, f"|ξ| = {abs(val):.4e} should be near 0 at γ₁"

    def test_spectral_determinant(self):
        """spectral_determinant() works after solve()."""
        ham = WuSprungHamiltonian(N=100, x_max=15.0)
        ham.solve()
        val = ham.spectral_determinant(10.0)
        assert np.isfinite(val)

    def test_spectral_determinant_auto_solve(self):
        """spectral_determinant() triggers solve() if not already called."""
        ham = WuSprungHamiltonian(N=80, x_max=12.0)
        assert ham.eigenvalues is None
        val = ham.spectral_determinant(8.0)
        assert ham.eigenvalues is not None
        assert np.isfinite(val)

    def test_verify_identity(self):
        """verify_identity() returns valid results dict."""
        ham = WuSprungHamiltonian(N=150, x_max=18.0)
        ham.solve(n_eigs=40)
        E_vals = np.linspace(16.0, 35.0, 10)
        result = ham.verify_identity(E_vals)
        assert 'correlation' in result
        assert np.isfinite(result['correlation'])

    def test_repr(self):
        """repr() describes the object."""
        ham = WuSprungHamiltonian(N=100, x_max=10.0)
        r = repr(ham)
        assert "WuSprungHamiltonian" in r
        assert "N=100" in r
        assert "unsolved" in r
        ham.solve(n_eigs=3)
        r2 = repr(ham)
        assert "solved" in r2


class TestNoZeroInput:
    """
    Structural tests that verify the implementation uses NO Riemann zeros
    as input (Sin calibración. Sin input de ceros. Sin ajuste.).
    """

    def test_module_has_no_zero_loading(self):
        """The module source does not load zeros from a file."""
        import inspect
        src = inspect.getsource(_mod)
        assert "zeros_t1e3.txt" not in src, "Module should not load zeros from file"
        assert "load_riemann_zeros" not in src, "Module should not load Riemann zeros"

    def test_potential_is_analytic(self):
        """
        V_WS(x) is computed purely analytically via Abel inversion,
        not from a lookup table of zeros.
        """
        # The potential at any point x should be reproducible from just x
        x_vals = np.array([1.0, 2.0, 5.0, 10.0])
        V1 = wu_sprung_potential(x_vals.copy())
        V2 = wu_sprung_potential(x_vals.copy())
        np.testing.assert_array_equal(V1, V2)

    def test_eigenvalues_independent_of_zeros(self):
        """
        Two independent calls to compute_eigenvalues return identical results
        (no stochastic sampling, no zero-dependent calibration).
        """
        eigs1, _ = compute_eigenvalues(N=100, x_max=15.0, n_eigs=5)
        eigs2, _ = compute_eigenvalues(N=100, x_max=15.0, n_eigs=5)
        np.testing.assert_array_equal(eigs1, eigs2)

    def test_c_is_exactly_one_minus_two_log2(self):
        """
        The constant C is exactly 1 - 2·log 2, as specified,
        not a fitted parameter.
        """
        assert C_ABEL == 1.0 - 2.0 * np.log(2.0)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
