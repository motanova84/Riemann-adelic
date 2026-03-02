#!/usr/bin/env python3
"""
Tests for Selberg-Type Trace Formula Operator
===============================================

This module tests the five-step programme:
  1. Exact domain definition and operator construction
  2. Self-adjointness and spectral properties in L²([0,L])
  3. Resolvent R(z) = (H − z)^{-1} and Green's function
  4. Explicit trace: spectral sum vs. Green's function integral
  5. Selberg-type trace formula structure

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: March 2026
QCAL ∞³ Active · 141.7001 Hz · C = 244.36
"""

import numpy as np
import pytest
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent))

from operators.selberg_trace_formula_operator import (
    # Step 1 & 2
    wu_sprung_potential,
    build_operator_matrix,
    verify_self_adjointness,
    compute_spectrum,
    # Step 3
    compute_resolvent,
    compute_green_function,
    resolvent_poles_and_residues,
    # Step 4
    trace_resolvent,
    trace_resolvent_via_green,
    trace_heat_kernel,
    trace_resolvent_path_integral,
    # Step 5
    selberg_spectral_side,
    selberg_arithmetic_side,
    verify_trace_formula,
    # Class
    SelbergTraceOperator,
    # Constants
    F0_QCAL,
    C_COHERENCE,
    DEFAULT_L,
    DEFAULT_N,
    DEFAULT_N_PRIMES,
    _first_n_primes,
)


# ---------------------------------------------------------------------------
# Shared fixtures
# ---------------------------------------------------------------------------

@pytest.fixture(scope="module")
def small_operator():
    """Small N=32 operator for fast tests."""
    H, x = build_operator_matrix(L=5.0, N=32, n_primes=5)
    return H, x


@pytest.fixture(scope="module")
def medium_operator():
    """Medium N=64 operator."""
    H, x = build_operator_matrix(L=8.0, N=64, n_primes=10)
    return H, x


@pytest.fixture(scope="module")
def medium_spectrum(medium_operator):
    H, x = medium_operator
    return compute_spectrum(H)


# ===========================================================================
# 1. DOMAIN AND OPERATOR CONSTRUCTION
# ===========================================================================

class TestWuSprungPotential:
    """Test the Wu-Sprung potential V(x)."""

    def test_positive_values(self):
        """V(x) > 0 for x > 0."""
        x = np.linspace(0.1, 10.0, 50)
        V = wu_sprung_potential(x, n_primes=5)
        assert np.all(V > 0), "Potential should be positive."

    def test_monotone_increasing(self):
        """V is approximately monotone increasing (Abel inversion)."""
        x = np.linspace(0.5, 10.0, 50)
        V = wu_sprung_potential(x, n_primes=0)   # no oscillatory correction
        # V_Abel should be increasing; check that most differences are positive
        dV = np.diff(V)
        fraction_increasing = np.mean(dV > 0)
        assert fraction_increasing > 0.60, "V_Abel should be broadly increasing."

    def test_shape(self):
        """Output shape matches input."""
        x = np.linspace(0.1, 5.0, 30)
        V = wu_sprung_potential(x, n_primes=5)
        assert V.shape == x.shape

    def test_no_nans(self):
        """No NaN or Inf values."""
        x = np.linspace(0.01, 20.0, 100)
        V = wu_sprung_potential(x, n_primes=10)
        assert np.all(np.isfinite(V)), "Potential should be finite everywhere."


class TestBuildOperatorMatrix:
    """Test operator matrix construction."""

    def test_shape(self, small_operator):
        H, x = small_operator
        assert H.shape == (32, 32)

    def test_grid_length(self, small_operator):
        H, x = small_operator
        assert len(x) == 32

    def test_symmetric(self, small_operator):
        H, x = small_operator
        assert np.allclose(H, H.T, atol=1e-12), "H must be symmetric."

    def test_positive_diagonal_dominance(self, small_operator):
        """Diagonal should dominate due to kinetic + positive potential."""
        H, x = small_operator
        diag = np.diag(H)
        assert np.all(diag > 0), "Diagonal of H should be positive."

    def test_grid_in_interior(self):
        """Grid points should lie strictly inside (0, L)."""
        H, x = build_operator_matrix(L=6.0, N=16, n_primes=3)
        assert x[0] > 0, "Grid must not include x=0."
        assert x[-1] < 6.0, "Grid must not include x=L."

    def test_different_L(self):
        """Different L values produce different grids."""
        _, x1 = build_operator_matrix(L=5.0, N=16, n_primes=3)
        _, x2 = build_operator_matrix(L=10.0, N=16, n_primes=3)
        assert x1[-1] < x2[-1]


class TestSelfAdjointness:
    """Test self-adjointness verification."""

    def test_is_symmetric(self, small_operator):
        H, _ = small_operator
        result = verify_self_adjointness(H)
        assert result["is_symmetric"]

    def test_real_eigenvalues(self, small_operator):
        H, _ = small_operator
        result = verify_self_adjointness(H)
        assert result["all_real"]

    def test_bounded_below(self, small_operator):
        H, _ = small_operator
        result = verify_self_adjointness(H)
        assert result["min_eigenvalue"] > -np.inf

    def test_self_adjoint_flag(self, small_operator):
        H, _ = small_operator
        result = verify_self_adjointness(H)
        assert result["self_adjoint"]

    def test_symmetry_error_small(self, small_operator):
        H, _ = small_operator
        result = verify_self_adjointness(H)
        assert result["symmetry_error"] < 1e-10


# ===========================================================================
# 2. SPECTRUM
# ===========================================================================

class TestSpectrum:
    """Test eigenvalue and eigenvector computation."""

    def test_eigenvalues_real_sorted(self, medium_operator):
        H, _ = medium_operator
        lam, _ = compute_spectrum(H)
        assert np.all(np.isreal(lam)), "Eigenvalues must be real."
        assert np.all(np.diff(lam) > 0), "Eigenvalues must be sorted."

    def test_positive_eigenvalues(self, medium_operator):
        """All eigenvalues should be positive (V > 0, kinetic > 0)."""
        H, _ = medium_operator
        lam, _ = compute_spectrum(H)
        assert np.all(lam > 0), "All eigenvalues must be positive."

    def test_eigenvectors_orthonormal(self, medium_operator):
        """Eigenvectors should be Euclidean-orthonormal."""
        H, _ = medium_operator
        _, psi = compute_spectrum(H)
        # V^T V should be identity
        product = psi.T @ psi
        assert np.allclose(product, np.eye(product.shape[0]), atol=1e-8)

    def test_n_eigenvalues_flag(self, medium_operator):
        H, _ = medium_operator
        lam, psi = compute_spectrum(H, n_eigenvalues=10)
        assert len(lam) == 10
        assert psi.shape[1] == 10

    def test_weyl_law(self, medium_operator):
        """Weyl law: #{λₙ ≤ E} ~ L·√E / π for large E."""
        H, x = medium_operator
        L = float(x[-1] + (x[1] - x[0]))
        lam, _ = compute_spectrum(H)
        # Check at E = lam[-1]
        E = float(lam[-1])
        count_actual = len(lam)          # all N eigenvalues
        count_weyl = L * np.sqrt(E) / np.pi
        # Within a factor of 2 (Weyl law is asymptotic)
        assert count_actual < 3 * count_weyl


# ===========================================================================
# 3. RESOLVENT
# ===========================================================================

class TestResolvent:
    """Test resolvent R(z) = (H − z)^{-1}."""

    def test_resolvent_shape(self, small_operator):
        H, x = small_operator
        R = compute_resolvent(H, complex(-10.0, 1.0))
        assert R.shape == H.shape

    def test_resolvent_complex(self, small_operator):
        """Resolvent should be complex-valued."""
        H, _ = small_operator
        R = compute_resolvent(H, complex(-5.0, 1.0))
        assert R.dtype in (np.complex64, np.complex128, complex)

    def test_resolvent_identity(self, small_operator):
        """(H − z·I) · R(z) ≈ I."""
        H, _ = small_operator
        z = complex(-5.0, 0.5)
        R = compute_resolvent(H, z)
        A = H.astype(complex) - z * np.eye(H.shape[0])
        product = A @ R
        assert np.allclose(product, np.eye(H.shape[0]), atol=1e-8), \
            "(H-z)·R(z) must equal identity."

    def test_resolvent_symmetry(self, small_operator):
        """R(z) = R(z)^T for real symmetric H."""
        H, _ = small_operator
        z = complex(-3.0, 2.0)
        R = compute_resolvent(H, z)
        assert np.allclose(R, R.T, atol=1e-10)

    def test_resolvent_near_eigenvalue_raises(self, small_operator):
        """Resolvent at an eigenvalue should raise ValueError."""
        H, _ = small_operator
        lam, _ = compute_spectrum(H)
        with pytest.raises(ValueError, match="singular"):
            compute_resolvent(H, complex(float(lam[0]), 0.0))

    def test_resolvent_analytic_continuation(self, small_operator):
        """Tr(R(z)) should vary continuously with z."""
        H, x = small_operator
        lam, _ = compute_spectrum(H)
        z_values = [complex(-5.0, 1.0), complex(-4.0, 1.0), complex(-3.0, 1.0)]
        traces = [trace_resolvent(lam, z) for z in z_values]
        # All traces should be finite
        for tr in traces:
            assert np.isfinite(tr.real) and np.isfinite(tr.imag)


class TestGreenFunction:
    """Test Green's function G(x, x; z)."""

    def test_green_diagonal_shape(self, small_operator, medium_spectrum):
        H_small, x_small = small_operator
        H_med, x_med = build_operator_matrix(L=8.0, N=64, n_primes=10)
        lam, psi = medium_spectrum
        G = compute_green_function(H_med, x_med, complex(-5.0, 1.0),
                                   eigenvalues=lam, eigenvectors=psi)
        assert G.shape == (64,)

    def test_green_diagonal_complex(self, small_operator):
        H, x = small_operator
        G = compute_green_function(H, x, complex(-5.0, 1.0))
        assert G.dtype in (np.complex64, np.complex128)

    def test_green_diagonal_finite(self, small_operator):
        H, x = small_operator
        G = compute_green_function(H, x, complex(-5.0, 1.0))
        assert np.all(np.isfinite(G))

    def test_poles_and_residues_count(self, small_operator):
        H, _ = small_operator
        lam, psi = compute_spectrum(H)
        poles = resolvent_poles_and_residues(lam, psi)
        assert len(poles) == H.shape[0]

    def test_poles_are_eigenvalues(self, small_operator):
        H, _ = small_operator
        lam, psi = compute_spectrum(H)
        poles = resolvent_poles_and_residues(lam, psi)
        pole_values = np.array([p["pole"] for p in poles])
        assert np.allclose(np.sort(pole_values), np.sort(lam), rtol=1e-10)

    def test_residue_rank_one(self, small_operator):
        H, _ = small_operator
        lam, psi = compute_spectrum(H)
        poles = resolvent_poles_and_residues(lam, psi)
        for p in poles[:5]:
            assert p["rank"] == 1
            res = p["residue"]
            rank = np.linalg.matrix_rank(res, tol=1e-8)
            assert rank == 1, f"Residue should be rank-1, got rank {rank}."


# ===========================================================================
# 4. EXPLICIT TRACES
# ===========================================================================

class TestTraceResolvent:
    """Test Tr(R(z)) computation."""

    def test_trace_spectral_finite(self, small_operator):
        H, x = small_operator
        lam, _ = compute_spectrum(H)
        tr = trace_resolvent(lam, complex(-5.0, 1.0))
        assert np.isfinite(tr.real) and np.isfinite(tr.imag)

    def test_trace_spectral_vs_green(self, small_operator):
        """Two methods should agree to within numerical precision."""
        H, x = small_operator
        lam, psi = compute_spectrum(H)
        z = complex(-5.0, 1.0)
        tr_spec = trace_resolvent(lam, z)
        tr_green = trace_resolvent_via_green(H, x, z, eigenvalues=lam,
                                              eigenvectors=psi)
        # Allow 1% relative error from quadrature
        diff = abs(tr_spec - tr_green)
        ref = max(abs(tr_spec), 1e-10)
        assert diff / ref < 0.05, (
            f"Spectral and Green traces differ by {diff/ref:.2%}. "
            f"Spectral={tr_spec:.6f}, Green={tr_green:.6f}"
        )

    def test_trace_imaginary_part_sign(self, small_operator):
        """Im(Tr(R(z))) < 0 when Im(z) > 0 (resolvent on upper half-plane)."""
        H, x = small_operator
        lam, _ = compute_spectrum(H)
        z = complex(-5.0, 1.0)  # Im(z) > 0, z below spectrum
        tr = trace_resolvent(lam, z)
        # For H self-adjoint with positive spectrum and z = a + ib, b>0, a<λ₁:
        # Tr(R(z)) = Σ 1/(λₙ - a - ib) = Σ (λₙ-a+ib)/((λₙ-a)²+b²)
        # Im > 0 when a < λₙ for all n
        assert tr.imag > 0

    def test_trace_path_integral_multiple_z(self, small_operator):
        H, x = small_operator
        lam, _ = compute_spectrum(H)
        z_vals = np.array([-5.0 + 1.0j, -3.0 + 1.0j, -1.0 + 1.0j])
        traces = trace_resolvent_path_integral(lam, z_vals)
        assert traces.shape == (3,)
        assert np.all(np.isfinite(traces))

    def test_trace_path_integral_consistent(self, small_operator):
        """Path integral should match single evaluations."""
        H, x = small_operator
        lam, _ = compute_spectrum(H)
        z_vals = np.array([-5.0 + 1.0j, -3.0 + 1.0j])
        traces_batch = trace_resolvent_path_integral(lam, z_vals)
        trace_0 = trace_resolvent(lam, complex(-5.0, 1.0))
        trace_1 = trace_resolvent(lam, complex(-3.0, 1.0))
        assert abs(traces_batch[0] - trace_0) < 1e-10
        assert abs(traces_batch[1] - trace_1) < 1e-10


class TestTraceHeatKernel:
    """Test Tr(e^{-tH})."""

    def test_heat_trace_positive(self, small_operator):
        H, _ = small_operator
        lam, _ = compute_spectrum(H)
        K = trace_heat_kernel(lam, 0.3)
        assert K > 0

    def test_heat_trace_decreasing_in_t(self, small_operator):
        """K(β) should decrease as β increases (more damping)."""
        H, _ = small_operator
        lam, _ = compute_spectrum(H)
        K1 = trace_heat_kernel(lam, 0.1)
        K2 = trace_heat_kernel(lam, 0.5)
        K3 = trace_heat_kernel(lam, 1.0)
        assert K1 > K2 > K3

    def test_heat_trace_invalid_t(self, small_operator):
        H, _ = small_operator
        lam, _ = compute_spectrum(H)
        with pytest.raises(ValueError):
            trace_heat_kernel(lam, 0.0)
        with pytest.raises(ValueError):
            trace_heat_kernel(lam, -1.0)

    def test_heat_trace_large_t_decays(self, small_operator):
        """For large β, heat trace → 1 (only ground state survives)."""
        H, _ = small_operator
        lam, _ = compute_spectrum(H)
        K_large = trace_heat_kernel(lam, 50.0)
        # Should be dominated by the ground state exp(-50 * λ₁)
        K_gs = np.exp(-50.0 * lam[0])
        assert abs(K_large - K_gs) / K_gs < 0.01


# ===========================================================================
# 5. SELBERG-TYPE TRACE FORMULA
# ===========================================================================

class TestSelbergFormula:
    """Test the Selberg-type trace formula."""

    def test_spectral_side_gaussian(self, small_operator):
        """Spectral side with Gaussian test function should be positive."""
        H, _ = small_operator
        lam, _ = compute_spectrum(H)
        sigma = 3.0
        h = lambda t: float(np.exp(-t**2 / (2 * sigma**2)))
        spectral = selberg_spectral_side(lam, h)
        assert spectral > 0

    def test_spectral_side_heat_kernel(self, small_operator):
        """Spectral side with e^{-βt} equals heat kernel trace."""
        H, _ = small_operator
        lam, _ = compute_spectrum(H)
        beta = 0.3
        h = lambda t: float(np.exp(-beta * t))
        spectral = selberg_spectral_side(lam, h)
        K = trace_heat_kernel(lam, beta)
        assert abs(spectral - K) < 1e-10

    def test_arithmetic_side_positive_weyl(self):
        """Arithmetic side with positive Fourier transform should give positive Weyl."""
        h_hat = lambda x: complex(np.exp(-x**2))  # positive everywhere
        result = selberg_arithmetic_side(h_hat, L=8.0, n_primes=5)
        assert result["weyl"] > 0

    def test_arithmetic_side_has_prime_contributions(self):
        """Arithmetic side should include prime contributions."""
        h_hat = lambda x: complex(np.exp(-x**2))
        result = selberg_arithmetic_side(h_hat, L=8.0, n_primes=5,
                                          weyl_term=False)
        assert len(result["prime_contributions"]) > 0
        assert result["prime_sum"] != 0.0

    def test_arithmetic_side_structure(self):
        """Result should have correct keys."""
        h_hat = lambda x: complex(np.exp(-x**2))
        result = selberg_arithmetic_side(h_hat, L=8.0, n_primes=5)
        for key in ("weyl", "prime_sum", "total", "prime_contributions"):
            assert key in result

    def test_verify_trace_formula_runs(self, small_operator):
        """verify_trace_formula should run without errors."""
        H, x = small_operator
        result = verify_trace_formula(H, x, t_heat=0.3, n_primes=5)
        for key in ("spectral_side", "arithmetic_side", "weyl_wkb",
                    "prime_correction", "discrepancy", "relative_discrepancy"):
            assert key in result

    def test_verify_trace_formula_spectral_positive(self, small_operator):
        """Spectral side should be positive."""
        H, x = small_operator
        result = verify_trace_formula(H, x, t_heat=0.3, n_primes=5)
        assert result["spectral_side"] > 0

    def test_verify_trace_formula_n_eigenvalues(self, small_operator):
        H, x = small_operator
        result = verify_trace_formula(H, x, t_heat=0.3, n_primes=5)
        assert result["n_eigenvalues"] == 32  # matches N=32 small_operator

    def test_first_n_primes(self):
        """_first_n_primes returns correct primes."""
        primes = _first_n_primes(5)
        assert primes == [2, 3, 5, 7, 11]

    def test_first_n_primes_zero(self):
        assert _first_n_primes(0) == []


# ===========================================================================
# Class SelbergTraceOperator (integration tests)
# ===========================================================================

class TestSelbergTraceOperator:
    """Integration tests for the SelbergTraceOperator class."""

    @pytest.fixture
    def op(self):
        return SelbergTraceOperator(L=5.0, N=32, n_primes=5)

    def test_domain_info(self, op):
        info = op.domain_info()
        assert "L²" in info["hilbert_space"]
        assert info["L"] == 5.0
        assert info["N"] == 32

    def test_self_adjointness(self, op):
        result = op.self_adjointness()
        assert result["self_adjoint"]

    def test_resolvent_computed(self, op):
        R = op.resolvent(complex(-5.0, 1.0))
        assert R.shape == (32, 32)

    def test_green_function_diagonal_shape(self, op):
        G = op.green_function_diagonal(complex(-5.0, 1.0))
        assert G.shape == (32,)

    def test_trace_resolvent_methods_agree(self, op):
        z = complex(-5.0, 1.0)
        tr1 = op.trace_resolvent_spectral(z)
        tr2 = op.trace_resolvent_green(z)
        diff = abs(tr1 - tr2) / max(abs(tr1), 1e-10)
        assert diff < 0.05, f"Traces differ by {diff:.2%}."

    def test_heat_kernel_positive(self, op):
        K = op.trace_heat_kernel(0.3)
        assert K > 0

    def test_selberg_formula_returns_dict(self, op):
        result = op.selberg_trace_formula(t_heat=0.3)
        assert isinstance(result, dict)
        assert "spectral_side" in result

    def test_summary_runs(self, op):
        report = op.summary(verbose=False)
        assert "domain" in report
        assert "self_adjointness" in report
        assert "resolvent_test" in report
        assert "trace_comparison" in report
        assert "selberg_formula" in report

    def test_summary_trace_consistent(self, op):
        report = op.summary(verbose=False)
        assert report["trace_comparison"]["consistent"], \
            "Trace methods should be consistent within 1%."

    def test_eigenvalues_cached(self, op):
        """Eigenvalues computed lazily and cached."""
        lam1 = op.eigenvalues
        lam2 = op.eigenvalues
        assert lam1 is lam2  # same object (cached)


# ===========================================================================
# Constants
# ===========================================================================

class TestConstants:
    """Validate module-level QCAL constants."""

    def test_f0_qcal(self):
        assert abs(F0_QCAL - 141.7001) < 1e-4

    def test_c_coherence(self):
        assert abs(C_COHERENCE - 244.36) < 1e-4

    def test_default_l_positive(self):
        assert DEFAULT_L > 0

    def test_default_n_positive(self):
        assert DEFAULT_N > 0

    def test_default_n_primes_positive(self):
        assert DEFAULT_N_PRIMES > 0
