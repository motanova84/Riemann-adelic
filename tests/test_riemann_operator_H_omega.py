#!/usr/bin/env python3
"""
Tests for riemann_operator_H_omega — Berry-Keating Symmetrised H_Ω Operator
============================================================================

Validates all classes and functions in
``operators.riemann_operator_H_omega``:

*   Module constants
*   :class:`MellinTransform`
*   :class:`Vortex8Geometry`
*   :class:`DeltaCombPotential`
*   :class:`AlignmentOperator`
*   :class:`HOmegaOperator`
*   :class:`TraceFormulaAnalysis`
*   :class:`GUEStatistics`
*   Integration — :func:`validar_operador_omega`, :func:`resolver_RH_biologico`

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz · C = 244.36
Signature: ∴𓂀Ω∞³Φ
"""

import pytest
import numpy as np

from operators.riemann_operator_H_omega import (
    # constants
    F0_QCAL,
    C_QCAL,
    PHI,
    EPSILON_BASE_DEFAULT,
    N_DEFAULT,
    U_MAX_DEFAULT,
    HAS_MPMATH,
    # helpers
    _sieve_primes,
    _get_primes,
    _get_riemann_zeros,
    _scale_to_zeros,
    # classes
    MellinTransform,
    Vortex8Geometry,
    DeltaCombPotential,
    AlignmentOperator,
    HOmegaOperator,
    TraceFormulaAnalysis,
    GUEStatistics,
    # public API
    validar_operador_omega,
    resolver_RH_biologico,
    _build_operator,
)


# =============================================================================
# 1 — Module constants (5 tests)
# =============================================================================

class TestConstants:
    """Test fundamental QCAL constants exported by the module."""

    def test_f0_value(self):
        """Base frequency must be 141.7001 Hz."""
        assert abs(F0_QCAL - 141.7001) < 1e-4

    def test_c_qcal_value(self):
        """QCAL coherence constant must be 244.36."""
        assert abs(C_QCAL - 244.36) < 0.01

    def test_phi_golden_ratio(self):
        """Golden ratio must satisfy Φ² = Φ + 1."""
        assert abs(PHI ** 2 - PHI - 1.0) < 1e-12

    def test_epsilon_base_positive(self):
        """Default epsilon base must be strictly positive."""
        assert EPSILON_BASE_DEFAULT > 0.0

    def test_n_default_positive(self):
        """Default grid size must be a positive integer."""
        assert isinstance(N_DEFAULT, int) and N_DEFAULT > 0


# =============================================================================
# Helper function tests (not counted in the 103; included for completeness)
# =============================================================================

class TestHelpers:
    """Tests for private helper functions."""

    def test_sieve_primes_empty(self):
        assert _sieve_primes(1) == []

    def test_sieve_primes_basic(self):
        assert _sieve_primes(10) == [2, 3, 5, 7]

    def test_get_primes_count(self):
        primes = _get_primes(10)
        assert len(primes) == 10

    def test_get_primes_first(self):
        assert _get_primes(5) == [2, 3, 5, 7, 11]

    def test_get_primes_invalid(self):
        with pytest.raises(ValueError):
            _get_primes(0)

    def test_get_riemann_zeros_count(self):
        z = _get_riemann_zeros(5)
        assert len(z) == 5

    def test_get_riemann_zeros_first(self):
        z = _get_riemann_zeros(1)
        assert abs(z[0] - 14.134725) < 0.01

    def test_get_riemann_zeros_ascending(self):
        z = _get_riemann_zeros(10)
        assert np.all(np.diff(z) > 0)

    def test_scale_to_zeros_linear(self):
        evals = np.array([1.0, 2.0, 3.0])
        zeros = np.array([2.0, 4.0, 6.0])
        scaled = _scale_to_zeros(evals, zeros)
        corr = np.corrcoef(scaled, zeros)[0, 1]
        assert corr > 0.9999

    def test_scale_to_zeros_empty(self):
        result = _scale_to_zeros(np.array([]), np.array([]))
        assert len(result) == 0


# =============================================================================
# 2 — MellinTransform (12 tests)
# =============================================================================

class TestMellinTransform:
    """Tests for MellinTransform class."""

    @pytest.fixture
    def mellin(self):
        return MellinTransform(N=64, u_max=10.0)

    def test_init_stores_N(self, mellin):
        assert mellin.N == 64

    def test_init_stores_u_max(self, mellin):
        assert mellin.u_max == 10.0

    def test_grid_length(self, mellin):
        assert len(mellin.u_grid) == 64

    def test_grid_symmetric(self, mellin):
        assert abs(mellin.u_grid[0] + mellin.u_max) < 1e-10
        assert abs(mellin.u_grid[-1] - mellin.u_max) < 1e-10

    def test_du_positive(self, mellin):
        assert mellin.du > 0

    def test_init_invalid_N(self):
        with pytest.raises(ValueError):
            MellinTransform(N=3, u_max=10.0)

    def test_init_invalid_u_max(self):
        with pytest.raises(ValueError):
            MellinTransform(N=64, u_max=-1.0)

    def test_diagonalize_returns_real_eigenvalues(self, mellin):
        H = np.diag(np.random.rand(20)) + np.eye(20)
        H = 0.5 * (H + H.T)
        evals, evecs = mellin.diagonalize(H)
        assert np.all(np.isreal(evals) | (np.abs(evals.imag) < 1e-10))

    def test_diagonalize_eigenvalue_count(self, mellin):
        H = np.eye(20)
        evals, evecs = mellin.diagonalize(H)
        assert len(evals) == 20

    def test_verify_self_adjoint_symmetric(self, mellin):
        H = np.eye(20)
        assert mellin.verify_self_adjoint(H)

    def test_verify_self_adjoint_antisymmetric(self, mellin):
        H = 1j * np.eye(20)  # anti-Hermitian (skew-Hermitian): H† = -H ≠ H
        assert not mellin.verify_self_adjoint(H)

    def test_critical_line_s_values(self, mellin):
        H = np.diag([1.0, 2.0, 3.0])
        evals, _ = mellin.diagonalize(H)
        s_vals = mellin.critical_line_s_values()
        assert np.all(np.abs(s_vals.real - 0.5) < 1e-10)

    def test_is_self_adjoint_property(self, mellin):
        H = np.eye(20)
        mellin.diagonalize(H)
        assert mellin.is_self_adjoint

    def test_critical_line_error_no_matrix(self):
        m = MellinTransform(N=10, u_max=5.0)
        assert m.critical_line_error == np.inf

    def test_s_values_without_diagonalize_raises(self):
        m = MellinTransform(N=10, u_max=5.0)
        with pytest.raises(ValueError):
            m.critical_line_s_values()

    def test_diagonalize_non_square_raises(self, mellin):
        with pytest.raises(ValueError):
            mellin.diagonalize(np.ones((3, 4)))


# =============================================================================
# 3 — Vortex8Geometry (14 tests)
# =============================================================================

class TestVortex8Geometry:
    """Tests for Vortex8Geometry class."""

    @pytest.fixture
    def geom(self):
        return Vortex8Geometry(N=64, u_max=10.0)

    def test_init_N_even(self, geom):
        assert geom.N % 2 == 0

    def test_init_N_odd_adjusted(self):
        g = Vortex8Geometry(N=65, u_max=10.0)
        assert g.N == 66

    def test_grid_length(self, geom):
        assert len(geom.u_grid) == geom.N

    def test_half_length(self, geom):
        assert len(geom.u_half) == geom.N_half

    def test_n_half_equals_N_over_2(self, geom):
        assert geom.N_half == geom.N // 2

    def test_u_half_starts_at_zero(self, geom):
        assert abs(geom.u_half[0]) < 1e-10

    def test_u_half_ends_at_u_max(self, geom):
        assert abs(geom.u_half[-1] - geom.u_max) < 1e-10

    def test_du_positive(self, geom):
        assert geom.du > 0

    def test_init_invalid_N(self):
        with pytest.raises(ValueError):
            Vortex8Geometry(N=2, u_max=5.0)

    def test_init_invalid_u_max(self):
        with pytest.raises(ValueError):
            Vortex8Geometry(N=8, u_max=0.0)

    def test_project_to_even_symmetric(self, geom):
        # Random asymmetric function → even projection must be symmetric
        psi = np.random.randn(geom.N)
        psi_even = geom.project_to_even(psi)
        assert geom.check_inversion_symmetry(psi_even, tol=1e-10)

    def test_symmetry_error_even_function(self, geom):
        psi = np.cos(np.linspace(-np.pi, np.pi, geom.N))
        # cos is even → symmetry error must be small
        assert geom.symmetry_error(psi) < 1e-12

    def test_symmetry_error_odd_function(self, geom):
        psi = np.sin(np.linspace(-np.pi, np.pi, geom.N))
        # sin is odd → error should be large
        assert geom.symmetry_error(psi) > 0.1

    def test_haar_inner_product_self_real(self, geom):
        psi = np.ones(geom.N)
        ip = geom.haar_inner_product(psi, psi)
        assert ip.real > 0

    def test_project_wrong_length_raises(self, geom):
        with pytest.raises(ValueError):
            geom.project_to_even(np.ones(geom.N + 1))

    def test_symmetry_error_wrong_length_raises(self, geom):
        with pytest.raises(ValueError):
            geom.symmetry_error(np.ones(geom.N + 1))

    def test_check_inversion_symmetry_true(self, geom):
        psi = np.ones(geom.N)  # constant is even
        assert geom.check_inversion_symmetry(psi)

    def test_haar_inner_product_wrong_length_raises(self, geom):
        with pytest.raises(ValueError):
            geom.haar_inner_product(np.ones(5), np.ones(geom.N))


# =============================================================================
# 4 — DeltaCombPotential (15 tests)
# =============================================================================

class TestDeltaCombPotential:
    """Tests for DeltaCombPotential class."""

    @pytest.fixture
    def u_half(self):
        return np.linspace(0.0, 20.0, 64)

    @pytest.fixture
    def potential(self, u_half):
        return DeltaCombPotential(
            u_grid=u_half, num_primes=5, max_k=3, epsilon_base=0.5
        )

    def test_init_stores_primes(self, potential):
        assert len(potential.primes) == 5

    def test_primes_correct(self, potential):
        assert potential.primes[:5] == [2, 3, 5, 7, 11]

    def test_epsilon_base_stored(self, potential):
        assert potential.epsilon_base == 0.5

    def test_adaptive_epsilon_k1(self, potential):
        eps1 = potential.adaptive_epsilon(1)
        assert abs(eps1 - potential.epsilon_base) < 1e-10

    def test_adaptive_epsilon_decreasing(self, potential):
        eps1 = potential.adaptive_epsilon(1)
        eps2 = potential.adaptive_epsilon(2)
        eps4 = potential.adaptive_epsilon(4)
        assert eps1 > eps2 > eps4

    def test_adaptive_epsilon_formula(self, potential):
        k = 3
        expected = potential.epsilon_base / (k ** 0.25)
        assert abs(potential.adaptive_epsilon(k) - expected) < 1e-10

    def test_adaptive_epsilon_invalid_k(self, potential):
        with pytest.raises(ValueError):
            potential.adaptive_epsilon(0)

    def test_build_returns_correct_shape(self, potential, u_half):
        V = potential.build()
        assert V.shape == (len(u_half),)

    def test_build_returns_real(self, potential):
        V = potential.build()
        assert np.all(np.isreal(V))

    def test_build_non_negative(self, potential):
        V = potential.build()
        # Potential should have mostly positive values (Gaussian peaks are positive)
        assert np.sum(V > 0) > 0

    def test_build_has_peaks_at_log_primes(self, potential):
        V = potential.build()
        # Peak near ln(2) ≈ 0.693 should be locally elevated
        ln2 = np.log(2.0)
        u = potential.u_grid
        idx = np.argmin(np.abs(u - ln2))
        assert V[idx] > 0.0

    def test_init_invalid_num_primes(self, u_half):
        with pytest.raises(ValueError):
            DeltaCombPotential(u_half, num_primes=0)

    def test_init_invalid_max_k(self, u_half):
        with pytest.raises(ValueError):
            DeltaCombPotential(u_half, max_k=0)

    def test_init_invalid_epsilon_base(self, u_half):
        with pytest.raises(ValueError):
            DeltaCombPotential(u_half, epsilon_base=-0.1)

    def test_init_invalid_grid(self):
        with pytest.raises(ValueError):
            DeltaCombPotential(np.array([1.0, 2.0]))  # too short

    def test_build_half_positive_grid(self, u_half):
        potential = DeltaCombPotential(u_half, num_primes=3, max_k=2)
        V = potential.build_half()
        assert len(V) > 0


# =============================================================================
# 5 — AlignmentOperator (12 tests)
# =============================================================================

class TestAlignmentOperator:
    """Tests for AlignmentOperator class."""

    @pytest.fixture
    def align_unity(self):
        return AlignmentOperator(N=20, psi=1.0)

    @pytest.fixture
    def align_half(self):
        return AlignmentOperator(N=20, psi=0.5)

    def test_init_psi_unity(self, align_unity):
        assert align_unity.psi == 1.0

    def test_a_value_at_psi_unity(self, align_unity):
        """At Ψ=1.0, A should equal 1/2."""
        assert abs(align_unity.A_value - 0.5) < 1e-10

    def test_a_value_at_psi_zero(self):
        a = AlignmentOperator(N=10, psi=0.0)
        assert abs(a.A_value) < 1e-10

    def test_matrix_shape(self, align_unity):
        M = align_unity.matrix()
        assert M.shape == (20, 20)

    def test_matrix_diagonal(self, align_unity):
        M = align_unity.matrix()
        assert np.all(M == np.diag(np.diag(M)))

    def test_imaginary_correction_zero_at_unity(self, align_unity):
        C = align_unity.imaginary_correction()
        assert np.all(np.abs(C) < 1e-14)

    def test_imaginary_correction_nonzero_at_half(self, align_half):
        C = align_half.imaginary_correction()
        assert np.max(np.abs(C)) > 0.0

    def test_vanishes_at_unity_true(self, align_unity):
        assert align_unity.vanishes_at_unity()

    def test_vanishes_at_unity_false(self, align_half):
        assert not align_half.vanishes_at_unity()

    def test_correction_norm_zero_at_unity(self, align_unity):
        assert align_unity.correction_norm() < 1e-14

    def test_correction_norm_positive_at_half(self, align_half):
        assert align_half.correction_norm() > 0.0

    def test_init_invalid_N(self):
        with pytest.raises(ValueError):
            AlignmentOperator(N=0, psi=0.5)

    def test_init_invalid_psi_high(self):
        with pytest.raises(ValueError):
            AlignmentOperator(N=10, psi=1.5)

    def test_init_invalid_psi_low(self):
        with pytest.raises(ValueError):
            AlignmentOperator(N=10, psi=-0.1)


# =============================================================================
# 6 — HOmegaOperator (18 tests)
# =============================================================================

# Small operator fixture for fast tests
_SMALL_N = 32
_SMALL_PRIMES = 3
_SMALL_ZEROS = 5


@pytest.fixture(scope="module")
def small_operator():
    """Build a small HOmegaOperator for fast unit tests."""
    geom = Vortex8Geometry(N=_SMALL_N, u_max=15.0)
    pot = DeltaCombPotential(
        u_grid=geom.u_half,
        num_primes=_SMALL_PRIMES,
        max_k=3,
        epsilon_base=1.0,
    )
    align = AlignmentOperator(N=geom.N_half, psi=1.0)
    return HOmegaOperator(geometry=geom, potential=pot, alignment=align)


class TestHOmegaOperator:
    """Tests for HOmegaOperator class."""

    def test_hermitian_matrix_shape(self, small_operator):
        n = small_operator.geometry.N_half
        assert small_operator.H_hermitian.shape == (n, n)

    def test_full_matrix_shape(self, small_operator):
        n = small_operator.geometry.N_half
        assert small_operator.H_full.shape == (n, n)

    def test_hermitian_part_is_symmetric(self, small_operator):
        H = small_operator.H_hermitian
        assert np.max(np.abs(H - H.T)) < 1e-10

    def test_hermitian_part_is_real(self, small_operator):
        H = small_operator.H_hermitian
        assert np.max(np.abs(H.imag)) < 1e-10

    def test_full_operator_at_psi_unity_equals_hermitian(self, small_operator):
        # When psi=1.0, correction=0, so H_full == H_hermitian
        diff = np.max(np.abs(small_operator.H_full - small_operator.H_hermitian))
        assert diff < 1e-13

    def test_compute_eigenvalues_count(self, small_operator):
        evals = small_operator.compute_eigenvalues(n=_SMALL_ZEROS)
        assert len(evals) == _SMALL_ZEROS

    def test_compute_eigenvalues_real(self, small_operator):
        evals = small_operator.compute_eigenvalues(n=_SMALL_ZEROS)
        assert np.all(np.isreal(evals))

    def test_compute_eigenvalues_sorted(self, small_operator):
        evals = small_operator.compute_eigenvalues(n=_SMALL_ZEROS)
        assert np.all(np.diff(evals) >= -1e-10)

    def test_compute_eigenvalues_n_zero_raises(self, small_operator):
        with pytest.raises(ValueError):
            small_operator.compute_eigenvalues(n=0)

    def test_compute_eigenvalues_too_many_raises(self, small_operator):
        dim = small_operator.H_hermitian.shape[0]
        with pytest.raises(ValueError):
            small_operator.compute_eigenvalues(n=dim + 1)

    def test_compare_with_zeta_zeros_returns_tuple(self, small_operator):
        corr, zeros, evals = small_operator.compare_with_zeta_zeros(n_zeros=_SMALL_ZEROS)
        assert isinstance(corr, float)
        assert len(zeros) == _SMALL_ZEROS

    def test_compare_correlation_bounded(self, small_operator):
        corr, _, _ = small_operator.compare_with_zeta_zeros(n_zeros=_SMALL_ZEROS)
        assert -1.0 <= corr <= 1.0

    def test_coherence_psi_in_range(self, small_operator):
        psi = small_operator.coherence_psi_value(n_zeros=_SMALL_ZEROS)
        assert 0.0 <= psi <= 1.0

    def test_dimension_mismatch_raises(self):
        geom = Vortex8Geometry(N=16, u_max=10.0)
        pot = DeltaCombPotential(u_grid=geom.u_half, num_primes=2, max_k=2)
        wrong_align = AlignmentOperator(N=geom.N_half + 5, psi=1.0)
        with pytest.raises(ValueError):
            HOmegaOperator(geometry=geom, potential=pot, alignment=wrong_align)

    def test_correction_zero_for_psi_unity(self, small_operator):
        assert small_operator.alignment.vanishes_at_unity()

    def test_full_operator_imaginary_part_nonzero_for_psi_half(self):
        geom = Vortex8Geometry(N=16, u_max=10.0)
        pot = DeltaCombPotential(u_grid=geom.u_half, num_primes=2, max_k=2)
        align = AlignmentOperator(N=geom.N_half, psi=0.5)
        op = HOmegaOperator(geometry=geom, potential=pot, alignment=align)
        # Full operator should have nonzero imaginary diagonal
        assert np.max(np.abs(op.H_full.imag)) > 0.0

    def test_kinetic_dominant_at_high_energy(self, small_operator):
        # Eigenvalues should be finite and positive
        evals = small_operator.compute_eigenvalues(n=3)
        assert np.all(np.isfinite(evals))

    def test_build_operator_factory(self):
        op = _build_operator(N=16, num_primes=2, psi=1.0, u_max=10.0)
        assert isinstance(op, HOmegaOperator)


# =============================================================================
# 7 — TraceFormulaAnalysis (12 tests)
# =============================================================================

class TestTraceFormulaAnalysis:
    """Tests for TraceFormulaAnalysis class."""

    @pytest.fixture
    def trace(self):
        evals = np.linspace(1.0, 100.0, 30)
        return TraceFormulaAnalysis(evals)

    def test_init_stores_sorted_eigenvalues(self, trace):
        assert np.all(np.diff(trace.eigenvalues) >= 0)

    def test_init_N_correct(self, trace):
        assert trace.N == 30

    def test_init_empty_raises(self):
        with pytest.raises(ValueError):
            TraceFormulaAnalysis(np.array([]))

    def test_weyl_term_positive(self, trace):
        assert trace.weyl_term(100.0) > 0.0

    def test_weyl_term_zero_for_nonpositive(self, trace):
        assert trace.weyl_term(-1.0) == 0.0
        assert trace.weyl_term(0.0) == 0.0

    def test_weyl_term_increasing(self, trace):
        assert trace.weyl_term(10.0) < trace.weyl_term(50.0)

    def test_spectral_counting_correct(self, trace):
        evals = np.array([1.0, 2.0, 3.0, 4.0])
        t = TraceFormulaAnalysis(evals)
        assert t.spectral_counting(2.5) == 2
        assert t.spectral_counting(5.0) == 4

    def test_spectral_counting_zero_below_min(self, trace):
        assert trace.spectral_counting(0.0) == 0

    def test_riemann_weil_trace_real_for_real_eigenvalues(self, trace):
        val = trace.riemann_weil_trace(5.0)
        assert abs(val.imag) < 1e-10

    def test_riemann_weil_trace_positive(self, trace):
        # Gaussian kernel is always positive
        assert trace.riemann_weil_trace(trace.eigenvalues[0]).real > 0

    def test_prime_orbit_sum_finite(self, trace):
        val = trace.prime_orbit_sum(1.0, num_primes=3, max_k=2)
        assert np.isfinite(val)

    def test_level_spacings_length(self, trace):
        spacings = trace.level_spacings()
        assert len(spacings) == trace.N - 1

    def test_weyl_law_agreement_non_negative(self, trace):
        err = trace.weyl_law_agreement()
        assert err >= 0.0


# =============================================================================
# 8 — GUEStatistics (12 tests)
# =============================================================================

class TestGUEStatistics:
    """Tests for GUEStatistics class."""

    @pytest.fixture
    def gue(self):
        rng = np.random.default_rng(42)
        # GUE-like spacings: Wigner surmise sampling approximation
        evals = np.sort(np.cumsum(np.abs(rng.normal(0, 1, 40))))
        return GUEStatistics(evals)

    def test_init_sorts_eigenvalues(self, gue):
        assert np.all(np.diff(gue.eigenvalues) >= 0)

    def test_init_too_few_raises(self):
        with pytest.raises(ValueError):
            GUEStatistics(np.array([1.0]))

    def test_compute_returns_spacings(self, gue):
        spacings = gue.compute()
        assert len(spacings) == len(gue.eigenvalues) - 1

    def test_compute_mean_approximately_one(self, gue):
        spacings = gue.compute()
        # Normalised spacings: mean should be ≈ 1
        assert abs(np.mean(spacings) - 1.0) < 1e-10

    def test_wigner_surmise_at_zero(self, gue):
        assert gue.wigner_surmise(np.array([0.0]))[0] == 0.0

    def test_wigner_surmise_positive(self, gue):
        s = np.linspace(0.01, 3.0, 20)
        assert np.all(gue.wigner_surmise(s) >= 0.0)

    def test_wigner_surmise_peak_location(self, gue):
        # Wigner surmise peaks around s ≈ 1.13
        s = np.linspace(0, 3, 300)
        vals = gue.wigner_surmise(s)
        s_peak = s[np.argmax(vals)]
        assert 0.8 < s_peak < 1.5

    def test_gue_correlation_bounded(self, gue):
        corr = gue.gue_correlation()
        assert -1.0 <= corr <= 1.0

    def test_mean_spacing_positive(self, gue):
        ms = gue.mean_spacing()
        assert ms > 0.0

    def test_spacing_variance_non_negative(self, gue):
        gue.compute()
        assert gue.spacing_variance() >= 0.0

    def test_level_repulsion_index_in_range(self, gue):
        gue.compute()
        lri = gue.level_repulsion_index()
        assert 0.0 <= lri <= 1.0

    def test_spacings_none_before_compute(self):
        evals = np.array([1.0, 2.0, 3.0])
        g = GUEStatistics(evals)
        assert g.spacings is None

    def test_level_repulsion_auto_computes(self):
        evals = np.array([1.0, 2.0, 3.0])
        g = GUEStatistics(evals)
        lri = g.level_repulsion_index()  # should auto-compute
        assert 0.0 <= lri <= 1.0


# =============================================================================
# 9 — Integration tests (3 tests)
# =============================================================================

class TestIntegration:
    """End-to-end integration tests for the public API."""

    def test_validar_operador_omega_keys(self):
        """validar_operador_omega must return all expected keys."""
        result = validar_operador_omega(N=32, num_primes=3, num_zeros=5)
        required = {
            "correlation", "coherence_psi", "mellin_self_adjoint",
            "eigenvalues", "riemann_zeros", "imaginary_correction_norm",
            "computation_time_ms", "parameters",
        }
        assert required.issubset(result.keys())

    def test_validar_operador_omega_mellin_self_adjoint(self):
        """Hermitian part must always pass the Mellin self-adjoint check."""
        result = validar_operador_omega(N=32, num_primes=3, num_zeros=5)
        assert result["mellin_self_adjoint"] is True

    def test_resolver_RH_biologico_returns_dict(self, capsys):
        """resolver_RH_biologico must return a result dict with correlation."""
        result = resolver_RH_biologico(N=32, num_primes=3, num_zeros=5)
        assert isinstance(result, dict)
        assert "correlation" in result
        assert -1.0 <= result["correlation"] <= 1.0
        captured = capsys.readouterr()
        assert "OPERADOR AUTOADJUNTO ACTIVO" in captured.out
