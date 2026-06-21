#!/usr/bin/env python3
"""
Tests for NodoZero, BifurcacionCuantica & VortexToroidal
=========================================================

Validates the three geometric extensions of the Vortex 8 framework:

1. NodoZero — Phase Inflection Point at x = 1
2. BifurcacionCuantica — Quantum Bifurcation (±γₙ dual branches)
3. VortexToroidal — 4D+ toroidal evolution of the figure-8

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz · C = 244.36
Signature: ∴𓂀Ω∞³Φ
"""

import numpy as np
import pytest
from numpy.testing import assert_allclose

from operators.nodo_zero_toroidal import (
    # Classes
    NodoZero,
    NodoZeroResult,
    BifurcacionCuantica,
    BifurcacionResult,
    VortexToroidal,
    VortexToroidalResult,
    # Convenience function
    compute_nodo_zero_full,
    # Constants
    F0_QCAL,
    C_COHERENCE_QCAL,
    C_PRIMARY_QCAL,
    OMEGA_0_QCAL,
)


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

@pytest.fixture
def symmetric_grid():
    """Symmetric logarithmic grid centred at x=1."""
    N = 51
    log_x = np.linspace(-5.0, 5.0, N)
    x = np.exp(log_x)
    return x, log_x


@pytest.fixture
def toy_operator(symmetric_grid):
    """Diagonal self-adjoint operator with eigenvalues ±γₙ."""
    x, _ = symmetric_grid
    N = len(x)
    # 10 positive zeros (approximate Riemann zeros) + 10 negatives + 1 zero mode
    gammas = np.array([14.13, 21.02, 25.01, 30.42, 32.93,
                       37.59, 40.92, 43.33, 48.00, 49.77])
    spectrum = np.concatenate([-gammas[::-1], [0.0], gammas])
    # Pad to size N with linearly spaced values
    if len(spectrum) < N:
        extra = np.linspace(55.0, 55.0 + (N - len(spectrum)) * 5, N - len(spectrum))
        spectrum = np.concatenate([spectrum, extra])
    spectrum = spectrum[:N]

    rng = np.random.RandomState(0)
    Q, _ = np.linalg.qr(rng.randn(N, N))
    H = Q @ np.diag(spectrum) @ Q.T
    H = 0.5 * (H + H.T)  # enforce symmetry
    return x, H


@pytest.fixture
def symmetric_spectrum():
    """Pure ±γₙ spectrum for bifurcation tests."""
    gammas = np.array([14.13, 21.02, 25.01, 30.42, 32.93])
    return np.concatenate([-gammas[::-1], gammas])


# ===========================================================================
# TestNodoZero
# ===========================================================================

class TestNodoZero:
    """Tests for the NodoZero (Phase Inflection Point) class."""

    def test_returns_correct_result_type(self, toy_operator):
        x, H = toy_operator
        nz = NodoZero(x, H)
        result = nz.compute()
        assert isinstance(result, NodoZeroResult)

    def test_nodo_position_near_one(self, toy_operator):
        """Zero Node must be at x ≈ 1 (centre of inversion-symmetric grid)."""
        x, H = toy_operator
        nz = NodoZero(x, H)
        result = nz.compute()
        assert abs(result.nodo_position - 1.0) < 0.3

    def test_nodo_index_in_range(self, toy_operator):
        x, H = toy_operator
        nz = NodoZero(x, H)
        result = nz.compute()
        assert 0 <= result.nodo_index < len(x)

    def test_phase_axis_amplitude_positive(self, toy_operator):
        """Phase Emission Axis amplitude must be non-negative."""
        x, H = toy_operator
        nz = NodoZero(x, H)
        result = nz.compute()
        assert result.phase_axis_amplitude >= 0.0

    def test_ground_mode_shape(self, toy_operator):
        """Ground mode must have same length as grid."""
        x, H = toy_operator
        nz = NodoZero(x, H)
        result = nz.compute()
        assert result.ground_mode.shape == x.shape

    def test_ground_mode_is_normalised(self, toy_operator):
        """Ground mode should be normalised in L²(dx/x)."""
        x, H = toy_operator
        nz = NodoZero(x, H)
        result = nz.compute()
        psi = result.ground_mode
        log_x = np.log(x)
        dlog = log_x[1] - log_x[0]
        norm_sq = np.sum(psi ** 2) * dlog
        assert_allclose(norm_sq, 1.0, rtol=0.05)

    def test_symmetry_error_is_finite(self, toy_operator):
        x, H = toy_operator
        nz = NodoZero(x, H)
        result = nz.compute()
        assert np.isfinite(result.symmetry_error)
        assert result.symmetry_error >= 0.0

    def test_is_singular_boolean(self, toy_operator):
        x, H = toy_operator
        nz = NodoZero(x, H)
        result = nz.compute()
        assert isinstance(result.is_singular, (bool, np.bool_))

    def test_ground_eigenvalue_is_real(self, toy_operator):
        x, H = toy_operator
        nz = NodoZero(x, H)
        result = nz.compute()
        assert np.isfinite(result.ground_eigenvalue)
        assert np.isreal(result.ground_eigenvalue)

    def test_accepts_small_grid(self):
        """Should work with a minimal grid of 3 points."""
        x = np.array([0.5, 1.0, 2.0])
        H = np.diag([1.0, 0.1, 1.0])
        nz = NodoZero(x, H)
        result = nz.compute()
        assert result.nodo_position > 0


# ===========================================================================
# TestBifurcacionCuantica
# ===========================================================================

class TestBifurcacionCuantica:
    """Tests for the Quantum Bifurcation class."""

    def test_returns_correct_result_type(self, symmetric_spectrum):
        bif = BifurcacionCuantica(symmetric_spectrum)
        result = bif.bifurcar()
        assert isinstance(result, BifurcacionResult)

    def test_correct_number_of_pairs(self, symmetric_spectrum):
        """Should find 5 ± pairs for a 10-element symmetric spectrum."""
        bif = BifurcacionCuantica(symmetric_spectrum)
        result = bif.bifurcar()
        assert result.n_pairs == 5

    def test_evolucion_branch_positive(self, symmetric_spectrum):
        """All Evolución values must be positive."""
        bif = BifurcacionCuantica(symmetric_spectrum)
        result = bif.bifurcar()
        assert np.all(result.rama_evolucion > 0)

    def test_encarnacion_branch_negative(self, symmetric_spectrum):
        """All Encarnación values must be negative."""
        bif = BifurcacionCuantica(symmetric_spectrum)
        result = bif.bifurcar()
        assert np.all(result.rama_encarnacion < 0)

    def test_duality_conservation(self, symmetric_spectrum):
        """For a perfectly symmetric spectrum, duality error must be zero."""
        bif = BifurcacionCuantica(symmetric_spectrum)
        result = bif.bifurcar()
        assert_allclose(result.dualidad_error, 0.0, atol=1e-10)

    def test_noetic_momentum_positive(self, symmetric_spectrum):
        """Conserved noetic momentum Σγₙ² must be positive."""
        bif = BifurcacionCuantica(symmetric_spectrum)
        result = bif.bifurcar()
        assert result.momento_noetico > 0.0

    def test_bifurcation_angles_range(self, symmetric_spectrum):
        """Bifurcation angles must be in (0, π/2) for positive eigenvalues."""
        bif = BifurcacionCuantica(symmetric_spectrum)
        result = bif.bifurcar()
        assert np.all(result.angulo_bifurcacion > 0)
        assert np.all(result.angulo_bifurcacion < np.pi / 2)

    def test_asymmetric_spectrum_smaller_pairs(self):
        """When positive branch is larger, only as many pairs as the smaller."""
        evals = np.array([-10.0, 5.0, 15.0, 25.0])
        bif = BifurcacionCuantica(evals)
        result = bif.bifurcar()
        assert result.n_pairs == 1  # only 1 negative value

    def test_all_positive_spectrum(self):
        """No bifurcation pairs when all eigenvalues are positive."""
        evals = np.array([1.0, 5.0, 10.0])
        bif = BifurcacionCuantica(evals)
        result = bif.bifurcar()
        assert result.n_pairs == 0

    def test_empty_spectrum(self):
        """Should handle an empty eigenvalue array gracefully."""
        bif = BifurcacionCuantica(np.array([]))
        result = bif.bifurcar()
        assert result.n_pairs == 0
        assert result.dualidad_error == 0.0


# ===========================================================================
# TestVortexToroidal
# ===========================================================================

class TestVortexToroidal:
    """Tests for the toroidal evolution (Dimensional Spiral) class."""

    @pytest.fixture
    def riemann_zeros(self):
        return np.array([14.13, 21.02, 25.01, 30.42, 32.93])

    def test_returns_correct_result_type(self, riemann_zeros):
        vt = VortexToroidal(riemann_zeros)
        result = vt.evolve()
        assert isinstance(result, VortexToroidalResult)

    def test_winding_numbers_nonnegative(self, riemann_zeros):
        """Winding numbers must be ≥ 0."""
        vt = VortexToroidal(riemann_zeros, t=np.pi)
        result = vt.evolve()
        assert np.all(result.winding_numbers >= 0)

    def test_phases_in_0_2pi(self, riemann_zeros):
        """Toroidal phases must be in [0, 2π)."""
        vt = VortexToroidal(riemann_zeros, t=np.pi)
        result = vt.evolve()
        assert np.all(result.toroidal_phases >= 0.0)
        assert np.all(result.toroidal_phases < 2.0 * np.pi + 1e-10)

    def test_petal_count_nonnegative(self, riemann_zeros):
        vt = VortexToroidal(riemann_zeros, t=np.pi)
        result = vt.evolve()
        assert result.petal_count >= 0

    def test_unitary_trace_finite(self, riemann_zeros):
        vt = VortexToroidal(riemann_zeros)
        result = vt.evolve()
        assert np.isfinite(abs(result.unitary_trace))

    def test_unitary_trace_real_part(self, riemann_zeros):
        """Tr(e^{iHt}) + Tr(e^{-iHt}) must be real."""
        vt = VortexToroidal(riemann_zeros, t=1.0)
        result = vt.evolve()
        assert abs(result.unitary_trace.imag) < 1e-10

    def test_flower_coordinates_shape(self, riemann_zeros):
        """Flower of Life must have 2*N_zeros coordinates (both branches)."""
        vt = VortexToroidal(riemann_zeros)
        result = vt.evolve()
        assert result.flower_coordinates.shape == (2 * len(riemann_zeros), 2)

    def test_flower_coordinates_finite(self, riemann_zeros):
        vt = VortexToroidal(riemann_zeros)
        result = vt.evolve()
        assert np.all(np.isfinite(result.flower_coordinates))

    def test_dimension_reached_at_least_2(self, riemann_zeros):
        """Effective dimension must be ≥ 2 (2D figure-8 base)."""
        vt = VortexToroidal(riemann_zeros, t=np.pi)
        result = vt.evolve()
        assert result.dimension_reached >= 2

    def test_larger_t_more_windings(self, riemann_zeros):
        """Larger time parameter should produce ≥ as many windings."""
        vt_small = VortexToroidal(riemann_zeros, t=1.0)
        vt_large = VortexToroidal(riemann_zeros, t=100.0)
        r_small = vt_small.evolve()
        r_large = vt_large.evolve()
        assert np.sum(r_large.winding_numbers) >= np.sum(r_small.winding_numbers)

    def test_t_parameter_stored(self, riemann_zeros):
        t_val = 3.14
        vt = VortexToroidal(riemann_zeros, t=t_val)
        result = vt.evolve()
        assert_allclose(result.t, t_val)

    def test_empty_eigenvalues(self):
        """Should handle empty eigenvalue array gracefully."""
        vt = VortexToroidal(np.array([]))
        result = vt.evolve()
        assert result.petal_count == 0
        assert result.flower_coordinates.shape == (0, 2)


# ===========================================================================
# TestComputeNodoZeroFull
# ===========================================================================

class TestComputeNodoZeroFull:
    """Tests for the convenience wrapper compute_nodo_zero_full()."""

    def test_returns_dict_with_all_keys(self):
        """Return value must contain all three result keys."""
        from operators.vortex8_operator import Vortex8Operator

        op = Vortex8Operator(N=51, p_max=20, k_max=2, include_qcal_modulation=True)
        results = compute_nodo_zero_full(op, t=np.pi, n_eigenvalues=5)

        assert "nodo_zero" in results
        assert "bifurcacion" in results
        assert "toroidal" in results

    def test_nodo_zero_result_type(self):
        from operators.vortex8_operator import Vortex8Operator

        op = Vortex8Operator(N=51, p_max=20, k_max=2, include_qcal_modulation=True)
        results = compute_nodo_zero_full(op, t=1.0)

        assert isinstance(results["nodo_zero"], NodoZeroResult)
        assert isinstance(results["bifurcacion"], BifurcacionResult)
        assert isinstance(results["toroidal"], VortexToroidalResult)

    def test_bifurcacion_has_pairs(self):
        """A proper Vortex8Operator must yield at least some pairs."""
        from operators.vortex8_operator import Vortex8Operator

        op = Vortex8Operator(N=51, p_max=20, k_max=2, include_qcal_modulation=True)
        results = compute_nodo_zero_full(op)

        assert results["bifurcacion"].n_pairs >= 1

    def test_toroidal_dimension_reached(self):
        """Toroidal evolution must report a meaningful dimension (≥ 2)."""
        from operators.vortex8_operator import Vortex8Operator

        op = Vortex8Operator(N=51, p_max=20, k_max=2, include_qcal_modulation=True)
        results = compute_nodo_zero_full(op, t=np.pi)

        assert results["toroidal"].dimension_reached >= 2


# ===========================================================================
# TestQCALModulationFixed
# ===========================================================================

class TestQCALModulationFixed:
    """Regression test: QCAL modulation must produce a different operator."""

    def test_qcal_modulation_changes_operator(self):
        """
        Operators with and without QCAL modulation must differ.

        This is a regression test for the bug where
        ``C_COHERENCE_QCAL / 244.36 == 1.0`` caused the modulation to have
        no effect.
        """
        from operators.vortex8_operator import Vortex8Operator, EPSILON

        op_on = Vortex8Operator(N=51, include_qcal_modulation=True)
        op_off = Vortex8Operator(N=51, include_qcal_modulation=False)

        diff = np.linalg.norm(op_on.H - op_off.H)
        assert diff > EPSILON, (
            "QCAL modulation must produce a non-trivially different operator "
            f"(difference norm = {diff:.2e})"
        )

    def test_qcal_modulation_factor_magnitude(self):
        """
        The modulation factor 1 + F0/C_PRIMARY must be ≈ 1.225, producing
        a measurable (~22.5 %) enhancement of the prime potential.
        """
        expected_factor = 1.0 + F0_QCAL / C_PRIMARY_QCAL
        assert 1.15 < expected_factor < 1.35, (
            f"QCAL modulation factor {expected_factor:.4f} is outside [1.15, 1.35]"
        )


# ===========================================================================
# TestConstants
# ===========================================================================

class TestConstants:
    """Sanity-check the imported QCAL constants."""

    def test_f0_value(self):
        assert abs(F0_QCAL - 141.7001) < 1e-3

    def test_c_coherence_value(self):
        assert abs(C_COHERENCE_QCAL - 244.36) < 0.1

    def test_c_primary_value(self):
        assert abs(C_PRIMARY_QCAL - 629.83) < 0.1

    def test_omega_0_value(self):
        assert_allclose(OMEGA_0_QCAL, 2.0 * np.pi * F0_QCAL, rtol=1e-6)
