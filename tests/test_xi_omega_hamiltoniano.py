#!/usr/bin/env python3
"""
Tests for core/xi_omega_hamiltoniano.py
========================================

Validates all classes and functions defined in the Xi–Omega Hamiltonian module.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
QCAL ∞³ Active · 141.7001 Hz
"""

import pytest
import numpy as np

from core.xi_omega_hamiltoniano import (
    CompactificacionLogaritmica,
    PotencialPrimos,
    HamiltonianoCircular,
    DensidadEspectral,
    OperadorConvolucionXi,
    activar_operador_Xi,
    validar_sistema_xi_omega,
    ResultadoHamiltoniano,
    ResultadoConvolucionXi,
    ResultadoValidacion,
    F0_QCAL,
    C_COHERENCE,
)


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

@pytest.fixture(scope="module")
def comp_small():
    return CompactificacionLogaritmica(N=1000, n_grid=64)


@pytest.fixture(scope="module")
def comp_medium():
    return CompactificacionLogaritmica(N=10_000, n_grid=128)


@pytest.fixture(scope="module")
def pot_small():
    return PotencialPrimos(P_max=50)


# ---------------------------------------------------------------------------
# 1. CompactificacionLogaritmica
# ---------------------------------------------------------------------------

class TestCompactificacionLogaritmica:
    """Tests for the logarithmic compactification."""

    def test_period(self):
        comp = CompactificacionLogaritmica(N=1000, n_grid=64)
        assert comp.L == pytest.approx(float(np.log(1000)), rel=1e-12)

    def test_grid_length(self, comp_small):
        assert len(comp_small.u_grid) == comp_small.n_grid

    def test_grid_range(self, comp_small):
        assert comp_small.u_grid[0] == pytest.approx(0.0, abs=1e-12)
        assert comp_small.u_grid[-1] < comp_small.L  # endpoint=False

    def test_du(self, comp_small):
        expected_du = comp_small.L / comp_small.n_grid
        assert comp_small.du == pytest.approx(expected_du, rel=1e-12)

    def test_free_spectrum_spacing(self, comp_small):
        E = comp_small.free_spectrum(n_modes=5)
        diffs = np.diff(E)
        expected = 2.0 * np.pi / comp_small.L
        np.testing.assert_allclose(diffs, expected, rtol=1e-12)

    def test_free_spectrum_length(self, comp_small):
        n_modes = 4
        E = comp_small.free_spectrum(n_modes=n_modes)
        assert len(E) == 2 * n_modes + 1

    def test_free_spectrum_zero_mode(self, comp_small):
        E = comp_small.free_spectrum(n_modes=3)
        # The middle element should be 0 (n=0)
        mid = len(E) // 2
        assert E[mid] == pytest.approx(0.0, abs=1e-12)

    def test_invalid_N(self):
        with pytest.raises(ValueError):
            CompactificacionLogaritmica(N=1, n_grid=64)

    def test_invalid_n_grid(self):
        with pytest.raises(ValueError):
            CompactificacionLogaritmica(N=100, n_grid=2)


# ---------------------------------------------------------------------------
# 2. PotencialPrimos
# ---------------------------------------------------------------------------

class TestPotencialPrimos:
    """Tests for the prime-number potential."""

    def test_primes_populated(self, pot_small):
        assert len(pot_small.primes) > 0
        assert all(p >= 2 for p in pot_small.primes)

    def test_coeffs_shape(self, pot_small):
        assert len(pot_small.coeffs) == len(pot_small.primes)

    def test_coeffs_positive(self, pot_small):
        assert np.all(pot_small.coeffs > 0)

    def test_evaluar_shape(self, comp_small, pot_small):
        V = pot_small.evaluar(comp_small.u_grid)
        assert V.shape == comp_small.u_grid.shape

    def test_evaluar_real(self, comp_small, pot_small):
        V = pot_small.evaluar(comp_small.u_grid)
        assert np.all(np.isreal(V))

    def test_invalid_P_max(self):
        with pytest.raises(ValueError):
            PotencialPrimos(P_max=1)


# ---------------------------------------------------------------------------
# 3. HamiltonianoCircular
# ---------------------------------------------------------------------------

class TestHamiltonianoCircular:
    """Tests for the circular Hamiltonian."""

    @pytest.fixture(scope="class")
    def resultado(self, comp_small, pot_small):
        ham = HamiltonianoCircular(comp_small, pot_small)
        return ham.construir()

    def test_returns_dataclass(self, resultado):
        assert isinstance(resultado, ResultadoHamiltoniano)

    def test_matrix_shape(self, comp_small, pot_small):
        ham = HamiltonianoCircular(comp_small, pot_small)
        res = ham.construir()
        n = comp_small.n_grid
        assert res.H.shape == (n, n)

    def test_self_adjoint(self, comp_small, pot_small):
        ham = HamiltonianoCircular(comp_small, pot_small)
        res = ham.construir()
        assert res.hermiticity_error < 1e-8
        assert res.is_self_adjoint

    def test_eigenvalues_real(self, comp_small, pot_small):
        ham = HamiltonianoCircular(comp_small, pot_small)
        res = ham.construir()
        # eigh returns real eigenvalues; verify they are finite
        assert np.all(np.isfinite(res.eigenvalues))

    def test_eigenvalues_count(self, comp_small, pot_small):
        ham = HamiltonianoCircular(comp_small, pot_small)
        res = ham.construir()
        assert len(res.eigenvalues) == comp_small.n_grid

    def test_psi_in_range(self, comp_small, pot_small):
        ham = HamiltonianoCircular(comp_small, pot_small)
        res = ham.construir()
        assert 0.0 <= res.psi <= 1.0

    def test_eigenvectors_shape(self, comp_small, pot_small):
        ham = HamiltonianoCircular(comp_small, pot_small)
        res = ham.construir()
        n = comp_small.n_grid
        assert res.eigenvectors.shape == (n, n)


# ---------------------------------------------------------------------------
# 4. DensidadEspectral
# ---------------------------------------------------------------------------

class TestDensidadEspectral:
    """Tests for Gutzwiller spectral density."""

    def test_evaluar_shape(self, comp_small):
        den = DensidadEspectral(comp_small, P_max=50, k_max=2)
        E = np.linspace(0, 20, 200)
        d = den.evaluar(E)
        assert d.shape == E.shape

    def test_smooth_part(self, comp_small):
        # For E far from any prime frequency the density should cluster around
        # the smooth mean d̄ = L/(2π) when oscillatory terms average out.
        den = DensidadEspectral(comp_small, P_max=10, k_max=1)
        expected_mean = comp_small.L / (2.0 * np.pi)
        E = np.linspace(100, 200, 1000)  # many oscillations → average ≈ mean
        d = den.evaluar(E)
        # Mean of d(E) over large range should approximate d̄
        assert abs(np.mean(d) - expected_mean) < 0.5 * expected_mean

    def test_evaluar_finite(self, comp_small):
        den = DensidadEspectral(comp_small, P_max=30, k_max=2)
        E = np.linspace(0, 50, 500)
        d = den.evaluar(E)
        assert np.all(np.isfinite(d))


# ---------------------------------------------------------------------------
# 5. OperadorConvolucionXi
# ---------------------------------------------------------------------------

class TestOperadorConvolucionXi:
    """Tests for the Xi convolution operator."""

    @pytest.fixture(scope="class")
    def xi_op(self, comp_small):
        return OperadorConvolucionXi(comp_small, N_terms=5)

    @pytest.fixture(scope="class")
    def resultado_xi(self, xi_op):
        return xi_op.evaluar_kernel()

    def test_returns_dataclass(self, resultado_xi):
        assert isinstance(resultado_xi, ResultadoConvolucionXi)

    def test_kernel_shape(self, comp_small, resultado_xi):
        assert resultado_xi.kernel_values.shape == (comp_small.n_grid,)

    def test_kernel_even(self, resultado_xi):
        assert resultado_xi.is_even
        assert resultado_xi.parity_error < 1e-12

    def test_kernel_non_negative(self, resultado_xi):
        assert resultado_xi.is_positive
        assert resultado_xi.min_value >= -1e-14

    def test_hs_norm_positive(self, resultado_xi):
        assert resultado_xi.hilbert_schmidt_norm > 0.0

    def test_psi_in_range(self, resultado_xi):
        assert 0.0 <= resultado_xi.psi <= 1.0

    def test_aplicar_shape(self, comp_small, xi_op):
        psi = np.random.default_rng(42).random(comp_small.n_grid)
        out = xi_op.aplicar(psi)
        assert out.shape == psi.shape

    def test_aplicar_real(self, comp_small, xi_op):
        psi = np.ones(comp_small.n_grid)
        out = xi_op.aplicar(psi)
        assert np.all(np.isfinite(out))


# ---------------------------------------------------------------------------
# 6. activar_operador_Xi
# ---------------------------------------------------------------------------

class TestActivarOperadorXi:
    """Tests for the activation entry point."""

    @pytest.fixture(scope="class")
    def report(self):
        return activar_operador_Xi(N=1000, n_grid=64, P_max=30, N_terms_phi=5)

    def test_returns_dict(self, report):
        assert isinstance(report, dict)

    def test_required_keys(self, report):
        for key in ("status", "L", "hermiticity_error", "is_self_adjoint",
                    "parity_error", "is_kernel_even", "psi_hamiltonian",
                    "psi_xi", "timestamp"):
            assert key in report, f"Missing key: {key}"

    def test_status_contains_activado(self, report):
        assert "ACTIVADO" in report["status"]

    def test_L_positive(self, report):
        assert report["L"] > 0.0

    def test_hermiticity_error_small(self, report):
        assert report["hermiticity_error"] < 1e-8

    def test_is_self_adjoint(self, report):
        assert report["is_self_adjoint"] is True

    def test_is_kernel_even(self, report):
        assert report["is_kernel_even"] is True

    def test_psi_in_range(self, report):
        assert 0.0 <= report["psi_hamiltonian"] <= 1.0
        assert 0.0 <= report["psi_xi"] <= 1.0


# ---------------------------------------------------------------------------
# 7. validar_sistema_xi_omega
# ---------------------------------------------------------------------------

class TestValidarSistemaXiOmega:
    """Tests for the 4-criterion system validation."""

    @pytest.fixture(scope="class")
    def resultado(self):
        return validar_sistema_xi_omega(
            N=1000, n_grid=64, P_max=30, N_terms_phi=5
        )

    def test_returns_dataclass(self, resultado):
        assert isinstance(resultado, ResultadoValidacion)

    def test_compactacion_ok(self, resultado):
        assert resultado.compactacion_ok is True

    def test_espectro_libre_ok(self, resultado):
        assert resultado.espectro_libre_ok is True

    def test_autoadjuncion_ok(self, resultado):
        assert resultado.autoadjuncion_ok is True

    def test_paridad_kernel_ok(self, resultado):
        assert resultado.paridad_kernel_ok is True

    def test_all_passed(self, resultado):
        assert resultado.all_passed is True

    def test_psi_in_range(self, resultado):
        assert 0.0 <= resultado.psi <= 1.0

    def test_details_keys(self, resultado):
        for key in ("L", "du", "spacing_error", "hermiticity_error",
                    "parity_error", "hs_norm", "n_primes", "n_eigenvalues"):
            assert key in resultado.details, f"Missing detail key: {key}"


# ---------------------------------------------------------------------------
# 8. Constants
# ---------------------------------------------------------------------------

class TestConstants:
    """Verify exported QCAL constants."""

    def test_F0_QCAL(self):
        assert F0_QCAL == pytest.approx(141.7001, rel=1e-6)

    def test_C_COHERENCE(self):
        assert C_COHERENCE == pytest.approx(244.36, rel=1e-6)
