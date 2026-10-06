#!/usr/bin/env python3
r"""
Tests for Motor de Resonancia PT-Symmetry: Operador Biológico Holográfico
=========================================================================

Validates the five-class PT-symmetry biological holographic module:
  1. GeometriaEspectral
  2. OperadorPTSimetrico
  3. BordeCitoplasmatico
  4. EspacioBulkAdS
  5. EstabilizadorRiemann
  + simular_resonancia_pt (helper)
  + resolver_holografia_biologica (master function)
  + ResultadoPTHolografico (result dataclass)

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: March 2026
"""

import pytest
import numpy as np

from physics.holografia_biologica_pt import (
    GeometriaEspectral,
    OperadorPTSimetrico,
    BordeCitoplasmatico,
    EspacioBulkAdS,
    EstabilizadorRiemann,
    ResultadoPTHolografico,
    simular_resonancia_pt,
    resolver_holografia_biologica,
    # Module-level constants
    RIEMANN_ZEROS_KNOWN,
    PSI_PT_THRESHOLD,
    DELTA_CFT,
    L_DVR,
)


# ============================================================================
# Module-level constants
# ============================================================================

class TestConstants:
    """Verify module-level constants match specification."""

    def test_psi_pt_threshold_value(self):
        assert abs(PSI_PT_THRESHOLD - 0.888) < 1e-6

    def test_delta_cft_positive(self):
        assert DELTA_CFT > 0

    def test_l_dvr_positive(self):
        assert L_DVR > 0

    def test_riemann_zeros_known_length(self):
        assert len(RIEMANN_ZEROS_KNOWN) >= 10

    def test_riemann_zeros_positive(self):
        assert all(z > 0 for z in RIEMANN_ZEROS_KNOWN)

    def test_riemann_zeros_sorted(self):
        zeros = RIEMANN_ZEROS_KNOWN
        assert all(zeros[i] < zeros[i + 1] for i in range(len(zeros) - 1))

    def test_first_riemann_zero_value(self):
        assert abs(RIEMANN_ZEROS_KNOWN[0] - 14.134725142) < 1e-6


# ============================================================================
# GeometriaEspectral
# ============================================================================

class TestGeometriaEspectral:
    """Tests for the DVR midpoint grid and kinetic operator."""

    def test_default_construction(self):
        geo = GeometriaEspectral()
        assert geo.N == 100
        assert geo.L == L_DVR

    def test_grid_length(self):
        geo = GeometriaEspectral(N=50, L=5.0)
        assert len(geo.u) == 50

    def test_grid_bounds(self):
        """Grid points must be strictly inside (-L, L)."""
        geo = GeometriaEspectral(N=50, L=5.0)
        assert geo.u.min() > -5.0
        assert geo.u.max() < 5.0

    def test_grid_spacing(self):
        """Uniform spacing: du = 2L / (N+1)."""
        geo = GeometriaEspectral(N=10, L=5.0)
        diffs = np.diff(geo.u)
        assert np.allclose(diffs, diffs[0], rtol=1e-10)
        expected_du = 2.0 * 5.0 / (10 + 1)
        assert abs(geo.du - expected_du) < 1e-12

    def test_kinetic_matrix_shape(self):
        geo = GeometriaEspectral(N=20, L=3.0)
        assert geo.T.shape == (20, 20)

    def test_kinetic_matrix_symmetric(self):
        geo = GeometriaEspectral(N=20, L=3.0)
        assert np.allclose(geo.T, geo.T.T, atol=1e-12)

    def test_kinetic_matrix_positive_definite(self):
        """−d²/du² with Dirichlet BC is positive definite."""
        geo = GeometriaEspectral(N=20, L=3.0)
        eigvals = np.linalg.eigvalsh(geo.T)
        assert eigvals.min() > 0

    def test_kinetic_diagonal_value(self):
        """Diagonal element should be 2/h²."""
        geo = GeometriaEspectral(N=10, L=5.0)
        expected = 2.0 / geo.du ** 2
        assert np.allclose(np.diag(geo.T), expected, rtol=1e-10)

    def test_invalid_N_too_small(self):
        with pytest.raises(ValueError, match="N debe ser"):
            GeometriaEspectral(N=3)

    def test_invalid_L_negative(self):
        with pytest.raises(ValueError, match="L debe ser"):
            GeometriaEspectral(L=-1.0)

    def test_invalid_L_zero(self):
        with pytest.raises(ValueError, match="L debe ser"):
            GeometriaEspectral(L=0.0)


# ============================================================================
# OperadorPTSimetrico
# ============================================================================

class TestOperadorPTSimetrico:
    """Tests for the non-Hermitian PT-symmetric Hamiltonian."""

    def test_default_construction(self):
        op = OperadorPTSimetrico()
        assert op.coherencia == 0.999999

    def test_hamiltonian_shape(self):
        op = OperadorPTSimetrico(N=30)
        assert op.H.shape == (30, 30)

    def test_hamiltonian_complex_dtype(self):
        op = OperadorPTSimetrico(N=20)
        assert np.iscomplexobj(op.H)

    def test_high_coherence_gives_real_spectrum(self):
        """Ψ → 1: imaginary parts of eigenvalues must be ≈ 0."""
        op = OperadorPTSimetrico(coherencia=0.999999, kappa=0.1, N=60)
        assert np.allclose(op.espectro.imag, 0, atol=1e-5)

    def test_zero_kappa_is_hermitian(self):
        """κ = 0 ⟹ operator is Hermitian ⟹ all eigenvalues are real."""
        op = OperadorPTSimetrico(coherencia=0.5, kappa=0.0, N=40)
        assert np.allclose(op.espectro.imag, 0, atol=1e-10)

    def test_low_coherence_large_kappa_may_have_complex_eigenvalues(self):
        """Low Ψ + large κ ⟹ at least some Im ≠ 0 (PT spontaneously broken)."""
        op = OperadorPTSimetrico(coherencia=0.0, kappa=5.0, N=40)
        max_imag = np.max(np.abs(op.espectro.imag))
        assert max_imag > 0

    def test_eigenvalues_sorted_by_real_part(self):
        op = OperadorPTSimetrico(N=30)
        reals = op.espectro.real
        assert np.all(np.diff(reals) >= -1e-10)

    def test_coherencia_operador_high_psi(self):
        """High Ψ ⟹ coherencia_operador ≈ 1."""
        op = OperadorPTSimetrico(coherencia=0.999999, N=60)
        assert op.coherencia_operador > 0.99

    def test_conmutador_pt_small_for_high_psi(self):
        """PT commutator norm should be ≈ 0 for any coherence level."""
        op = OperadorPTSimetrico(coherencia=0.999999, N=30)
        comm = op.verificar_conmutador_pt()
        assert comm < 1e-10

    def test_conmutador_pt_returns_float(self):
        op = OperadorPTSimetrico(N=20)
        assert isinstance(op.verificar_conmutador_pt(), float)

    def test_invalid_coherencia_above_one(self):
        with pytest.raises(ValueError, match="coherencia debe estar"):
            OperadorPTSimetrico(coherencia=1.5)

    def test_invalid_coherencia_below_zero(self):
        with pytest.raises(ValueError, match="coherencia debe estar"):
            OperadorPTSimetrico(coherencia=-0.1)

    def test_invalid_kappa_negative(self):
        with pytest.raises(ValueError, match="kappa debe ser"):
            OperadorPTSimetrico(kappa=-1.0)

    def test_determinism(self):
        """Same parameters must produce identical eigenvalues."""
        op1 = OperadorPTSimetrico(coherencia=0.5, kappa=0.1, N=30)
        op2 = OperadorPTSimetrico(coherencia=0.5, kappa=0.1, N=30)
        assert np.allclose(op1.espectro, op2.espectro)

    def test_kappa_eff_suppression(self):
        """Higher Ψ ⟹ smaller imaginary part ⟹ more real eigenvalues."""
        op_low = OperadorPTSimetrico(coherencia=0.0, kappa=0.3, N=40)
        op_high = OperadorPTSimetrico(coherencia=0.999, kappa=0.3, N=40)
        imag_low = np.mean(np.abs(op_low.espectro.imag))
        imag_high = np.mean(np.abs(op_high.espectro.imag))
        assert imag_high < imag_low


# ============================================================================
# simular_resonancia_pt
# ============================================================================

class TestSimularResonanciaPT:
    """Tests for the simular_resonancia_pt helper function."""

    def test_returns_ndarray(self):
        result = simular_resonancia_pt(N=30)
        assert isinstance(result, np.ndarray)

    def test_high_coherence_real_spectrum(self):
        espectro = simular_resonancia_pt(coherencia=0.999999, N=60)
        assert np.allclose(espectro.imag, 0, atol=1e-5)

    def test_length_matches_N(self):
        espectro = simular_resonancia_pt(N=40)
        assert len(espectro) == 40

    def test_sorted_by_real_part(self):
        espectro = simular_resonancia_pt(N=30)
        assert np.all(np.diff(espectro.real) >= -1e-10)


# ============================================================================
# BordeCitoplasmatico
# ============================================================================

class TestBordeCitoplasmatico:
    """Tests for the CFT boundary / cytoplasmic membrane correlator."""

    def test_default_construction(self):
        borde = BordeCitoplasmatico()
        assert borde.n_puntos == 512
        assert borde.delta == DELTA_CFT

    def test_correlator_length(self):
        borde = BordeCitoplasmatico(n_puntos=100)
        assert len(borde.G) == 100

    def test_correlator_positive(self):
        """G(t) = 1/|t|^{2Δ} is strictly positive."""
        borde = BordeCitoplasmatico()
        assert np.all(borde.G > 0)

    def test_correlator_decaying(self):
        """G must be a decreasing function of t (since t > 0 and 2Δ > 0)."""
        borde = BordeCitoplasmatico(n_puntos=50, delta=1.0)
        assert np.all(np.diff(borde.G) <= 0)

    def test_coherencia_borde_in_range(self):
        borde = BordeCitoplasmatico()
        assert 0.0 <= borde.coherencia_borde <= 1.0

    def test_time_axis_positive(self):
        """Time axis must be positive (no singularity at t=0)."""
        borde = BordeCitoplasmatico(n_puntos=50)
        assert borde.t.min() > 0

    def test_larger_delta_steeper_decay(self):
        """Larger Δ ⟹ faster decay of G(t) for t > 1."""
        borde1 = BordeCitoplasmatico(n_puntos=50, delta=1.0)
        borde2 = BordeCitoplasmatico(n_puntos=50, delta=2.0)
        # At t=5, Δ=2 ⟹ much smaller G
        assert borde2.G[-1] < borde1.G[-1]

    def test_invalid_n_puntos(self):
        with pytest.raises(ValueError, match="n_puntos debe ser"):
            BordeCitoplasmatico(n_puntos=5)

    def test_invalid_delta_zero(self):
        with pytest.raises(ValueError, match="delta debe ser"):
            BordeCitoplasmatico(delta=0.0)

    def test_invalid_t_max_negative(self):
        with pytest.raises(ValueError, match="t_max debe ser"):
            BordeCitoplasmatico(t_max=-1.0)


# ============================================================================
# EspacioBulkAdS
# ============================================================================

class TestEspacioBulkAdS:
    """Tests for the AdS₂ Poincaré bulk with Witten propagator."""

    def test_default_construction(self):
        bulk = EspacioBulkAdS()
        assert bulk.delta == DELTA_CFT

    def test_m2_formula(self):
        """m² = Δ(Δ−1) for AdS₂ scalar."""
        bulk = EspacioBulkAdS(delta=2.0)
        assert abs(bulk.m2 - 2.0 * 1.0) < 1e-12

    def test_bf_satisfied_for_delta_half(self):
        """Δ = 0.5 ⟹ m² = 0.5·(−0.5) = −0.25 ≥ −0.25 ⟹ BF satisfied."""
        bulk = EspacioBulkAdS(delta=0.5)
        assert bulk.bf_satisfecha

    def test_bf_satisfied_for_large_delta(self):
        bulk = EspacioBulkAdS(delta=2.0)
        assert bulk.bf_satisfecha

    def test_propagator_shape(self):
        bulk = EspacioBulkAdS(n_z=10, n_t=12)
        assert bulk.K.shape == (10, 12)

    def test_propagator_positive(self):
        bulk = EspacioBulkAdS()
        assert np.all(bulk.K >= 0)

    def test_propagator_peaks_near_boundary(self):
        """K should be largest near z → 0 (holographic UV dominance)."""
        bulk = EspacioBulkAdS(delta=1.5, n_z=20, n_t=20)
        near_boundary_mean = bulk.K[:3, :].mean()
        far_bulk_mean = bulk.K[-3:, :].mean()
        assert near_boundary_mean > far_bulk_mean

    def test_coherencia_bulk_in_range(self):
        bulk = EspacioBulkAdS()
        assert 0.0 <= bulk.coherencia_bulk <= 1.0

    def test_invalid_delta_below_half(self):
        with pytest.raises(ValueError, match="cota BF"):
            EspacioBulkAdS(delta=0.4)

    def test_invalid_n_z(self):
        with pytest.raises(ValueError, match="n_z debe ser"):
            EspacioBulkAdS(n_z=1)

    def test_invalid_n_t(self):
        with pytest.raises(ValueError, match="n_t debe ser"):
            EspacioBulkAdS(n_t=1)

    def test_determinism(self):
        bulk1 = EspacioBulkAdS(delta=1.5, n_z=10, n_t=10)
        bulk2 = EspacioBulkAdS(delta=1.5, n_z=10, n_t=10)
        assert np.allclose(bulk1.K, bulk2.K)


# ============================================================================
# EstabilizadorRiemann
# ============================================================================

class TestEstabilizadorRiemann:
    """Tests for the Pearson correlation with known Riemann zeros."""

    def _make_real_spectrum(self, n: int = 20) -> np.ndarray:
        """Return synthetic real positive spectrum for testing."""
        op = OperadorPTSimetrico(coherencia=0.999999, N=n)
        return op.espectro

    def test_autovalores_reales_positive(self):
        espectro = self._make_real_spectrum()
        estab = EstabilizadorRiemann(espectro)
        assert np.all(estab.autovalores_reales > 0)

    def test_autovalores_reales_sorted(self):
        espectro = self._make_real_spectrum()
        estab = EstabilizadorRiemann(espectro)
        av = estab.autovalores_reales
        assert np.all(np.diff(av) >= -1e-10)

    def test_correlacion_in_valid_range(self):
        espectro = self._make_real_spectrum()
        estab = EstabilizadorRiemann(espectro)
        assert -1.0 <= estab.correlacion <= 1.0

    def test_high_coherence_achieves_high_correlation(self):
        """High-Ψ eigenvalues rescaled to Riemann range should correlate well."""
        op = OperadorPTSimetrico(coherencia=0.999999, kappa=0.1, N=100)
        estab = EstabilizadorRiemann(op.espectro)
        assert estab.correlacion >= 0.85

    def test_estabilizado_flag_set_when_above_threshold(self):
        op = OperadorPTSimetrico(coherencia=0.999999, N=100)
        estab = EstabilizadorRiemann(op.espectro, umbral_pearson=0.85)
        assert estab.estabilizado == (estab.correlacion >= 0.85)

    def test_custom_zeros_riemann(self):
        espectro = self._make_real_spectrum()
        custom_zeros = [14.0, 21.0, 25.0, 30.0, 33.0]
        estab = EstabilizadorRiemann(espectro, zeros_riemann=custom_zeros)
        assert len(estab.zeros_riemann) == 5

    def test_empty_positive_eigenvalues_gives_zero_correlation(self):
        """All-imaginary spectrum ⟹ no real eigenvalues ⟹ correlation = 0."""
        espectro = np.array([1j, 2j, 3j, -1j])
        estab = EstabilizadorRiemann(espectro)
        assert estab.correlacion == 0.0

    def test_invalid_umbral_above_one(self):
        espectro = self._make_real_spectrum()
        with pytest.raises(ValueError, match="umbral_pearson"):
            EstabilizadorRiemann(espectro, umbral_pearson=1.5)

    def test_invalid_umbral_zero(self):
        espectro = self._make_real_spectrum()
        with pytest.raises(ValueError, match="umbral_pearson"):
            EstabilizadorRiemann(espectro, umbral_pearson=0.0)

    def test_correlation_finite(self):
        espectro = self._make_real_spectrum()
        estab = EstabilizadorRiemann(espectro)
        assert np.isfinite(estab.correlacion)


# ============================================================================
# ResultadoPTHolografico
# ============================================================================

class TestResultadoPTHolografico:
    """Tests for the result dataclass."""

    def test_default_construction(self):
        res = ResultadoPTHolografico()
        assert res.coherencia_global == 0.0
        assert not res.aprobado

    def test_resumen_returns_string(self):
        res = ResultadoPTHolografico(aprobado=True, coherencia_global=0.95)
        summary = res.resumen()
        assert isinstance(summary, str)
        assert "APROBADO" in summary

    def test_resumen_unapproved(self):
        res = ResultadoPTHolografico(aprobado=False)
        assert "REQUIERE REVISIÓN" in res.resumen()

    def test_detalles_is_dict(self):
        res = ResultadoPTHolografico()
        assert isinstance(res.detalles, dict)


# ============================================================================
# resolver_holografia_biologica (master function) — end-to-end
# ============================================================================

class TestResolverHolografiaBiologica:
    """End-to-end tests for the master function."""

    @pytest.fixture(scope="class")
    def resultado_default(self):
        """Compute default result once for the class (expensive)."""
        return resolver_holografia_biologica(N_dvr=60, n_borde=128, n_z=20, n_t=20)

    def test_returns_result_dataclass(self, resultado_default):
        assert isinstance(resultado_default, ResultadoPTHolografico)

    def test_coherencia_global_above_threshold(self, resultado_default):
        assert resultado_default.coherencia_global >= PSI_PT_THRESHOLD

    def test_aprobado_true(self, resultado_default):
        assert resultado_default.aprobado is True

    def test_estabilizado_true(self, resultado_default):
        assert resultado_default.estabilizado is True

    def test_bf_satisfecha(self, resultado_default):
        assert resultado_default.bf_satisfecha is True

    def test_conmutador_pt_near_zero(self, resultado_default):
        assert resultado_default.conmutador_pt < 1e-10

    def test_correlacion_riemann_above_threshold(self, resultado_default):
        assert resultado_default.correlacion_riemann >= 0.85

    def test_coherencia_operador_high(self, resultado_default):
        assert resultado_default.coherencia_operador > 0.99

    def test_coherencia_borde_in_range(self, resultado_default):
        assert 0.0 <= resultado_default.coherencia_borde <= 1.0

    def test_coherencia_bulk_in_range(self, resultado_default):
        assert 0.0 <= resultado_default.coherencia_bulk <= 1.0

    def test_detalles_has_expected_keys(self, resultado_default):
        expected = {"kappa_eff", "n_autovalores_reales", "n_zeros_riemann",
                    "m2_bulk", "delta_cft", "N_dvr"}
        assert expected.issubset(resultado_default.detalles.keys())

    def test_global_coherence_formula(self, resultado_default):
        """Verify Ψ_global = 0.6·Ψ_op + 0.3·Ψ_borde + 0.1·Ψ_bulk."""
        res = resultado_default
        expected = (
            0.6 * res.coherencia_operador
            + 0.3 * res.coherencia_borde
            + 0.1 * res.coherencia_bulk
        )
        assert abs(res.coherencia_global - expected) < 1e-12

    def test_determinism(self):
        """Identical inputs must produce identical outputs."""
        kwargs = dict(
            coherencia=0.999999, kappa=0.1, N_dvr=40,
            n_borde=64, n_z=10, n_t=10
        )
        res1 = resolver_holografia_biologica(**kwargs)
        res2 = resolver_holografia_biologica(**kwargs)
        assert abs(res1.coherencia_global - res2.coherencia_global) < 1e-12
        assert abs(res1.correlacion_riemann - res2.correlacion_riemann) < 1e-12

    def test_low_coherence_may_not_be_approved(self):
        """Very low Ψ + high κ should reduce coherencia_operador significantly."""
        res = resolver_holografia_biologica(
            coherencia=0.0, kappa=5.0, N_dvr=40,
            n_borde=64, n_z=10, n_t=10
        )
        # Not asserting aprobado=False because borde/bulk coherences may compensate,
        # but coherencia_operador should drop noticeably
        assert res.coherencia_operador < 1.0

    def test_resumen_string_content(self, resultado_default):
        summary = resultado_default.resumen()
        assert "Ψ_global" in summary
        assert "r_Riemann" in summary
        assert "Cota BF" in summary
