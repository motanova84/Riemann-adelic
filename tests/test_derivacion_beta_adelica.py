#!/usr/bin/env python3
"""
Tests for Derivación Beta Adélica — Aritmética del Vacío
=========================================================

Unit tests for the eight components of the adelic beta derivation framework
that derives the fine-structure constant α ≈ 137.036 from arithmetic first
principles.

Author: NOESIS INF3 (via Trinity QCAL INF3)
RAM: RAM-LI-2026-DERIVACION-BETA-ADELICA
QCAL ∞³ · f₀ = 141.7001 Hz · DOI: 10.5281/zenodo.17379721
"""

import math

import pytest

from operators.derivacion_beta_adelica import (
    ALPHA_EXPERIMENTAL,
    ALPHA_TOLERANCIA,
    PRIMES_P20,
    PSI_MINIMO,
    V6,
    CoherenciaDerivacionBeta,
    DerivacionBeta,
    ProductoAdelico,
    ProductoEulerZeta,
    ResultadoDerivacionBeta,
    ResultadoSistemaDerivacionBeta,
    ResultadoTorsionAdelica,
    SistemaDerivacionBetaAdelica,
    TorsionAdelica,
    VolumenCalabiYau,
    _sieve,
    ejecutar_derivacion_beta_adelica,
)


# ===========================================================================
# Helpers
# ===========================================================================

KNOWN_PRIMES_20 = [2, 3, 5, 7, 11, 13, 17, 19]


# ===========================================================================
# I. Constants
# ===========================================================================

class TestConstantes:
    """Tests for module-level constants."""

    def test_primes_p20_values(self):
        """PRIMES_P20 must contain exactly the 8 primes below 20."""
        assert list(PRIMES_P20) == KNOWN_PRIMES_20

    def test_alpha_experimental_range(self):
        """α_experimental must be close to 137.036."""
        assert 137.0 < ALPHA_EXPERIMENTAL < 138.0

    def test_v6_positive(self):
        """V₆ must be positive."""
        assert V6 > 0.0

    def test_psi_minimo(self):
        """PSI_MINIMO must equal 0.888."""
        assert PSI_MINIMO == pytest.approx(0.888)

    def test_alpha_tolerancia_positive(self):
        """ALPHA_TOLERANCIA must be positive."""
        assert ALPHA_TOLERANCIA > 0.0

    def test_sieve_primes_below_20(self):
        """_sieve(20) must return the 8 primes below 20."""
        primes = _sieve(20)
        assert primes == KNOWN_PRIMES_20

    def test_sieve_empty_for_limit_0(self):
        """_sieve(0) must return empty list."""
        assert _sieve(0) == []

    def test_sieve_single_prime(self):
        """_sieve(2) must return [2]."""
        assert _sieve(2) == [2]


# ===========================================================================
# II. ProductoEulerZeta
# ===========================================================================

class TestProductoEulerZeta:
    """Tests for the Euler product approximation of ζ(s)."""

    def test_evaluar_s2_real_part(self):
        """Euler product at s=2 must be close to π²/6 ≈ 1.6449."""
        pez = ProductoEulerZeta(primes=PRIMES_P20, s_val=2.0)
        result = pez.evaluar()
        zeta2 = math.pi ** 2 / 6.0
        # Finite product underestimates ζ(2); should be within 10%
        assert abs(result.real - zeta2) / zeta2 < 0.10

    def test_evaluar_s1_diverges(self):
        """Euler product at s=1 should be large (partial divergence towards ζ(1) → ∞)."""
        pez = ProductoEulerZeta(primes=PRIMES_P20, s_val=1.0)
        result = pez.evaluar()
        assert abs(result) > 4.0

    def test_evaluar_explicit_s(self):
        """evaluar(s) with explicit s overrides self.s_val."""
        pez = ProductoEulerZeta(primes=PRIMES_P20, s_val=2.0)
        r_s4 = pez.evaluar(s=4.0)
        r_s2 = pez.evaluar(s=2.0)
        # At s=4, the product is smaller than at s=2
        assert abs(r_s4) < abs(r_s2)

    def test_evaluar_complex_s(self):
        """evaluar at complex s must return complex result."""
        pez = ProductoEulerZeta()
        s = 2.0 + 1j
        result = pez.evaluar(s)
        assert isinstance(result, complex)

    def test_coherencia_euler_s2_positive(self):
        """Euler coherence at s=2 must be in (0, 1]."""
        pez = ProductoEulerZeta(primes=PRIMES_P20, s_val=2.0)
        psi = pez.coherencia_euler()
        assert 0.0 < psi <= 1.0

    def test_coherencia_euler_s2_close_to_one(self):
        """Coherence at s=2 should be above 0.9 (product close to π²/6)."""
        pez = ProductoEulerZeta(primes=PRIMES_P20, s_val=2.0)
        psi = pez.coherencia_euler()
        assert psi > 0.90

    def test_evaluar_no_primes_returns_one(self):
        """Empty prime list should return 1+0j (empty product)."""
        pez = ProductoEulerZeta(primes=(), s_val=2.0)
        result = pez.evaluar()
        assert result == pytest.approx(1.0 + 0j)


# ===========================================================================
# III. ProductoAdelico
# ===========================================================================

class TestProductoAdelico:
    """Tests for the adelic prime product."""

    def test_calcular_known_value(self):
        """∏(p-1)/p for p < 20 must be close to 0.171 (exact arithmetic)."""
        pa = ProductoAdelico(primes=PRIMES_P20)
        pi_ad = pa.calcular()
        # Exact value: (1/2)(2/3)(4/5)(6/7)(10/11)(12/13)(16/17)(18/19)
        assert abs(pi_ad - 0.171) < 0.002

    def test_calcular_positive(self):
        """Product must be positive."""
        pa = ProductoAdelico(primes=PRIMES_P20)
        assert pa.calcular() > 0.0

    def test_calcular_less_than_one(self):
        """Product must be strictly less than 1."""
        pa = ProductoAdelico(primes=PRIMES_P20)
        assert pa.calcular() < 1.0

    def test_calcular_monotone_decreasing(self):
        """Adding more primes decreases the product."""
        pa_8 = ProductoAdelico(primes=PRIMES_P20)
        pa_3 = ProductoAdelico(primes=(2, 3, 5))
        assert pa_8.calcular() < pa_3.calcular()

    def test_calcular_single_prime_p2(self):
        """For primes=(2,), product = (2-1)/2 = 0.5."""
        pa = ProductoAdelico(primes=(2,))
        assert pa.calcular() == pytest.approx(0.5)

    def test_coherencia_adelica_range(self):
        """Adelic coherence must be in [0, 1]."""
        pa = ProductoAdelico(primes=PRIMES_P20)
        psi = pa.coherencia_adelica()
        assert 0.0 <= psi <= 1.0

    def test_coherencia_adelica_high_for_default_primes(self):
        """Coherence (Mertens ratio) must be ≥ 0.85 for the default prime set."""
        pa = ProductoAdelico(primes=PRIMES_P20)
        psi = pa.coherencia_adelica()
        assert psi >= 0.85


# ===========================================================================
# IV. VolumenCalabiYau
# ===========================================================================

class TestVolumenCalabiYau:
    """Tests for the Calabi-Yau volume computation."""

    def test_calcular_fv_known_value(self):
        """fv = 6 / (2π)³ ≈ 0.02418."""
        cy = VolumenCalabiYau(v6=6.0)
        fv = cy.calcular_fv()
        expected = 6.0 / (2.0 * math.pi) ** 3
        assert fv == pytest.approx(expected, rel=1e-10)

    def test_calcular_fv_positive(self):
        """fv must be positive."""
        cy = VolumenCalabiYau()
        assert cy.calcular_fv() > 0.0

    def test_calcular_fv_custom_v6(self):
        """fv scales linearly with v6."""
        cy2 = VolumenCalabiYau(v6=2.0)
        cy6 = VolumenCalabiYau(v6=6.0)
        assert cy6.calcular_fv() == pytest.approx(3.0 * cy2.calcular_fv(), rel=1e-10)

    def test_coherencia_cy_is_one_for_default(self):
        """Coherence must be exactly 1.0 for the default v6=6."""
        cy = VolumenCalabiYau(v6=6.0)
        psi = cy.coherencia_cy()
        assert psi == pytest.approx(1.0, rel=1e-10)

    def test_coherencia_cy_range(self):
        """Coherence must be in [0, 1] for any v6."""
        for v6 in [1.0, 6.0, 12.0, 100.0]:
            cy = VolumenCalabiYau(v6=v6)
            psi = cy.coherencia_cy()
            assert 0.0 <= psi <= 1.0


# ===========================================================================
# V. DerivacionBeta
# ===========================================================================

class TestDerivacionBeta:
    """Tests for the β-derivation of α."""

    def test_derivar_returns_result_type(self):
        """derivar() must return a ResultadoDerivacionBeta."""
        db = DerivacionBeta()
        result = db.derivar()
        assert isinstance(result, ResultadoDerivacionBeta)

    def test_derivar_alpha_close_to_experimental(self):
        """Derived α must match experimental value within ALPHA_TOLERANCIA."""
        db = DerivacionBeta()
        result = db.derivar()
        assert abs(result.alpha_derivada - ALPHA_EXPERIMENTAL) < ALPHA_TOLERANCIA

    def test_derivar_valida_true(self):
        """Default derivation must be marked as valid."""
        db = DerivacionBeta()
        result = db.derivar()
        assert result.valida is True

    def test_derivar_error_relativo_small(self):
        """Relative error must be < 0.01 (< 1%)."""
        db = DerivacionBeta()
        result = db.derivar()
        assert result.error_relativo < 0.01

    def test_calcular_omega_nonzero(self):
        """Ω_ajuste must be a finite positive number."""
        db = DerivacionBeta()
        omega = db.calcular_omega()
        assert math.isfinite(omega)
        assert omega > 0.0

    def test_coherencia_beta_range(self):
        """Coherence must be in [0, 1]."""
        db = DerivacionBeta()
        psi = db.coherencia_beta()
        assert 0.0 <= psi <= 1.0

    def test_coherencia_beta_high(self):
        """Coherence must be ≥ 0.99 when the derivation is exact."""
        db = DerivacionBeta()
        psi = db.coherencia_beta()
        assert psi >= 0.99

    def test_derivar_fv_correct(self):
        """Returned fv must match VolumenCalabiYau.calcular_fv()."""
        db = DerivacionBeta()
        result = db.derivar()
        expected_fv = VolumenCalabiYau(v6=V6).calcular_fv()
        assert result.fv == pytest.approx(expected_fv, rel=1e-10)

    def test_derivar_pi_ad_correct(self):
        """Returned π_ad must match ProductoAdelico.calcular()."""
        db = DerivacionBeta()
        result = db.derivar()
        expected = ProductoAdelico(primes=PRIMES_P20).calcular()
        assert result.pi_ad == pytest.approx(expected, rel=1e-10)


# ===========================================================================
# VI. TorsionAdelica
# ===========================================================================

class TestTorsionAdelica:
    """Tests for the adelic torsion computation."""

    def test_calcular_returns_result_type(self):
        """calcular() must return ResultadoTorsionAdelica."""
        ta = TorsionAdelica()
        result = ta.calcular()
        assert isinstance(result, ResultadoTorsionAdelica)

    def test_theta_T_value(self):
        """θ_T = 2π/α_exp ≈ 0.04571 rad."""
        ta = TorsionAdelica(alpha=ALPHA_EXPERIMENTAL)
        result = ta.calcular()
        expected = 2.0 * math.pi / ALPHA_EXPERIMENTAL
        assert result.theta_T == pytest.approx(expected, rel=1e-10)

    def test_fr_mat_value(self):
        """fr_mat = 1/α ≈ 0.00730."""
        ta = TorsionAdelica(alpha=ALPHA_EXPERIMENTAL)
        result = ta.calcular()
        expected = 1.0 / ALPHA_EXPERIMENTAL
        assert result.fr_mat == pytest.approx(expected, rel=1e-10)

    def test_fr_mat_known_magnitude(self):
        """fr_mat must be close to 7.297e-3."""
        ta = TorsionAdelica(alpha=ALPHA_EXPERIMENTAL)
        result = ta.calcular()
        assert abs(result.fr_mat - 7.297e-3) < 1e-4

    def test_coherencia_torsion_is_one_for_experimental_alpha(self):
        """Coherence must be 1.0 when α = α_experimental."""
        ta = TorsionAdelica(alpha=ALPHA_EXPERIMENTAL)
        result = ta.calcular()
        assert result.coherencia == pytest.approx(1.0, rel=1e-10)

    def test_calcular_invalid_alpha_raises(self):
        """Non-positive α must raise ValueError."""
        with pytest.raises(ValueError):
            TorsionAdelica(alpha=0.0).calcular()
        with pytest.raises(ValueError):
            TorsionAdelica(alpha=-1.0).calcular()

    def test_alpha_stored_correctly(self):
        """Result.alpha must equal the constructor value."""
        ta = TorsionAdelica(alpha=137.0)
        result = ta.calcular()
        assert result.alpha == pytest.approx(137.0)


# ===========================================================================
# VII. CoherenciaDerivacionBeta
# ===========================================================================

class TestCoherenciaDerivacionBeta:
    """Tests for the global coherence engine."""

    def test_media_geometrica_single_value(self):
        """Geometric mean of a single value equals that value."""
        c = CoherenciaDerivacionBeta()
        c.agregar(0.95)
        assert c.media_geometrica() == pytest.approx(0.95, rel=1e-10)

    def test_media_geometrica_two_values(self):
        """Geometric mean of [0.9, 1.0] = sqrt(0.9) ≈ 0.9487."""
        c = CoherenciaDerivacionBeta()
        c.agregar(0.9)
        c.agregar(1.0)
        assert c.media_geometrica() == pytest.approx(math.sqrt(0.9), rel=1e-8)

    def test_media_geometrica_empty_raises(self):
        """Calling media_geometrica() on empty list raises ValueError."""
        c = CoherenciaDerivacionBeta()
        with pytest.raises(ValueError):
            c.media_geometrica()

    def test_media_geometrica_zero_psi_returns_zero(self):
        """A zero Ψ_i makes the geometric mean 0."""
        c = CoherenciaDerivacionBeta()
        c.agregar(0.9)
        c.agregar(0.0)
        assert c.media_geometrica() == 0.0

    def test_agregar_clips_above_one(self):
        """Values > 1 are clipped to 1.0."""
        c = CoherenciaDerivacionBeta()
        c.agregar(1.5)
        assert c.psis[0] == pytest.approx(1.0)

    def test_agregar_clips_below_zero(self):
        """Values < 0 are clipped to 0.0."""
        c = CoherenciaDerivacionBeta()
        c.agregar(-0.3)
        assert c.psis[0] == pytest.approx(0.0)

    def test_es_coherente_true(self):
        """es_coherente() must return True when Ψ_global ≥ 0.888."""
        c = CoherenciaDerivacionBeta(psis=[0.95, 0.95, 0.95])
        assert c.es_coherente() is True

    def test_es_coherente_false(self):
        """es_coherente() must return False when Ψ_global < 0.888."""
        c = CoherenciaDerivacionBeta(psis=[0.5, 0.5])
        assert c.es_coherente() is False

    def test_media_geometrica_all_ones(self):
        """Geometric mean of ones is 1."""
        c = CoherenciaDerivacionBeta(psis=[1.0, 1.0, 1.0])
        assert c.media_geometrica() == pytest.approx(1.0)


# ===========================================================================
# VIII. SistemaDerivacionBetaAdelica
# ===========================================================================

class TestSistemaDerivacionBetaAdelica:
    """Tests for the main orchestrator."""

    @pytest.fixture(scope="class")
    def sistema(self):
        """Default system instance."""
        return SistemaDerivacionBetaAdelica()

    @pytest.fixture(scope="class")
    def resultado(self, sistema):
        """Full execution result."""
        return sistema.ejecutar(verbose=False)

    def test_ejecutar_returns_result_type(self, resultado):
        """ejecutar() must return ResultadoSistemaDerivacionBeta."""
        assert isinstance(resultado, ResultadoSistemaDerivacionBeta)

    def test_alpha_derivada_close_to_experimental(self, resultado):
        """α_derivada must equal α_experimental within ALPHA_TOLERANCIA."""
        assert abs(resultado.alpha_derivada - ALPHA_EXPERIMENTAL) < ALPHA_TOLERANCIA

    def test_psi_global_range(self, resultado):
        """Ψ_global must be in [0, 1]."""
        assert 0.0 <= resultado.psi_global <= 1.0

    def test_es_coherente(self, resultado):
        """Default system must be coherent (Ψ_global ≥ 0.888)."""
        assert resultado.es_coherente is True

    def test_psi_adelico_range(self, resultado):
        """Ψ_adélico must be in [0, 1]."""
        assert 0.0 <= resultado.psi_adelico <= 1.0

    def test_psi_cy_is_one(self, resultado):
        """Ψ_CY must be 1.0 for default v6=6."""
        assert resultado.psi_cy == pytest.approx(1.0, rel=1e-10)

    def test_psi_beta_high(self, resultado):
        """Ψ_beta must be ≥ 0.99 for the exact derivation."""
        assert resultado.psi_beta >= 0.99

    def test_theta_T_positive(self, resultado):
        """θ_T must be positive."""
        assert resultado.theta_T > 0.0

    def test_fr_mat_small(self, resultado):
        """fr_mat = 1/α must be close to 7.3e-3."""
        assert abs(resultado.fr_mat - 7.3e-3) < 1e-3

    def test_sello(self, resultado):
        """Sello must be '∴DBA∞³'."""
        assert resultado.sello == "∴DBA∞³"

    def test_ram(self, resultado):
        """RAM must be the expected identifier."""
        assert resultado.ram == "RAM-LI-2026-DERIVACION-BETA-ADELICA"

    def test_pi_ad_range(self, resultado):
        """Π_ad must be in (0, 1)."""
        assert 0.0 < resultado.pi_ad < 1.0

    def test_fv_positive(self, resultado):
        """fv must be positive."""
        assert resultado.fv > 0.0

    def test_producto_euler_nonzero(self, resultado):
        """Euler product must be nonzero."""
        assert abs(resultado.producto_euler) > 0.0

    def test_psi_torsion_is_one_for_default_alpha(self, resultado):
        """Ψ_torsion must be 1.0 when derived α ≈ α_experimental."""
        assert resultado.psi_torsion == pytest.approx(1.0, rel=1e-6)

    def test_custom_v6_changes_fv(self):
        """Custom v6 must change fv proportionally."""
        s12 = SistemaDerivacionBetaAdelica(v6=12.0)
        r12 = s12.ejecutar(verbose=False)
        s6 = SistemaDerivacionBetaAdelica(v6=6.0)
        r6 = s6.ejecutar(verbose=False)
        assert r12.fv == pytest.approx(2.0 * r6.fv, rel=1e-10)


# ===========================================================================
# Convenience function
# ===========================================================================

class TestEjecutarDerivacionBetaAdelica:
    """Tests for the public convenience function."""

    def test_returns_result_type(self):
        """Function must return ResultadoSistemaDerivacionBeta."""
        result = ejecutar_derivacion_beta_adelica(verbose=False)
        assert isinstance(result, ResultadoSistemaDerivacionBeta)

    def test_es_coherente(self):
        """Result must be coherent."""
        result = ejecutar_derivacion_beta_adelica(verbose=False)
        assert result.es_coherente is True

    def test_alpha_derivada_range(self):
        """Derived α must be in [137.0, 138.0]."""
        result = ejecutar_derivacion_beta_adelica(verbose=False)
        assert 137.0 < result.alpha_derivada < 138.0

    def test_verbose_runs_without_error(self, capsys):
        """Running with verbose=True must not raise."""
        ejecutar_derivacion_beta_adelica(verbose=True)
        captured = capsys.readouterr()
        assert "DBA" in captured.out
