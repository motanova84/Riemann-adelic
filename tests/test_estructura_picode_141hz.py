#!/usr/bin/env python3
"""
Tests for reloj_universo_f0.py and modulo_holograma_141hz.py
=============================================================

39 tests covering:
  - Riemann-derived constants in reloj_universo_f0
  - Bekenstein-Hawking holographic bit counting
  - Polar zeta spiral (espiral_zeta_polar)
  - Holographic coherence (Gaussian decay)
  - Lunar-bounce simulation and FFT analysis

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
"""

import math
import importlib.util
from pathlib import Path

import pytest

# ---------------------------------------------------------------------------
# Direct module loading (avoids __init__ chain issues, consistent with repo)
# ---------------------------------------------------------------------------
_ROOT = Path(__file__).parent.parent

_spec_reloj = importlib.util.spec_from_file_location(
    "reloj_universo_f0",
    _ROOT / "reloj_universo_f0.py",
)
reloj = importlib.util.module_from_spec(_spec_reloj)
_spec_reloj.loader.exec_module(reloj)

_spec_holo = importlib.util.spec_from_file_location(
    "modulo_holograma_141hz",
    _ROOT / "modulo_holograma_141hz.py",
)
holo = importlib.util.module_from_spec(_spec_holo)
_spec_holo.loader.exec_module(holo)


# ===========================================================================
# Helper tolerance
# ===========================================================================
RTOL = 1e-9   # tight relative tolerance for exact relations
ATOL = 1e-12  # absolute tolerance for very small quantities


# ===========================================================================
# Part I — reloj_universo_f0 constants (tests 1-20)
# ===========================================================================

class TestGamma1:
    """Tests 1-5: GAMMA_1 value and precision."""

    def test_gamma1_positive(self):
        """Test 1: γ₁ is a positive real number."""
        assert reloj.GAMMA_1 > 0

    def test_gamma1_known_digits(self):
        """Test 2: γ₁ matches the known value 14.1347... to 10 decimal places."""
        assert abs(reloj.GAMMA_1 - 14.134725141734) < 1e-10

    def test_gamma1_str_starts_with_known(self):
        """Test 3: GAMMA_1_STR starts with correct decimal expansion."""
        assert reloj.GAMMA_1_STR.startswith("14.134725141734693")

    def test_gamma1_str_length_sufficient(self):
        """Test 4: GAMMA_1_STR has at least 50 significant characters."""
        digits = reloj.GAMMA_1_STR.replace(".", "")
        assert len(digits) >= 49  # 50 sig digits minus the dot

    def test_gamma1_float_matches_str(self):
        """Test 5: float(GAMMA_1) is consistent with GAMMA_1_STR."""
        from_str = float(reloj.GAMMA_1_STR)
        assert abs(reloj.GAMMA_1 - from_str) < 1e-12


class TestMultiplicadorTuyoyotu:
    """Tests 6-8: MULTIPLICADOR_TUYOYOTU."""

    def test_multiplicador_value(self):
        """Test 6: Tuyoyotu multiplier equals 10.025."""
        assert reloj.MULTIPLICADOR_TUYOYOTU == 10.025

    def test_multiplicador_is_10_plus_1_over_40(self):
        """Test 7: 10.025 == 10 + 1/40 (exact rational)."""
        assert math.isclose(reloj.MULTIPLICADOR_TUYOYOTU, 10 + 1 / 40, rel_tol=1e-15)

    def test_multiplicador_type(self):
        """Test 8: Tuyoyotu multiplier is a float."""
        assert isinstance(reloj.MULTIPLICADOR_TUYOYOTU, float)


class TestF0ExactHz:
    """Tests 9-13: F0_EXACT_HZ derivation."""

    def test_f0_exact_formula(self):
        """Test 9: F0_EXACT_HZ = GAMMA_1 * MULTIPLICADOR_TUYOYOTU."""
        expected = reloj.GAMMA_1 * reloj.MULTIPLICADOR_TUYOYOTU
        assert math.isclose(reloj.F0_EXACT_HZ, expected, rel_tol=RTOL)

    def test_f0_exact_approx_value(self):
        """Test 10: F0_EXACT_HZ ≈ 141.7006 Hz."""
        assert 141.699 < reloj.F0_EXACT_HZ < 141.702

    def test_f0_exact_close_to_operative(self):
        """Test 11: F0_EXACT_HZ is very close to operative F0_HZ."""
        assert abs(reloj.F0_EXACT_HZ - reloj.F0_HZ) < 0.01

    def test_f0_exact_greater_than_operative(self):
        """Test 12: F0_EXACT_HZ > F0_HZ (exact > operative)."""
        assert reloj.F0_EXACT_HZ > reloj.F0_HZ

    def test_f0_exact_numeric_precision(self):
        """Test 13: F0_EXACT_HZ matches expected value to 8 decimal places."""
        assert abs(reloj.F0_EXACT_HZ - 141.70061954) < 1e-7


class TestDeltaFaseZiusudra:
    """Tests 14-16: DELTA_FASE_ZIUSUDRA."""

    def test_delta_fase_formula(self):
        """Test 14: DELTA_FASE_ZIUSUDRA = GAMMA_1 / 40."""
        expected = reloj.GAMMA_1 / 40.0
        assert math.isclose(reloj.DELTA_FASE_ZIUSUDRA, expected, rel_tol=RTOL)

    def test_delta_fase_approx_value(self):
        """Test 15: DELTA_FASE_ZIUSUDRA ≈ 0.3534 Hz."""
        assert 0.353 < reloj.DELTA_FASE_ZIUSUDRA < 0.354

    def test_delta_fase_positive(self):
        """Test 16: DELTA_FASE_ZIUSUDRA is positive."""
        assert reloj.DELTA_FASE_ZIUSUDRA > 0


class TestFisuraZiusudra:
    """Tests 17-19: FISURA_ZIUSUDRA."""

    def test_fisura_formula(self):
        """Test 17: FISURA_ZIUSUDRA = F0_EXACT_HZ - F0_HZ."""
        expected = reloj.F0_EXACT_HZ - reloj.F0_HZ
        assert math.isclose(reloj.FISURA_ZIUSUDRA, expected, rel_tol=RTOL)

    def test_fisura_magnitude(self):
        """Test 18: |FISURA_ZIUSUDRA| is on the order of 5×10⁻⁴ Hz."""
        assert 1e-4 < abs(reloj.FISURA_ZIUSUDRA) < 5e-3

    def test_fisura_positive(self):
        """Test 19: FISURA_ZIUSUDRA > 0 (exact is above operative)."""
        assert reloj.FISURA_ZIUSUDRA > 0


class TestF0OctavaHz:
    """Test 20: F0_OCTAVA_HZ."""

    def test_f0_octava_value(self):
        """Test 20: F0_OCTAVA_HZ == 151.7001 Hz."""
        assert reloj.F0_OCTAVA_HZ == 151.7001


class TestConstantesFisicas:
    """Tests 21-25: CONSTANTES_FISICAS dictionary."""

    def test_dict_has_gamma1(self):
        """Test 21: CONSTANTES_FISICAS contains GAMMA_1."""
        assert "GAMMA_1" in reloj.CONSTANTES_FISICAS

    def test_dict_has_f0_exact(self):
        """Test 22: CONSTANTES_FISICAS contains F0_EXACT_HZ."""
        assert "F0_EXACT_HZ" in reloj.CONSTANTES_FISICAS

    def test_dict_has_fisura(self):
        """Test 23: CONSTANTES_FISICAS contains FISURA_ZIUSUDRA."""
        assert "FISURA_ZIUSUDRA" in reloj.CONSTANTES_FISICAS

    def test_dict_has_octava(self):
        """Test 24: CONSTANTES_FISICAS contains F0_OCTAVA_HZ."""
        assert "F0_OCTAVA_HZ" in reloj.CONSTANTES_FISICAS

    def test_dict_values_consistent(self):
        """Test 25: Dictionary values match module-level constants."""
        cf = reloj.CONSTANTES_FISICAS
        assert cf["GAMMA_1"] == reloj.GAMMA_1
        assert cf["F0_EXACT_HZ"] == reloj.F0_EXACT_HZ
        assert cf["DELTA_FASE_ZIUSUDRA"] == reloj.DELTA_FASE_ZIUSUDRA
        assert cf["FISURA_ZIUSUDRA"] == reloj.FISURA_ZIUSUDRA
        assert cf["F0_OCTAVA_HZ"] == reloj.F0_OCTAVA_HZ


# ===========================================================================
# Part II — modulo_holograma_141hz functions (tests 26-39)
# ===========================================================================

class TestAreaEfectivaHolografica:
    """Tests 26-28: area_efectiva_holografica."""

    def test_unit_sphere(self):
        """Test 26: Area of unit sphere is 4π."""
        area = holo.area_efectiva_holografica(1.0)
        assert math.isclose(area, 4 * math.pi, rel_tol=1e-12)

    def test_scales_with_radius_squared(self):
        """Test 27: Area scales as r²."""
        a1 = holo.area_efectiva_holografica(1.0e6)
        a2 = holo.area_efectiva_holografica(2.0e6)
        assert math.isclose(a2 / a1, 4.0, rel_tol=1e-10)

    def test_negative_radius_raises(self):
        """Test 28: Non-positive radius raises ValueError."""
        with pytest.raises(ValueError):
            holo.area_efectiva_holografica(-1.0)


class TestBitsHolograficosPlanck:
    """Tests 29-31: bits_holograficos_planck."""

    def test_positive_bits(self):
        """Test 29: Bit count is positive for positive area."""
        bits = holo.bits_holograficos_planck(4.48e12)
        assert bits > 0

    def test_linear_scaling(self):
        """Test 30: Bit count scales linearly with area."""
        b1 = holo.bits_holograficos_planck(1.0e12)
        b2 = holo.bits_holograficos_planck(2.0e12)
        assert math.isclose(b2 / b1, 2.0, rel_tol=1e-10)

    def test_zero_area_raises(self):
        """Test 31: Zero area raises ValueError."""
        with pytest.raises(ValueError):
            holo.bits_holograficos_planck(0.0)


class TestEspiralZetaPolar:
    """Tests 32-34: espiral_zeta_polar."""

    def test_at_theta_zero(self):
        """Test 32: r(0) = F0 (spiral originates at carrier frequency)."""
        r = holo.espiral_zeta_polar(gamma_n=reloj.GAMMA_1, theta=0.0)
        assert math.isclose(r, holo.F0_EXACT_HZ, rel_tol=1e-12)

    def test_monotone_increasing_positive_theta(self):
        """Test 33: Spiral is monotonically increasing for θ > 0."""
        r1 = holo.espiral_zeta_polar(reloj.GAMMA_1, 1.0)
        r2 = holo.espiral_zeta_polar(reloj.GAMMA_1, 2.0)
        assert r2 > r1 > 0

    def test_invalid_f0_raises(self):
        """Test 34: f0 ≤ 0 raises ValueError."""
        with pytest.raises(ValueError):
            holo.espiral_zeta_polar(gamma_n=14.0, theta=1.0, f0=0.0)


class TestCoherenciaHolografica:
    """Tests 35-37: coherencia_holografica."""

    def test_peak_at_f0_exact(self):
        """Test 35: Ψ = 1 at F0_EXACT_HZ."""
        psi = holo.coherencia_holografica(holo.F0_EXACT_HZ)
        assert math.isclose(psi, 1.0, rel_tol=1e-15)

    def test_decays_away_from_centre(self):
        """Test 36: Ψ < 1 away from F0_EXACT_HZ."""
        psi_off = holo.coherencia_holografica(holo.F0_EXACT_HZ + 1.0)
        assert psi_off < 1.0

    def test_gaussian_width(self):
        """Test 37: Ψ = 1/e at |f − F0_EXACT| = DELTA_F_VORTICE."""
        freq = holo.F0_EXACT_HZ + holo.DELTA_F_VORTICE
        psi = holo.coherencia_holografica(freq)
        assert math.isclose(psi, math.exp(-1.0), rel_tol=1e-12)


class TestSimularEcoLunar:
    """Test 38: simular_eco_lunar."""

    def test_output_shape(self):
        """Test 38: Output arrays have the correct length."""
        t, s = holo.simular_eco_lunar(duracion_s=1.0, fs=500.0)
        assert len(t) == 500
        assert len(s) == 500


class TestAnalizarFftMoonbounce:
    """Test 39: analizar_fft_moonbounce."""

    def test_peak_near_f0_exact(self):
        """Test 39: FFT peak is within 1 Hz of F0_EXACT_HZ for clean signal."""
        _, s = holo.simular_eco_lunar(duracion_s=10.0, fs=1000.0)
        res = holo.analizar_fft_moonbounce(s, fs=1000.0)
        assert res["delta_f"] < 1.0
        assert 0.0 < res["psi_proxy"] <= 1.0
        assert isinstance(res["n_samples"], int)
        assert res["n_samples"] == 10000
