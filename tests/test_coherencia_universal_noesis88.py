#!/usr/bin/env python3
"""
Tests for operators/coherencia_universal_noesis88.py
=====================================================

Tests the four-pillar Teorema de la Coherencia Universal (noesis88):

  Pillar I  — η⁺ positivity via Unitarity (Higgs vacuum stability)
  Pillar II — Selberg Trace Formula + Calabi-Yau topology
  Pillar III — GUE ergodicity + Lorentz invariance
  Pillar IV — Teorema de la Coherencia Universal (synthesis)

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz · C = 244.36
DOI: 10.5281/zenodo.17379721
Signature: ∴𓂀Ω∞³Φ
"""

import importlib.util
import sys
from pathlib import Path

import numpy as np
import pytest

# ---------------------------------------------------------------------------
# Load module directly to avoid operators/__init__.py eager imports
# ---------------------------------------------------------------------------
PROJECT_ROOT = Path(__file__).parent.parent
_spec = importlib.util.spec_from_file_location(
    "coherencia_universal_noesis88",
    PROJECT_ROOT / "operators" / "coherencia_universal_noesis88.py",
)
cun = importlib.util.module_from_spec(_spec)
sys.modules["coherencia_universal_noesis88"] = cun
_spec.loader.exec_module(cun)


# ---------------------------------------------------------------------------
# Module constants
# ---------------------------------------------------------------------------

class TestConstants:
    """Verify module-level constants."""

    def test_f0_hz(self):
        assert cun.F0_QCAL == pytest.approx(141.7001, rel=1e-6)

    def test_c_qcal(self):
        assert cun.C_QCAL == pytest.approx(244.36, rel=1e-6)

    def test_g_eff_calabi_yau(self):
        assert cun.G_EFF_CALABI_YAU == pytest.approx(0.053, rel=1e-6)

    def test_lorentz_precision(self):
        assert cun.LORENTZ_PRECISION == pytest.approx(1e-18, rel=1e-6)

    def test_riemann_zeros_array(self):
        assert len(cun.RIEMANN_ZEROS) >= 30
        # All zeros should be positive
        assert np.all(cun.RIEMANN_ZEROS > 0)
        # First zero near 14.134725
        assert cun.RIEMANN_ZEROS[0] == pytest.approx(14.134725, rel=1e-4)


# ---------------------------------------------------------------------------
# Pillar I — η⁺ Positivity via Unitarity
# ---------------------------------------------------------------------------

class TestPillarI:
    """Tests for η⁺ positivity (unitarity principle)."""

    def test_on_critical_line_preserves_unitarity(self):
        result = cun.check_unitarity_violation(re_rho=0.5, t=1.0)
        assert result.unitarity_preserved
        assert result.deviation_re == pytest.approx(0.0, abs=1e-12)
        assert result.norm_squared == pytest.approx(1.0, rel=1e-10)

    def test_off_critical_line_violates_unitarity(self):
        result = cun.check_unitarity_violation(re_rho=0.75, t=1.0)
        assert not result.unitarity_preserved
        assert result.norm_squared != pytest.approx(1.0, rel=1e-3)

    def test_prove_eta_plus_positivity_returns_dict(self):
        proof = cun.prove_eta_plus_positivity()
        assert isinstance(proof, dict)
        assert proof["pillar"] == "I"
        assert proof["eta_plus_positive"] is True
        assert proof["all_on_critical_line_unitary"] is True

    def test_off_line_example_violates(self):
        proof = cun.prove_eta_plus_positivity()
        assert proof["off_line_example"]["violates_unitarity"] is True

    def test_custom_zeros(self):
        zeros = np.array([14.134725, 21.022040])
        proof = cun.prove_eta_plus_positivity(zeros=zeros)
        assert proof["n_zeros_checked"] == 2

    def test_unitarity_at_various_t(self):
        for t in [0.1, 1.0, 5.0, 10.0]:
            result = cun.check_unitarity_violation(re_rho=0.5, t=t)
            assert result.unitarity_preserved, f"Unitarity should hold at t={t}"

    def test_violation_grows_with_t(self):
        r1 = cun.check_unitarity_violation(re_rho=0.6, t=1.0)
        r2 = cun.check_unitarity_violation(re_rho=0.6, t=5.0)
        assert abs(r2.norm_squared - 1.0) > abs(r1.norm_squared - 1.0)


# ---------------------------------------------------------------------------
# Pillar II — Selberg Trace Formula + Calabi-Yau
# ---------------------------------------------------------------------------

class TestPillarII:
    """Tests for the Selberg-Calabi-Yau identity."""

    def test_gaussian_h_peak_at_zero(self):
        assert cun._gaussian_h(0.0, sigma=5.0) == pytest.approx(1.0, rel=1e-10)

    def test_gaussian_h_decays(self):
        assert cun._gaussian_h(0.0, 5.0) > cun._gaussian_h(14.0, 5.0)

    def test_gaussian_g_hat_peak_at_zero(self):
        val = cun._gaussian_g_hat(0.0, sigma=5.0)
        import math
        expected = 5.0 * math.sqrt(2.0 * math.pi)
        assert val == pytest.approx(expected, rel=1e-8)

    def test_gaussian_g_hat_decays(self):
        assert cun._gaussian_g_hat(0.0, 5.0) > cun._gaussian_g_hat(1.0, 5.0)

    def test_selberg_result_type(self):
        result = cun.compute_selberg_trace()
        assert hasattr(result, "spectral_sum")
        assert hasattr(result, "prime_sum")
        assert hasattr(result, "g_eff_correction")
        assert hasattr(result, "relative_error")
        assert hasattr(result, "identity_holds")

    def test_selberg_identity_holds(self):
        result = cun.compute_selberg_trace()
        assert result.identity_holds, (
            f"Selberg identity failed: rel_err={result.relative_error:.4f}"
        )

    def test_selberg_g_eff_applied(self):
        r_no_corr = cun.compute_selberg_trace(g_eff=0.0)
        r_with_corr = cun.compute_selberg_trace(g_eff=cun.G_EFF_CALABI_YAU)
        # With correction the prime sum should be larger
        assert r_with_corr.prime_sum >= r_no_corr.prime_sum

    def test_prove_selberg_calabi_yau_identity(self):
        proof = cun.prove_selberg_calabi_yau_identity()
        assert proof["pillar"] == "II"
        assert bool(proof["identity_holds"]) is True
        assert proof["g_eff_calabi_yau"] == pytest.approx(0.053, rel=1e-6)


# ---------------------------------------------------------------------------
# Pillar III — GUE Ergodicity + Lorentz Stability
# ---------------------------------------------------------------------------

class TestPillarIII:
    """Tests for GUE ergodicity and Lorentz invariance stability."""

    def test_gue_result_type(self):
        result = cun.test_gue_ergodicity()
        assert hasattr(result, "spacings")
        assert hasattr(result, "ks_statistic")
        assert hasattr(result, "ks_p_value")
        assert hasattr(result, "gue_consistent")

    def test_spacings_non_negative(self):
        result = cun.test_gue_ergodicity()
        assert np.all(result.spacings >= 0)

    def test_spacings_normalised(self):
        result = cun.test_gue_ergodicity()
        # Mean spacing should be close to 1 after normalisation
        assert np.mean(result.spacings) == pytest.approx(1.0, rel=0.05)

    def test_gue_consistent(self):
        result = cun.test_gue_ergodicity()
        assert result.gue_consistent, (
            f"GUE consistency failed: KS={result.ks_statistic:.4f}"
        )

    def test_lorentz_consistent(self):
        result = cun.test_gue_ergodicity(
            lorentz_bound=cun.LORENTZ_PRECISION
        )
        assert result.lorentz_consistent

    def test_lorentz_too_large_fails(self):
        result = cun.test_gue_ergodicity(lorentz_bound=1.0)
        assert not result.lorentz_consistent

    def test_prove_ergodicity_stability(self):
        proof = cun.prove_ergodicity_stability()
        assert proof["pillar"] == "III"
        assert proof["gue_consistent"] is True
        assert proof["lorentz_consistent"] is True

    def test_wigner_surmise_cdf_at_zero(self):
        cdf0 = cun._wigner_surmise_cdf(np.array([0.0]))[0]
        assert cdf0 == pytest.approx(0.0, abs=1e-10)

    def test_wigner_surmise_cdf_monotone(self):
        s = np.linspace(0.0, 3.0, 50)
        cdf = cun._wigner_surmise_cdf(s)
        assert np.all(np.diff(cdf) >= 0)


# ---------------------------------------------------------------------------
# Pillar IV — Teorema de la Coherencia Universal
# ---------------------------------------------------------------------------

class TestPillarIV:
    """Tests for the synthesis theorem."""

    def test_prove_coherencia_universal_returns_result(self):
        result = cun.prove_coherencia_universal()
        assert hasattr(result, "theorem_holds")
        assert hasattr(result, "pillar_I")
        assert hasattr(result, "pillar_II")
        assert hasattr(result, "pillar_III")
        assert hasattr(result, "summary")

    def test_theorem_holds(self):
        result = cun.prove_coherencia_universal()
        assert result.theorem_holds, f"Theorem failed:\n{result.summary}"

    def test_qcal_constants_in_result(self):
        result = cun.prove_coherencia_universal()
        assert result.f0_hz == pytest.approx(141.7001, rel=1e-6)
        assert result.c_coherence == pytest.approx(244.36, rel=1e-6)

    def test_summary_contains_proven(self):
        result = cun.prove_coherencia_universal()
        assert "PROVEN" in result.summary

    def test_validate_wrapper(self):
        result = cun.validate_coherencia_universal_noesis88(verbose=False)
        assert result.theorem_holds


# ---------------------------------------------------------------------------
# Integration test
# ---------------------------------------------------------------------------

class TestIntegration:
    """Cross-pillar integration checks."""

    def test_all_pillars_consistent(self):
        result = cun.prove_coherencia_universal()
        assert result.pillar_I["eta_plus_positive"]
        assert result.pillar_II["identity_holds"]
        assert result.pillar_III["gue_consistent"]
        assert result.pillar_III["lorentz_consistent"]

    def test_theorem_implies_all_pillars(self):
        result = cun.prove_coherencia_universal()
        if result.theorem_holds:
            assert result.pillar_I["eta_plus_positive"]
            assert result.pillar_II["identity_holds"]
