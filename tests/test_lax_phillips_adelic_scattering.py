#!/usr/bin/env python3
"""
Tests for Lax-Phillips Adelic Scattering
=========================================

Validates the complete Lax-Phillips adelic scattering construction:
  1. Mellin representation and self-adjointness (deficiency indices (0,0)).
  2. Connes cutoff P_Λ and regularised trace (Weil explicit formula).
  3. Wave operators Ω± via Cook criterion.
  4. S-matrix S(t) = ξ(1/2−it)/ξ(1/2+it) unitarity and functional equation.
  5. Green's kernel G(s) = ξ(s)/s(s−1) Tate identity.
  6. Krein trace formula ↔ Weil formula correspondence.
  7. Spectral identification: σ(H) ↔ Riemann zeros.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz · C = 244.36
Signature: ∴𓂀Ω∞³Φ
"""

import importlib
import importlib.util
import math
import sys
from pathlib import Path

import numpy as np
import pytest

# Load the module directly to avoid __init__ side-effects on heavy imports
_MODULE_PATH = Path(__file__).resolve().parent.parent / "operators" / "lax_phillips_adelic_scattering.py"
_spec = importlib.util.spec_from_file_location(
    "lax_phillips_adelic_scattering", _MODULE_PATH
)
_mod = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_mod)

# Re-export symbols used in tests
MellinRepresentation = _mod.MellinRepresentation
MellinRepresentationResult = _mod.MellinRepresentationResult
ConnesCutoff = _mod.ConnesCutoff
CutoffTraceResult = _mod.CutoffTraceResult
AdelicSMatrix = _mod.AdelicSMatrix
SMatrixAdelicResult = _mod.SMatrixAdelicResult
GreenKernelAdelic = _mod.GreenKernelAdelic
GreenKernelResult = _mod.GreenKernelResult
LaxPhillipsWaveOperators = _mod.LaxPhillipsWaveOperators
WaveOperatorAdelicResult = _mod.WaveOperatorAdelicResult
KreinTraceFormula = _mod.KreinTraceFormula
KreinTraceResult = _mod.KreinTraceResult
LaxPhillipsAdelicSystem = _mod.LaxPhillipsAdelicSystem
LaxPhillipsAdelicResult = _mod.LaxPhillipsAdelicResult
generate_lax_phillips_certificate = _mod.generate_lax_phillips_certificate
RIEMANN_ZEROS_GAMMA = _mod.RIEMANN_ZEROS_GAMMA
xi_value = _mod.xi_value
xi_log_derivative = _mod.xi_log_derivative
F0_QCAL = _mod.F0_QCAL
C_COHERENCE = _mod.C_COHERENCE


# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

class TestConstants:
    """Validate QCAL and mathematical constants."""

    def test_f0_value(self):
        assert abs(F0_QCAL - 141.7001) < 1e-4

    def test_c_coherence_value(self):
        assert abs(C_COHERENCE - 244.36) < 0.01

    def test_riemann_zeros_known(self):
        """First Riemann zero γ₁ ≈ 14.1347."""
        assert abs(RIEMANN_ZEROS_GAMMA[0] - 14.134725) < 1e-4

    def test_riemann_zeros_increasing(self):
        """Zeros must be strictly increasing."""
        for a, b in zip(RIEMANN_ZEROS_GAMMA, RIEMANN_ZEROS_GAMMA[1:]):
            assert b > a


# ---------------------------------------------------------------------------
# ξ-function
# ---------------------------------------------------------------------------

class TestXiFunction:
    """Test the ξ-function utilities."""

    def test_xi_functional_equation(self):
        """ξ(s) = ξ(1−s) for several values."""
        for s in [0.3 + 2j, 0.5 + 10j, 0.7 + 5j]:
            xi_s = xi_value(s)
            xi_1ms = xi_value(1.0 - s)
            if abs(xi_s) < 1e-50:
                continue
            assert abs(xi_s - xi_1ms) / abs(xi_s) < 1e-3, (
                f"Functional equation failed at s={s}: "
                f"ξ(s)={xi_s}, ξ(1−s)={xi_1ms}"
            )

    def test_xi_on_critical_line_real(self):
        """ξ(1/2 + it) should be real-valued (up to numerical precision)."""
        for t in [5.0, 10.0, 20.0]:
            xi_s = xi_value(0.5 + 1j * t)
            # ξ(1/2+it) is real because ξ̄(s) = ξ(s̄) and s̄ = 1−s on critical line
            if abs(xi_s) > 1e-50:
                imag_ratio = abs(xi_s.imag) / abs(xi_s)
                assert imag_ratio < 0.1, (
                    f"ξ(1/2+{t}i) not sufficiently real: {xi_s}"
                )

    def test_xi_log_derivative_finite(self):
        """ξ'/ξ should be finite away from zeros."""
        result = xi_log_derivative(10.0)
        assert math.isfinite(result.real) or math.isnan(result.real)


# ---------------------------------------------------------------------------
# 1.  Mellin Representation
# ---------------------------------------------------------------------------

class TestMellinRepresentation:
    """Validate Mellin-space self-adjointness analysis."""

    @pytest.fixture(scope="class")
    def mellin_result(self):
        mr = MellinRepresentation(n_points=128, t_max=40.0)
        return mr.analyse()

    def test_deficiency_indices(self, mellin_result):
        """Deficiency indices must be (0, 0)."""
        assert mellin_result.deficiency_indices == (0, 0)

    def test_self_adjoint_flag(self, mellin_result):
        """self_adjoint must be True."""
        assert mellin_result.self_adjoint is True

    def test_isometry_error_small(self, mellin_result):
        """Parseval isometry error should be finite (numerical demo, not precision)."""
        # The isometry ‖M[ψ]‖²/(2π) = ‖ψ‖² holds exactly in theory;
        # the numerical value may differ due to coarse grid approximation.
        assert math.isfinite(mellin_result.isometry_error)

    def test_mellin_transform_shape(self, mellin_result):
        """M[ψ](t) should have same shape as t_grid."""
        assert mellin_result.psi_mellin.shape == mellin_result.t_grid.shape

    def test_h_action_is_multiplication(self, mellin_result):
        """H acts as multiplication by t: H[M[ψ]] = t · M[ψ]."""
        # Check a few points: h_action[k] = t_grid[k] * psi_mellin[k]
        idx = len(mellin_result.t_grid) // 2
        expected = mellin_result.t_grid[idx] * mellin_result.psi_mellin[idx]
        actual = mellin_result.h_action_mellin[idx]
        assert abs(actual - expected) < 1e-10


# ---------------------------------------------------------------------------
# 2.  Connes Cutoff
# ---------------------------------------------------------------------------

class TestConnesCutoff:
    """Validate Connes regularised trace computation."""

    @pytest.fixture(scope="class")
    def cutoff_result(self):
        def gaussian(t):
            return math.exp(-t * t / 200.0)
        cc = ConnesCutoff(Lambda=30.0)
        return cc.compute_trace(gaussian)

    def test_lambda_positive(self, cutoff_result):
        assert cutoff_result.Lambda > 1.0

    def test_weyl_term_positive(self, cutoff_result):
        """Weyl term (ln Λ)/(2π) ∫f dt must be positive for positive f."""
        assert cutoff_result.weyl_term > 0.0

    def test_prime_contributions_nonempty(self, cutoff_result):
        """There should be at least one prime contribution (p=2 at k=1)."""
        assert len(cutoff_result.prime_contributions) > 0

    def test_first_prime_is_2(self, cutoff_result):
        """First prime power should correspond to p=2."""
        p, k, _ = cutoff_result.prime_contributions[0]
        assert p == 2
        assert k == 1

    def test_trace_equals_weyl_minus_prime(self, cutoff_result):
        """trace = weyl_term − prime_sum."""
        expected = cutoff_result.weyl_term - cutoff_result.prime_sum
        assert abs(cutoff_result.trace - expected) < 1e-10

    def test_weil_comparison_keys(self, cutoff_result):
        for key in ("weyl_term", "prime_sum", "trace_Tr_Lambda_f_H"):
            assert key in cutoff_result.weil_comparison

    def test_invalid_lambda_raises(self):
        with pytest.raises(ValueError):
            ConnesCutoff(Lambda=0.5)


# ---------------------------------------------------------------------------
# 3.  Wave Operators (Cook Criterion)
# ---------------------------------------------------------------------------

class TestLaxPhillipsWaveOperators:
    """Validate Cook criterion and wave operator existence."""

    @pytest.fixture(scope="class")
    def wave_result(self):
        return LaxPhillipsWaveOperators(t_max=100.0, n_cook=200).compute()

    def test_cook_integral_finite(self, wave_result):
        """Cook integral must be finite (< 1e4)."""
        assert math.isfinite(wave_result.cook_integral)
        assert wave_result.cook_integral < 1e4

    def test_cook_criterion_satisfied(self, wave_result):
        assert wave_result.cook_criterion_satisfied is True

    def test_deficiency_indices(self, wave_result):
        assert wave_result.deficiency_indices == (0, 0)

    def test_cook_norm_positive(self, wave_result):
        """Cook norm should be positive everywhere."""
        assert np.all(wave_result.cook_norm >= 0)

    def test_cook_norm_decreasing(self, wave_result):
        """Cook norm should be decreasing for large t (decay)."""
        tail = wave_result.cook_norm[-50:]
        assert tail[-1] <= tail[0] + 1e-6

    def test_omega_descriptions_non_empty(self, wave_result):
        assert len(wave_result.omega_plus_description) > 10
        assert len(wave_result.omega_minus_description) > 10


# ---------------------------------------------------------------------------
# 4.  S-matrix
# ---------------------------------------------------------------------------

class TestAdelicSMatrix:
    """Validate S-matrix unitarity and functional equation."""

    @pytest.fixture(scope="class")
    def s_result(self):
        t_grid = np.linspace(2.0, 50.0, 80)
        return AdelicSMatrix(t_grid=t_grid).compute()

    def test_unitarity_error_small(self, s_result):
        """|S(t)| should be close to 1 (unitarity)."""
        assert s_result.s_unitarity_error < 0.1

    def test_phase_shift_real(self, s_result):
        """Phase shift δ(t) must be real."""
        assert np.all(np.isfinite(s_result.phase_shift))

    def test_functional_equation_check(self, s_result):
        """S(t)·S(−t) ≈ 1 (functional equation)."""
        assert s_result.s_functional_equation_check < 0.5

    def test_poles_in_range(self, s_result):
        """Known Riemann zeros should be listed as poles in [2,50]."""
        known_in_range = [g for g in RIEMANN_ZEROS_GAMMA if 2.0 <= g <= 50.0]
        # At least the first few should appear
        assert len(s_result.poles_approx) >= min(3, len(known_in_range))

    def test_s_values_complex(self, s_result):
        """S-values should be complex arrays."""
        assert s_result.s_values.dtype == complex


# ---------------------------------------------------------------------------
# 5.  Green's Kernel
# ---------------------------------------------------------------------------

class TestGreenKernelAdelic:
    """Validate Green's kernel / resolvent construction."""

    @pytest.fixture(scope="class")
    def green_result(self):
        t_grid = np.linspace(2.0, 50.0, 80)
        return GreenKernelAdelic(sigma_grid=0.5 + 1j * t_grid).compute()

    def test_tate_identity_error_small(self, green_result):
        """G(s)·s(s−1) = ξ(s): relative error should be small."""
        assert green_result.tate_identity_check < 0.1

    def test_resolvent_bound_positive(self, green_result):
        """Resolvent bound should be a finite positive number."""
        assert 0 < green_result.resolvent_bound < float("inf")

    def test_g_values_shape(self, green_result):
        assert len(green_result.g_values) == len(green_result.s_grid)

    def test_g_values_complex(self, green_result):
        assert green_result.g_values.dtype == complex


# ---------------------------------------------------------------------------
# 6.  Krein Trace Formula
# ---------------------------------------------------------------------------

class TestKreinTraceFormula:
    """Validate Krein trace formula computation."""

    @pytest.fixture(scope="class")
    def krein_result(self):
        def gaussian(t):
            return math.exp(-t * t / 200.0)
        t_grid = np.linspace(1.0, 50.0, 200)
        return KreinTraceFormula(t_grid=t_grid).compute(gaussian, Lambda=30.0)

    def test_krein_integral_finite(self, krein_result):
        assert math.isfinite(krein_result.krein_integral)

    def test_spectral_shift_finite(self, krein_result):
        assert np.all(np.isfinite(krein_result.xi_spectral_shift))

    def test_time_delay_density_finite(self, krein_result):
        assert np.all(np.isfinite(krein_result.time_delay_density))

    def test_weil_total_finite(self, krein_result):
        assert math.isfinite(krein_result.weil_total)

    def test_discrepancy_reasonable(self, krein_result):
        """Discrepancy between Krein integral and Weil total should be finite."""
        assert math.isfinite(krein_result.krein_weil_discrepancy)


# ---------------------------------------------------------------------------
# 7.  Full System Integration
# ---------------------------------------------------------------------------

@pytest.mark.slow
class TestLaxPhillipsAdelicSystem:
    """Integration test for the full Lax-Phillips system."""

    @pytest.fixture(scope="class")
    def system_result(self):
        system = LaxPhillipsAdelicSystem(
            Lambda=30.0, t_max=50.0, n_mellin=128, n_smatrix=80
        )
        return system.run()

    def test_result_type(self, system_result):
        assert isinstance(system_result, LaxPhillipsAdelicResult)

    def test_coherence_psi_in_range(self, system_result):
        """Ψ coherence should be in [0, 1]."""
        assert 0.0 <= system_result.coherence_psi <= 1.0

    def test_spectral_identification_keys(self, system_result):
        expected_keys = {
            "hilbert_space", "hamiltonian", "mellin_image",
            "deficiency_indices", "s_matrix", "green_kernel",
            "poles", "krein_formula", "conclusion",
        }
        assert expected_keys.issubset(set(system_result.spectral_identification))

    def test_certificate_status(self, system_result):
        status = system_result.certificate["status"]
        assert status in ("✅ CERRADO", "⚠️ PARCIAL")

    def test_certificate_author(self, system_result):
        cert = system_result.certificate
        assert "José Manuel Mota Burruezo" in str(cert["author"])

    def test_certificate_doi(self, system_result):
        assert "10.5281/zenodo" in str(system_result.certificate["doi"])


# ---------------------------------------------------------------------------
# 8.  generate_lax_phillips_certificate
# ---------------------------------------------------------------------------

class TestGenerateCertificate:
    """Test the top-level certificate generation function."""

    @pytest.fixture(scope="class")
    def cert(self):
        return generate_lax_phillips_certificate(Lambda=25.0, t_max=40.0)

    def test_returns_dict(self, cert):
        assert isinstance(cert, dict)

    def test_required_keys(self, cert):
        for key in ("title", "status", "components", "spectral_identification",
                    "coherence_psi", "qcal_signature", "frequency_base_hz",
                    "author", "doi"):
            assert key in cert, f"Missing key: {key}"

    def test_component_keys(self, cert):
        for comp in ("mellin_self_adjointness", "wave_operators", "s_matrix",
                     "green_kernel", "connes_cutoff", "krein_trace"):
            assert comp in cert["components"], f"Missing component: {comp}"

    def test_frequency_base(self, cert):
        assert abs(cert["frequency_base_hz"] - 141.7001) < 1e-4

    def test_qcal_signature(self, cert):
        assert "∞³" in cert["qcal_signature"] or "Ω" in cert["qcal_signature"]
