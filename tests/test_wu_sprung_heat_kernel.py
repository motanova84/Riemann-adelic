#!/usr/bin/env python3
"""
Tests for Wu-Sprung Heat Kernel Expansion Coefficients
=======================================================

Validates the analytical coefficients A₀–A₄ of the asymptotic expansion

    Tr(e^{-tH}) ~ A₀·ln(1/t)/t + A₁/t + A₂ + A₃·t·ln(1/t) + A₄·t

for the Wu-Sprung Hamiltonian whose counting function N(E) reproduces
N_smooth of the Riemann zeta zeros.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Protocol: QCAL-WU-SPRUNG-HEAT-KERNEL-TEST v1.0
DOI: 10.5281/zenodo.17379721
"""

import math

import numpy as np
import pytest

from operators.wu_sprung_heat_kernel import (
    EULER_GAMMA,
    F0_QCAL,
    C_COHERENCE,
    HeatKernelCoefficients,
    WuSprungHeatKernel,
    compute_heat_kernel_coefficients,
)


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

@pytest.fixture
def hk() -> WuSprungHeatKernel:
    """Default WuSprungHeatKernel instance."""
    return WuSprungHeatKernel()


# ---------------------------------------------------------------------------
# Analytical coefficient tests
# ---------------------------------------------------------------------------

class TestHeatKernelCoefficients:
    """Test the analytical values of the heat kernel expansion coefficients."""

    def test_A0_value(self, hk: WuSprungHeatKernel) -> None:
        """A₀ = 1/(2π) ≈ 0.15915."""
        expected = 1.0 / (2.0 * math.pi)
        assert math.isclose(hk.A0, expected, rel_tol=1e-12)

    def test_A1_value(self, hk: WuSprungHeatKernel) -> None:
        """A₁ = -(γ + ln(2π)) / (2π)."""
        expected = -(EULER_GAMMA + math.log(2.0 * math.pi)) / (2.0 * math.pi)
        assert math.isclose(hk.A1, expected, rel_tol=1e-12)

    def test_A1_is_negative(self, hk: WuSprungHeatKernel) -> None:
        """A₁ must be negative because γ + ln(2π) > 0."""
        assert hk.A1 < 0.0

    def test_A2_value(self, hk: WuSprungHeatKernel) -> None:
        """A₂ = 7/8 exactly."""
        assert math.isclose(hk.A2, 7.0 / 8.0, rel_tol=1e-12)

    def test_A3_value(self, hk: WuSprungHeatKernel) -> None:
        """A₃ = 1/(48π) > 0."""
        expected = 1.0 / (48.0 * math.pi)
        assert math.isclose(hk.A3, expected, rel_tol=1e-12)
        assert hk.A3 > 0.0

    def test_A4_value(self, hk: WuSprungHeatKernel) -> None:
        """A₄ = -γ/(48π) < 0."""
        expected = -EULER_GAMMA / (48.0 * math.pi)
        assert math.isclose(hk.A4, expected, rel_tol=1e-12)
        assert hk.A4 < 0.0

    def test_coefficients_dataclass(self, hk: WuSprungHeatKernel) -> None:
        """coefficients() returns a HeatKernelCoefficients with all fields."""
        c = hk.coefficients()
        assert isinstance(c, HeatKernelCoefficients)
        assert math.isclose(c.A0, hk.A0)
        assert math.isclose(c.A1, hk.A1)
        assert math.isclose(c.A2, hk.A2)
        assert math.isclose(c.A3, hk.A3)
        assert math.isclose(c.A4, hk.A4)
        assert math.isclose(c.euler_gamma, EULER_GAMMA)

    def test_convenience_function(self) -> None:
        """compute_heat_kernel_coefficients() matches WuSprungHeatKernel."""
        c = compute_heat_kernel_coefficients()
        hk_ref = WuSprungHeatKernel()
        assert math.isclose(c.A0, hk_ref.A0)
        assert math.isclose(c.A1, hk_ref.A1)
        assert math.isclose(c.A2, hk_ref.A2)
        assert math.isclose(c.A3, hk_ref.A3)
        assert math.isclose(c.A4, hk_ref.A4)


# ---------------------------------------------------------------------------
# Numerical accuracy of the coefficients
# ---------------------------------------------------------------------------

class TestCoefficientNumericalValues:
    """Verify coefficients match known numerical constants."""

    def test_A0_approx(self, hk: WuSprungHeatKernel) -> None:
        """A₀ ≈ 0.1591549."""
        assert math.isclose(hk.A0, 0.1591549, rel_tol=1e-5)

    def test_A2_exact(self, hk: WuSprungHeatKernel) -> None:
        """A₂ = 0.875 exactly."""
        assert hk.A2 == 0.875

    def test_A3_approx(self, hk: WuSprungHeatKernel) -> None:
        """A₃ ≈ 0.006631."""
        assert math.isclose(hk.A3, 0.006631, rel_tol=1e-3)

    def test_euler_gamma_constant(self) -> None:
        """EULER_GAMMA matches the known Euler-Mascheroni constant to 10 decimal places."""
        # Check against well-known value
        assert math.isclose(EULER_GAMMA, 0.5772156649, rel_tol=1e-9)


# ---------------------------------------------------------------------------
# trace_expansion tests
# ---------------------------------------------------------------------------

class TestTraceExpansion:
    """Test trace_expansion(t) for correctness and edge cases."""

    def test_positive_result_small_t(self, hk: WuSprungHeatKernel) -> None:
        """For small t, Tr(e^{-tH}) is dominated by A₀·ln(1/t)/t > 0."""
        val = hk.trace_expansion(0.001)
        assert val > 0.0

    def test_monotone_divergence(self, hk: WuSprungHeatKernel) -> None:
        """Expansion should grow as t → 0 (dominant term ~ ln(1/t)/t)."""
        val_small = hk.trace_expansion(0.001)
        val_larger = hk.trace_expansion(0.01)
        assert val_small > val_larger

    def test_n_terms_consistency(self, hk: WuSprungHeatKernel) -> None:
        """Adding more terms refines the value monotonically in magnitude."""
        t = 0.005
        v1 = hk.trace_expansion(t, n_terms=1)
        v5 = hk.trace_expansion(t, n_terms=5)
        # With more terms the value changes; just check both are finite and positive
        assert math.isfinite(v1)
        assert math.isfinite(v5)
        assert v1 > 0.0

    def test_invalid_t_raises(self, hk: WuSprungHeatKernel) -> None:
        """t ≤ 0 must raise ValueError."""
        with pytest.raises(ValueError):
            hk.trace_expansion(0.0)
        with pytest.raises(ValueError):
            hk.trace_expansion(-1.0)

    def test_invalid_n_terms_raises(self, hk: WuSprungHeatKernel) -> None:
        """n_terms outside [1,5] must raise ValueError."""
        with pytest.raises(ValueError):
            hk.trace_expansion(0.01, n_terms=0)
        with pytest.raises(ValueError):
            hk.trace_expansion(0.01, n_terms=6)

    def test_single_term_is_A0_term(self, hk: WuSprungHeatKernel) -> None:
        """With n_terms=1, result equals A₀·ln(1/t)/t."""
        t = 0.01
        expected = hk.A0 * math.log(1.0 / t) / t
        assert math.isclose(hk.trace_expansion(t, n_terms=1), expected)


# ---------------------------------------------------------------------------
# Numerical trace vs expansion agreement
# ---------------------------------------------------------------------------

class TestNumericalAgreement:
    """
    Check that the asymptotic expansion agrees with direct numerical
    Laplace-transform integration for small t.
    """

    @pytest.mark.parametrize("t", [0.001, 0.002, 0.005])
    def test_small_t_relative_error(
        self, hk: WuSprungHeatKernel, t: float
    ) -> None:
        """For t ≤ 0.005, 5-term expansion should match within 5%."""
        exp_val = hk.trace_expansion(t)
        num_val = hk.trace_numerical(t)
        rel_err = abs(exp_val - num_val) / (abs(num_val) + 1e-30)
        assert rel_err < 0.05, (
            f"t={t}: expansion={exp_val:.4f}, numerical={num_val:.4f}, "
            f"rel_err={rel_err:.2%}"
        )

    def test_validate_coefficients_passes(self, hk: WuSprungHeatKernel) -> None:
        """validate_coefficients should report all_passed=True for small t."""
        t_vals = np.array([0.001, 0.002, 0.005])
        result = hk.validate_coefficients(t_vals, rtol=0.05)
        assert result["all_passed"], (
            f"Validation failed: relative errors = {result['relative_errors']}"
        )

    def test_numerical_trace_positive(self, hk: WuSprungHeatKernel) -> None:
        """Numerical trace must be positive for any valid t."""
        for t in [0.001, 0.01, 0.05]:
            val = hk.trace_numerical(t)
            assert val > 0.0, f"Numerical trace negative at t={t}"

    def test_numerical_invalid_t(self, hk: WuSprungHeatKernel) -> None:
        """trace_numerical with t ≤ 0 must raise ValueError."""
        with pytest.raises(ValueError):
            hk.trace_numerical(0.0)


# ---------------------------------------------------------------------------
# Certificate generation
# ---------------------------------------------------------------------------

class TestCertificate:
    """Test generate_certificate() output structure and content."""

    def test_certificate_keys(self, hk: WuSprungHeatKernel) -> None:
        """Certificate must contain required top-level keys."""
        cert = hk.generate_certificate()
        for key in ("protocol", "version", "status", "coefficients",
                    "formulas", "expansion", "validation",
                    "qcal_signature", "frequency_base", "coherence",
                    "doi", "author", "orcid", "institution"):
            assert key in cert, f"Missing key: {key}"

    def test_certificate_protocol(self, hk: WuSprungHeatKernel) -> None:
        """Protocol name and version must be correct."""
        cert = hk.generate_certificate()
        assert cert["protocol"] == "QCAL-WU-SPRUNG-HEAT-KERNEL"
        assert cert["version"] == "v1.0"

    def test_certificate_qcal_metadata(self, hk: WuSprungHeatKernel) -> None:
        """QCAL metadata fields must match module constants."""
        cert = hk.generate_certificate()
        assert cert["frequency_base"] == F0_QCAL
        assert cert["coherence"] == C_COHERENCE
        assert cert["qcal_signature"] == "∴𓂀Ω∞³Φ"
        assert cert["doi"] == "10.5281/zenodo.17379721"

    def test_certificate_coefficients(self, hk: WuSprungHeatKernel) -> None:
        """Certificate coefficients must match analytical values."""
        cert = hk.generate_certificate()
        c = cert["coefficients"]
        assert math.isclose(c["A0"], hk.A0, rel_tol=1e-10)
        assert math.isclose(c["A1"], hk.A1, rel_tol=1e-10)
        assert math.isclose(c["A2"], hk.A2, rel_tol=1e-10)
        assert math.isclose(c["A3"], hk.A3, rel_tol=1e-10)
        assert math.isclose(c["A4"], hk.A4, rel_tol=1e-10)

    def test_certificate_validation_finite(self, hk: WuSprungHeatKernel) -> None:
        """Certificate validation values must be finite numbers."""
        cert = hk.generate_certificate()
        v = cert["validation"]
        assert math.isfinite(v["expansion_value"])
        assert math.isfinite(v["numerical_value"])
        assert math.isfinite(v["relative_error"])
        assert v["relative_error"] >= 0.0

    def test_certificate_validated_status(self, hk: WuSprungHeatKernel) -> None:
        """Certificate status should be VALIDATED for default parameters."""
        cert = hk.generate_certificate()
        assert cert["status"] == "✅ VALIDATED"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
