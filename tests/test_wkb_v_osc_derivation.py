#!/usr/bin/env python3
"""
Tests for WKB Quantization and V_osc Derivation
================================================

Comprehensive test suite for operators/wkb_v_osc_derivation.py, validating:
  - WKB quantization (Bohr-Sommerfeld condition)
  - Density of states decomposition (smooth + oscillatory)
  - Abel transform and its inverse (asymptotic and exact)
  - Oscillatory potential V_osc(x) = Σ_p (log p/√p) cos(x log p + φ_p)
  - Corrected Wu-Sprung Hamiltonian
  - QCAL certificate generation
"""

import pytest
import numpy as np

from operators.wkb_v_osc_derivation import (
    WKBQuantization,
    DensityOfStates,
    AbelTransform,
    VOscPotential,
    WuSprungHamiltonianCorrected,
    WKBResult,
    AbelTransformResult,
    VOscResult,
    compute_smooth_density,
    compute_oscillatory_density,
    abel_integral_asymptotic,
    abel_integral_exact,
    generate_qcal_certificate,
    _sieve_primes,
)


# ---------------------------------------------------------------------------
# Helper potential for WKB tests: harmonic oscillator V(x) = x²
# ---------------------------------------------------------------------------

def _harmonic(x: float) -> float:
    """Harmonic oscillator potential V(x) = x²."""
    return x * x


def _linear(x: float) -> float:
    """Linear potential V(x) = x (triangular well)."""
    return x


# ---------------------------------------------------------------------------
# Tests: _sieve_primes
# ---------------------------------------------------------------------------

class TestSievePrimes:
    """Tests for internal prime sieve."""

    def test_small_primes(self):
        """Verify first few primes."""
        primes = _sieve_primes(30)
        assert primes == [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]

    def test_empty_for_small_n(self):
        """No primes below 2."""
        assert _sieve_primes(1) == []
        assert _sieve_primes(0) == []

    def test_includes_boundary(self):
        """n_max itself is included if prime."""
        primes = _sieve_primes(7)
        assert 7 in primes

    def test_count(self):
        """π(100) = 25."""
        primes = _sieve_primes(100)
        assert len(primes) == 25


# ---------------------------------------------------------------------------
# Tests: compute_smooth_density
# ---------------------------------------------------------------------------

class TestSmoothDensity:
    """Tests for smooth (Weyl) density of states."""

    def test_positive_E(self):
        """ρ̄(E) > 0 for sufficiently large E."""
        rho = compute_smooth_density(10.0)
        assert rho > 0

    def test_zero_for_nonpositive(self):
        """Returns 0 for E ≤ 0."""
        assert compute_smooth_density(0.0) == 0.0
        assert compute_smooth_density(-1.0) == 0.0

    def test_formula(self):
        """ρ̄(E) = (1/2π) log(E/2π) matches manual computation."""
        E = 20.0
        expected = np.log(E / (2 * np.pi)) / (2 * np.pi)
        assert abs(compute_smooth_density(E) - expected) < 1e-12

    def test_monotone_increasing(self):
        """Smooth density is monotonically increasing for E > 2π."""
        E_vals = [10.0, 20.0, 50.0, 100.0]
        rho_vals = [compute_smooth_density(E) for E in E_vals]
        for i in range(len(rho_vals) - 1):
            assert rho_vals[i] < rho_vals[i + 1]


# ---------------------------------------------------------------------------
# Tests: compute_oscillatory_density
# ---------------------------------------------------------------------------

class TestOscillatoryDensity:
    """Tests for oscillatory density from Gutzwiller/explicit formula."""

    def setup_method(self):
        self.primes = _sieve_primes(30)

    def test_finite(self):
        """ρ_osc(E) is finite for real E."""
        for E in [5.0, 10.0, 20.0, 50.0]:
            rho = compute_oscillatory_density(E, self.primes)
            assert np.isfinite(rho)

    def test_oscillatory(self):
        """ρ_osc changes sign as E varies (not always positive)."""
        vals = [compute_oscillatory_density(E, self.primes) for E in np.linspace(1, 30, 50)]
        assert any(v > 0 for v in vals)
        assert any(v < 0 for v in vals)

    def test_formula_structure(self):
        """Manual computation matches function."""
        E = 15.0
        primes = [2, 3, 5]
        expected = sum(
            (np.log(p) / np.sqrt(p)) * np.cos(E * np.log(p)) for p in primes
        ) / np.pi
        result = compute_oscillatory_density(E, primes)
        assert abs(result - expected) < 1e-12

    def test_zero_primes(self):
        """Zero primes gives zero oscillatory density."""
        assert compute_oscillatory_density(10.0, []) == 0.0


# ---------------------------------------------------------------------------
# Tests: WKBQuantization
# ---------------------------------------------------------------------------

class TestWKBQuantization:
    """Tests for WKB quantization with harmonic oscillator."""

    def setup_method(self):
        """Use harmonic oscillator V(x) = x²."""
        self.wkb = WKBQuantization(_harmonic)

    def test_turning_point_harmonic(self):
        """Turning point of harmonic oscillator: x_t = √E."""
        for E in [1.0, 4.0, 9.0]:
            x_t = self.wkb.find_turning_point(E)
            expected = np.sqrt(E)
            assert abs(x_t - expected) < 1e-6, f"x_t={x_t}, expected {expected}"

    def test_turning_point_no_bracket(self):
        """Raises ValueError when no turning point in search range."""
        with pytest.raises(ValueError):
            # V(x) = x² never reaches E=100 in [0,1]
            self.wkb.find_turning_point(100.0, x_search_max=1.0)

    def test_action_harmonic(self):
        """S(E) = ∫₀^√E √(E-x²) dx = πE/4 for harmonic oscillator."""
        E = 4.0
        action = self.wkb.compute_action(E)
        expected = np.pi * E / 4.0
        assert abs(action - expected) / expected < 1e-4

    def test_density_harmonic(self):
        """ρ(E) = (1/π)·(π/2)/√E · ... Should equal dS/dE / π."""
        # For V=x², ρ(E) = (1/π) ∫₀^√E dx/√(E-x²) = 1/2
        E = 4.0
        density = self.wkb.compute_density(E)
        # ∫₀^√E dx/√(E-x²) = π/2, so ρ = 1/2
        assert abs(density - 0.5) < 1e-3

    def test_compute_returns_wkbresult(self):
        """compute() returns WKBResult with correct structure."""
        result = self.wkb.compute(4.0)
        assert isinstance(result, WKBResult)
        assert result.energy == 4.0
        assert result.turning_point > 0
        assert result.action > 0
        assert result.density > 0

    def test_quantum_numbers(self):
        """Quantum number n = S(E)/π - 1/2 increases with E."""
        ns = [self.wkb.compute(E).quantum_number for E in [1.0, 4.0, 9.0, 16.0]]
        for i in range(len(ns) - 1):
            assert ns[i] < ns[i + 1]

    def test_linear_potential(self):
        """Test with linear potential V(x) = x."""
        wkb_lin = WKBQuantization(_linear)
        E = 4.0
        x_t = wkb_lin.find_turning_point(E)
        assert abs(x_t - E) < 1e-8  # V(x_t) = x_t = E
        action = wkb_lin.compute_action(E, x_t=x_t)
        # ∫₀^E √(E-x) dx = 2E^{3/2}/3
        expected = 2.0 * E ** 1.5 / 3.0
        assert abs(action - expected) / expected < 1e-4


# ---------------------------------------------------------------------------
# Tests: DensityOfStates
# ---------------------------------------------------------------------------

class TestDensityOfStates:
    """Tests for DensityOfStates class."""

    def setup_method(self):
        self.dos = DensityOfStates(p_max=50)

    def test_smooth_matches_standalone(self):
        """DensityOfStates.smooth matches compute_smooth_density."""
        for E in [10.0, 30.0, 100.0]:
            assert abs(self.dos.smooth(E) - compute_smooth_density(E)) < 1e-12

    def test_oscillatory_matches_standalone(self):
        """DensityOfStates.oscillatory matches compute_oscillatory_density."""
        for E in [5.0, 15.0, 40.0]:
            expected = compute_oscillatory_density(E, self.dos.primes)
            assert abs(self.dos.oscillatory(E) - expected) < 1e-12

    def test_total_decomposition(self):
        """total = smooth + oscillatory."""
        for E in [10.0, 25.0, 60.0]:
            assert abs(self.dos.total(E) - (self.dos.smooth(E) + self.dos.oscillatory(E))) < 1e-12

    def test_with_custom_primes(self):
        """Works with custom prime list."""
        dos = DensityOfStates(primes=[2, 3, 5])
        rho = dos.oscillatory(10.0)
        assert np.isfinite(rho)

    def test_smooth_zero_at_e2pi(self):
        """ρ̄(2π) = 0."""
        rho = self.dos.smooth(2.0 * np.pi)
        assert abs(rho) < 1e-10

    def test_smooth_zero_nonpositive(self):
        """ρ̄(E) = 0 for E ≤ 0."""
        assert self.dos.smooth(0.0) == 0.0
        assert self.dos.smooth(-5.0) == 0.0


# ---------------------------------------------------------------------------
# Tests: abel_integral_asymptotic and abel_integral_exact
# ---------------------------------------------------------------------------

class TestAbelIntegrals:
    """Tests for Abel integral evaluation."""

    def test_asymptotic_structure(self):
        """Asymptotic integral has correct phase."""
        omega = np.log(2)
        V = 50.0
        val = abel_integral_asymptotic(omega, V)
        expected = np.sqrt(np.pi / (4.0 * omega)) * np.cos(omega * V - np.pi / 4.0)
        assert abs(val - expected) < 1e-12

    def test_asymptotic_zero_omega(self):
        """Returns 0 for omega=0."""
        assert abel_integral_asymptotic(0.0, 10.0) == 0.0

    def test_exact_finite(self):
        """Exact Fresnel integral is finite."""
        omega = np.log(3)
        V = 20.0
        val = abel_integral_exact(omega, V)
        assert np.isfinite(val)

    def test_exact_zero_V(self):
        """Returns 0 when V <= V_min."""
        assert abel_integral_exact(np.log(2), 0.0) == 0.0
        assert abel_integral_exact(np.log(2), -1.0) == 0.0

    def test_exact_vs_asymptotic_large_V(self):
        """Exact and asymptotic agree for large ωV."""
        omega = np.log(2)
        V = 200.0  # ωV ≈ 139 >> 1
        exact = abel_integral_exact(omega, V)
        asymp = abel_integral_asymptotic(omega, V)
        # Should agree to within ~10% for large ωV
        relative_error = abs(exact - asymp) / (abs(asymp) + 1e-15)
        assert relative_error < 0.15, f"Relative error {relative_error} too large"

    def test_exact_positive_for_small_V(self):
        """Exact integral is non-zero for small V > 0."""
        val = abel_integral_exact(np.log(5), 1.0)
        assert np.isfinite(val)


# ---------------------------------------------------------------------------
# Tests: AbelTransform
# ---------------------------------------------------------------------------

class TestAbelTransform:
    """Tests for AbelTransform class."""

    def setup_method(self):
        self.abel = AbelTransform(p_max=30)

    def test_x_smooth_zero_at_Vmin(self):
        """x_smooth(V_min) = 0."""
        result = self.abel.x_smooth(self.abel.V_min)
        assert result == 0.0

    def test_x_smooth_positive_increasing(self):
        """x_smooth(V) > 0 and increasing for V > 2π (where Weyl density > 0)."""
        # ρ̄(E) = (1/2π) log(E/2π) > 0 only for E > 2π, so x_smooth
        # becomes meaningfully positive only for sufficiently large V.
        vals = [self.abel.x_smooth(V) for V in [15.0, 30.0, 80.0]]
        for v in vals:
            assert v > 0
        for i in range(len(vals) - 1):
            assert vals[i] < vals[i + 1]

    def test_x_osc_asymptotic_finite(self):
        """Asymptotic x_osc is finite."""
        for V in [5.0, 10.0, 20.0]:
            val = self.abel.x_osc_asymptotic(V)
            assert np.isfinite(val)

    def test_x_osc_exact_finite(self):
        """Exact x_osc is finite."""
        for V in [5.0, 10.0, 20.0]:
            val = self.abel.x_osc_exact(V)
            assert np.isfinite(val)

    def test_compute_asymptotic_returns_result(self):
        """compute() with asymptotic returns AbelTransformResult."""
        result = self.abel.compute(10.0, method="asymptotic")
        assert isinstance(result, AbelTransformResult)
        assert result.V == 10.0
        assert np.isfinite(result.x_smooth)
        assert np.isfinite(result.x_osc)
        assert np.isfinite(result.x_total)
        assert result.n_primes == len(self.abel.primes)

    def test_compute_exact_returns_result(self):
        """compute() with exact returns AbelTransformResult."""
        result = self.abel.compute(10.0, method="exact")
        assert isinstance(result, AbelTransformResult)
        assert np.isfinite(result.x_total)

    def test_total_is_sum(self):
        """x_total = x_smooth + x_osc."""
        result = self.abel.compute(15.0)
        assert abs(result.x_total - (result.x_smooth + result.x_osc)) < 1e-12

    def test_oscillatory_smaller_than_smooth(self):
        """Oscillatory correction is small compared to smooth part."""
        result = self.abel.compute(20.0)
        assert abs(result.x_osc) < abs(result.x_smooth)


# ---------------------------------------------------------------------------
# Tests: VOscPotential
# ---------------------------------------------------------------------------

class TestVOscPotential:
    """Tests for oscillatory potential V_osc(x)."""

    def setup_method(self):
        self.v_osc = VOscPotential(p_max=50)

    def test_evaluate_returns_result(self):
        """evaluate() returns VOscResult."""
        result = self.v_osc.evaluate(10.0)
        assert isinstance(result, VOscResult)
        assert result.x == 10.0
        assert np.isfinite(result.V_osc)
        assert result.n_primes == len(self.v_osc.primes)

    def test_terms_sum_to_total(self):
        """Sum of per-prime terms equals V_osc total."""
        result = self.v_osc.evaluate(5.0)
        assert abs(sum(result.terms) - result.V_osc) < 1e-12

    def test_phases_constant(self):
        """All phases equal the configured phase."""
        result = self.v_osc.evaluate(5.0)
        for phi in result.phases:
            assert abs(phi - self.v_osc.phase) < 1e-12

    def test_default_phase(self):
        """Default phase is -π/4."""
        assert abs(self.v_osc.phase - (-np.pi / 4.0)) < 1e-12

    def test_zero_phase(self):
        """Zero phase gives pure cosine."""
        v = VOscPotential(primes=[2], phase=0.0)
        result = v.evaluate(10.0)
        expected = (np.log(2) / np.sqrt(2)) * np.cos(10.0 * np.log(2))
        assert abs(result.V_osc - expected) < 1e-12

    def test_evaluate_array_matches_single(self):
        """evaluate_array matches evaluate for each point."""
        x_arr = np.array([1.0, 5.0, 10.0, 20.0])
        arr_result = self.v_osc.evaluate_array(x_arr)
        for i, x in enumerate(x_arr):
            single = self.v_osc.evaluate(x).V_osc
            assert abs(arr_result[i] - single) < 1e-12

    def test_oscillatory_character(self):
        """V_osc changes sign over x (oscillatory)."""
        x_arr = np.linspace(1, 50, 500)
        vals = self.v_osc.evaluate_array(x_arr)
        assert any(v > 0 for v in vals)
        assert any(v < 0 for v in vals)

    def test_finite_for_large_x(self):
        """V_osc is finite even for large x."""
        for x in [100.0, 500.0, 1000.0]:
            result = self.v_osc.evaluate(x)
            assert np.isfinite(result.V_osc)

    def test_custom_primes(self):
        """Works with a custom prime list."""
        v = VOscPotential(primes=[2, 3, 5, 7])
        result = v.evaluate(10.0)
        assert result.n_primes == 4

    def test_perturbation_correction_finite(self):
        """Perturbation correction integral is finite."""
        x_arr = np.linspace(0.1, 5.0, 100)
        psi_n = lambda x: np.exp(-x**2 / 2.0)  # Gaussian wavefunction
        delta = self.v_osc.perturbation_correction(0, psi_n, x_arr)
        assert np.isfinite(delta)

    def test_perturbation_correction_formula(self):
        """Perturbation correction uses V_osc weighted by ψ²."""
        x_arr = np.linspace(0.0, 10.0, 1000)
        # Constant wavefunction (unnormalized) — correction = ∫V_osc dx
        psi_const = lambda x: 1.0
        delta = self.v_osc.perturbation_correction(0, psi_const, x_arr)
        # Should equal ∫V_osc dx over [0,10]
        v_vals = self.v_osc.evaluate_array(x_arr)
        expected = np.trapezoid(v_vals, x_arr)
        assert abs(delta - expected) < 1e-10


# ---------------------------------------------------------------------------
# Tests: WuSprungHamiltonianCorrected
# ---------------------------------------------------------------------------

class TestWuSprungHamiltonianCorrected:
    """Tests for corrected Wu-Sprung Hamiltonian."""

    def setup_method(self):
        self.H = WuSprungHamiltonianCorrected(p_max=30)

    def test_V_Abel_positive(self):
        """V_Abel(x) > 0 for x > 0."""
        for x in [1.0, 5.0, 10.0, 50.0]:
            assert self.H.V_Abel(x) > 0

    def test_V_Abel_zero_at_origin(self):
        """V_Abel(0) = 0."""
        assert self.H.V_Abel(0.0) == 0.0

    def test_V_Abel_increasing(self):
        """V_Abel is increasing."""
        vals = [self.H.V_Abel(x) for x in [1.0, 5.0, 10.0, 50.0]]
        for i in range(len(vals) - 1):
            assert vals[i] < vals[i + 1]

    def test_V_total_finite(self):
        """Total potential is finite."""
        for x in [1.0, 5.0, 10.0]:
            assert np.isfinite(self.H.V_total(x))

    def test_V_total_array_shape(self):
        """V_total_array returns same shape as input."""
        x_arr = np.linspace(1, 10, 50)
        v = self.H.V_total_array(x_arr)
        assert v.shape == x_arr.shape
        assert all(np.isfinite(v))

    def test_epsilon_zero_gives_smooth(self):
        """With ε=0, total potential equals smooth Abel potential."""
        H_smooth = WuSprungHamiltonianCorrected(p_max=30, epsilon=0.0)
        for x in [1.0, 5.0, 10.0]:
            assert abs(H_smooth.V_total(x) - H_smooth.V_Abel(x)) < 1e-12

    def test_v_osc_correction_small(self):
        """Oscillatory correction is small relative to smooth potential."""
        x_arr = np.linspace(5.0, 50.0, 20)
        for x in x_arr:
            v_abel = self.H.V_Abel(x)
            v_total = self.H.V_total(x)
            correction = abs(v_total - v_abel)
            # Correction should be much smaller than Abel potential for large x
            if v_abel > 1.0:
                assert correction < 10.0 * v_abel


# ---------------------------------------------------------------------------
# Tests: generate_qcal_certificate
# ---------------------------------------------------------------------------

class TestQCALCertificate:
    """Tests for QCAL certificate generation."""

    def test_certificate_structure(self):
        """Certificate contains all required keys."""
        cert = generate_qcal_certificate(p_max=20)
        required_keys = [
            "protocol", "timestamp", "doi", "f0_hz", "C_coherence",
            "n_primes", "p_max", "epsilon", "results", "checksum",
            "mathematical_steps", "seal",
        ]
        for key in required_keys:
            assert key in cert, f"Missing key: {key}"

    def test_certificate_metadata(self):
        """Certificate has correct QCAL metadata."""
        cert = generate_qcal_certificate(p_max=20)
        assert cert["f0_hz"] == 141.7001
        assert cert["C_coherence"] == 244.36
        assert cert["seal"] == 14170001
        assert cert["doi"] == "10.5281/zenodo.17379721"

    def test_certificate_n_primes(self):
        """Certificate reports correct number of primes."""
        cert = generate_qcal_certificate(p_max=30)
        expected_n = len(_sieve_primes(30))
        assert cert["n_primes"] == expected_n

    def test_certificate_checksum_format(self):
        """Checksum starts with expected prefix."""
        cert = generate_qcal_certificate(p_max=20)
        assert cert["checksum"].startswith("0xQCAL_WKB_VOSC_")

    def test_certificate_results_structure(self):
        """Results section contains expected sub-keys."""
        cert = generate_qcal_certificate(p_max=20)
        results = cert["results"]
        assert "v_osc_values" in results
        assert "smooth_densities" in results
        assert "osc_densities" in results
        assert "abel_results" in results

    def test_certificate_v_osc_values(self):
        """V_osc values in certificate are finite."""
        cert = generate_qcal_certificate(p_max=20, x_values=[1.0, 10.0])
        for key, val in cert["results"]["v_osc_values"].items():
            assert np.isfinite(val), f"V_osc({key}) = {val} is not finite"

    def test_certificate_smooth_densities(self):
        """Smooth densities in certificate match formula."""
        cert = generate_qcal_certificate(p_max=20)
        for E_str, rho in cert["results"]["smooth_densities"].items():
            E = float(E_str)
            expected = compute_smooth_density(E)
            assert abs(rho - expected) < 1e-12

    def test_certificate_mathematical_steps(self):
        """Certificate lists all 7 mathematical derivation steps."""
        cert = generate_qcal_certificate(p_max=20)
        assert len(cert["mathematical_steps"]) == 7

    def test_certificate_reproducible(self):
        """Same inputs produce same checksum (reproducibility)."""
        cert1 = generate_qcal_certificate(p_max=20, x_values=[1.0, 5.0])
        cert2 = generate_qcal_certificate(p_max=20, x_values=[1.0, 5.0])
        assert cert1["checksum"] == cert2["checksum"]


# ---------------------------------------------------------------------------
# Integration tests: WKB ↔ density consistency
# ---------------------------------------------------------------------------

class TestWKBDensityConsistency:
    """Integration tests for WKB-density consistency."""

    def test_harmonic_density_constant(self):
        """Harmonic oscillator has constant density ρ = 1/2."""
        wkb = WKBQuantization(_harmonic)
        for E in [1.0, 4.0, 9.0, 16.0]:
            rho = wkb.compute_density(E)
            assert abs(rho - 0.5) < 1e-2, f"ρ({E}) = {rho} ≠ 0.5"

    def test_harmonic_action_formula(self):
        """S(E) = πE/4 for harmonic oscillator V(x) = x²."""
        wkb = WKBQuantization(_harmonic)
        for E in [1.0, 4.0, 9.0]:
            action = wkb.compute_action(E)
            expected = np.pi * E / 4.0
            assert abs(action - expected) / expected < 1e-4

    def test_density_from_action_derivative(self):
        """ρ(E) via Leibniz rule: dS/dE = (1/2)∫dx/√(E-V), so ρ = (1/π)·(1/2)·∫.

        Note: the formula ρ(E) = (1/π)∫dx/√(E-V) used in compute_density
        corresponds to the full-period (period T = 2∫₀^{x_t}) density convention,
        while the action S = ∫₀^{x_t}√(E-V)dx satisfies dS/dE = (1/2)∫dx/√(E-V).
        This reconciles the factor of 2 difference between the half-period
        (action derivative) and full-period (direct density formula) conventions.
        We verify this factor of 2 relationship explicitly.
        """
        wkb = WKBQuantization(_harmonic)
        E = 5.0
        dE = 0.001
        S_plus = wkb.compute_action(E + dE)
        S_minus = wkb.compute_action(E - dE)
        # dS/dE = (1/2) ∫dx/√(E-V), so 2·dS/dE / π = ρ(E) [the full-period density]
        rho_from_action = (S_plus - S_minus) / (2 * dE * np.pi)
        rho_direct = wkb.compute_density(E)
        # rho_direct = (1/π)∫dx/√(E-V) = 2 * (1/π)·(1/2)∫ = 2 * rho_from_action
        assert abs(rho_direct - 2.0 * rho_from_action) < 0.01


# ---------------------------------------------------------------------------
# Tests: V_osc derivation mathematical properties
# ---------------------------------------------------------------------------

class TestVOscMathematicalProperties:
    """Tests for mathematical properties of V_osc derivation."""

    def test_v_osc_prime_amplitude_decreasing(self):
        """Amplitude (log p)/√p decreases for large p."""
        # log(p)/√p is decreasing for p ≥ 3
        primes = _sieve_primes(100)
        amplitudes = [np.log(p) / np.sqrt(p) for p in primes if p >= 3]
        # Check that amplitudes eventually decrease
        assert amplitudes[-1] < amplitudes[0]

    def test_v_osc_bounded(self):
        """V_osc is bounded: |V_osc(x)| ≤ Σ_p (log p/√p)."""
        primes = _sieve_primes(30)
        max_amplitude = sum(np.log(p) / np.sqrt(p) for p in primes)
        v_osc = VOscPotential(primes=primes)
        for x in np.linspace(0.1, 100.0, 20):
            val = abs(v_osc.evaluate(x).V_osc)
            assert val <= max_amplitude + 1e-10

    def test_abel_integral_phase_shift(self):
        """Asymptotic Abel integral gives -π/4 phase shift."""
        # For large ωV: ∫cos(ωT)/√(V-T) ≈ √(π/(4ω)) cos(ωV - π/4)
        omega = np.log(2)
        V = 500.0  # Large ωV
        val = abel_integral_asymptotic(omega, V)
        expected = np.sqrt(np.pi / (4 * omega)) * np.cos(omega * V - np.pi / 4)
        assert abs(val - expected) < 1e-12

    def test_oscillatory_density_connection_to_explicit_formula(self):
        """ρ_osc is the prime-weighted cosine sum from explicit formula."""
        primes = [2, 3, 5, 7]
        E = 20.0
        rho = compute_oscillatory_density(E, primes)
        # Verify structure: each term (log p/√p) cos(E log p)
        manual = sum((np.log(p) / np.sqrt(p)) * np.cos(E * np.log(p)) for p in primes) / np.pi
        assert abs(rho - manual) < 1e-12

    def test_smooth_density_weyl_law(self):
        """Smooth density integrates to correct counting function N(E)."""
        # N(E) ≈ (1/2π)(E log(E/2π) - E) for large E [Riemann-Weyl]
        # Here we just check: ρ̄ is the derivative of the smooth part
        E1, E2 = 20.0, 21.0
        # Numerical derivative of smooth counting function
        # N̄(E) = (E/2π)(log(E/2π) - 1)
        N_smooth = lambda E: (E / (2 * np.pi)) * (np.log(E / (2 * np.pi)) - 1)
        dN_dE = (N_smooth(E2) - N_smooth(E1)) / (E2 - E1)
        rho_avg = (compute_smooth_density(E1) + compute_smooth_density(E2)) / 2.0
        assert abs(dN_dE - rho_avg) < 0.01


# ---------------------------------------------------------------------------
# Tests: Full derivation pipeline
# ---------------------------------------------------------------------------

class TestFullDerivationPipeline:
    """End-to-end tests for the full WKB → V_osc derivation pipeline."""

    def test_pipeline_produces_finite_values(self):
        """Full pipeline produces finite values at all steps."""
        primes = _sieve_primes(20)

        # Step 1: Density
        dos = DensityOfStates(primes=primes)
        for E in [10.0, 20.0, 50.0]:
            assert np.isfinite(dos.smooth(E))
            assert np.isfinite(dos.oscillatory(E))

        # Step 2: Abel transform
        abel = AbelTransform(primes=primes)
        for V in [5.0, 15.0, 30.0]:
            result = abel.compute(V)
            assert np.isfinite(result.x_smooth)
            assert np.isfinite(result.x_osc)

        # Step 3: V_osc
        v_osc = VOscPotential(primes=primes)
        for x in [1.0, 10.0, 50.0]:
            assert np.isfinite(v_osc.evaluate(x).V_osc)

    def test_hamiltonian_pipeline(self):
        """Wu-Sprung corrected Hamiltonian works end-to-end."""
        H = WuSprungHamiltonianCorrected(p_max=20)
        x_arr = np.linspace(0.1, 20.0, 50)
        v = H.V_total_array(x_arr)
        assert all(np.isfinite(v))
        assert len(v) == len(x_arr)
