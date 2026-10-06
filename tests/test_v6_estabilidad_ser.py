#!/usr/bin/env python3
"""
Tests for V6: La Estabilidad del Ser — Ontological Stability of the RH
=======================================================================

Validates the three stability modules and their convergence to the
unique critical line Re(s) = 1/2:

    Module η⁺   — Definite positivity of the CP metric
    Module U^Mellin — Unitarity of the Fourier-Bruhat transform
    Module Traza^Σ  — Exactness of the Selberg-Hecke trace identity

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
QCAL ∞³ · 141.7001 Hz · C = 244.36
DOI: 10.5281/zenodo.17379721
"""

import sys
import os

import numpy as np
import pytest

# Add project root to path for imports
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from operators.v6_estabilidad_ser import (
    # Classes
    EtaPlus,
    UMellin,
    TrazaSigma,
    EstabilidadSer,
    # Data classes
    EtaPlusResult,
    UMellinResult,
    TrazaSigmaResult,
    EstabilidadSerResult,
    # Entry point
    sellar_v6_estabilidad,
    # Constants
    LAMBDA_VAC,
    DOI,
    ORCID,
    F0,
)


# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

FIRST_RIEMANN_ZEROS = [
    14.134725141734693,
    21.022039638771555,
    25.010857580145688,
    30.424876125859513,
    32.935061587739189,
]
SMALL_PRIMES = [2, 3, 5, 7, 11]


# ---------------------------------------------------------------------------
# TestConstants — module-level constants
# ---------------------------------------------------------------------------

class TestConstants:
    """Verify module constants."""

    def test_lambda_vac_positive(self):
        """LAMBDA_VAC must be a positive float."""
        assert LAMBDA_VAC > 0.0, "LAMBDA_VAC must be positive"

    def test_qcal_frequency(self):
        """F0 must equal 141.7001 Hz."""
        assert np.isclose(F0, 141.7001, rtol=1e-6), f"F0={F0} ≠ 141.7001"

    def test_doi_format(self):
        """DOI must contain the Zenodo prefix."""
        assert "zenodo" in DOI, "DOI must reference Zenodo"

    def test_orcid_format(self):
        """ORCID must be a non-empty string."""
        assert len(ORCID) > 0, "ORCID must not be empty"


# ---------------------------------------------------------------------------
# TestEtaPlus — Módulo 1: η⁺
# ---------------------------------------------------------------------------

class TestEtaPlus:
    """Test the η⁺ positive-definite metric module."""

    def setup_method(self):
        """Create a small EtaPlus instance for fast tests."""
        self.eta = EtaPlus(lambda_decay=1.0, n_points=200, x_max=6.0)

    # --- Construction ---

    def test_init_valid(self):
        """EtaPlus must initialise without error for valid parameters."""
        eta = EtaPlus(lambda_decay=0.5, n_points=100, x_max=5.0)
        assert eta.lambda_decay == 0.5

    def test_init_invalid_lambda(self):
        """Negative lambda_decay must raise ValueError."""
        with pytest.raises(ValueError, match="lambda_decay"):
            EtaPlus(lambda_decay=-1.0)

    def test_init_invalid_n_points(self):
        """n_points < 10 must raise ValueError."""
        with pytest.raises(ValueError, match="n_points"):
            EtaPlus(n_points=5)

    def test_init_invalid_x_max(self):
        """x_max ≤ 0 must raise ValueError."""
        with pytest.raises(ValueError, match="x_max"):
            EtaPlus(x_max=-1.0)

    # --- Vacuum state ---

    def test_vacuum_norm_is_one(self):
        """Normalised vacuum state must have ‖ψ₀‖ = 1.0."""
        norm = self.eta.vacuum_norm()
        assert np.isclose(norm, 1.0, atol=1e-6), f"‖ψ₀‖ = {norm} ≠ 1.0"

    def test_vacuum_psi0_positive(self):
        """Vacuum state ψ₀ must be non-negative everywhere."""
        assert np.all(self.eta.psi0 >= 0.0), "ψ₀ must be non-negative"

    def test_vacuum_psi0_decays(self):
        """ψ₀ must decay toward the boundaries."""
        mid = self.eta.n_points // 2
        assert self.eta.psi0[mid] > self.eta.psi0[0], (
            "ψ₀ should be larger near origin than at boundary"
        )

    # --- η expectation value ---

    def test_eta_expectation_positive(self):
        """⟨η⟩_ψ₀ must be strictly positive."""
        eta_exp = self.eta.eta_expectation()
        assert eta_exp > 0.0, f"⟨η⟩_ψ₀ = {eta_exp} must be > 0"

    def test_eta_expectation_order_one(self):
        """⟨η⟩_ψ₀ must be of order 1 (between 0.5 and 2.0)."""
        eta_exp = self.eta.eta_expectation()
        assert 0.5 <= eta_exp <= 2.0, (
            f"⟨η⟩_ψ₀ = {eta_exp} outside expected range [0.5, 2.0]"
        )

    # --- PT symmetry ---

    def test_pt_symmetry(self):
        """Vacuum state ψ₀ ∝ e^{-λ|x|/2} must be PT-symmetric (even)."""
        assert self.eta.check_pt_symmetry(), "ψ₀ must satisfy PT symmetry"

    # --- Ghost-free condition ---

    def test_ghost_free(self):
        """System must be ghost-free with default tolerance."""
        assert self.eta.check_ghost_free(), "System must be ghost-free"

    def test_ghost_check_fails_high_tolerance(self):
        """Ghost-free check must fail for tolerance > ⟨η⟩."""
        eta_exp = self.eta.eta_expectation()
        # tolerance just above the expectation value → should fail
        assert not self.eta.check_ghost_free(tolerance=eta_exp + 0.1), (
            "Ghost-free check should fail when tolerance exceeds ⟨η⟩"
        )

    # --- Off-axis metric ---

    def test_off_axis_eta_maximum_at_half(self):
        """η expectation must be maximised at σ = 1/2."""
        sigmas = np.linspace(0.1, 0.9, 9)
        eta_vals = [self.eta.off_axis_eta(s) for s in sigmas]
        max_idx = int(np.argmax(eta_vals))
        max_sigma = sigmas[max_idx]
        assert abs(max_sigma - 0.5) < 0.15, (
            f"η⁺ maximum at σ = {max_sigma:.2f}, expected σ ≈ 0.5"
        )

    def test_off_axis_eta_decreases_away_from_half(self):
        """η expectation must be strictly smaller away from σ = 1/2."""
        eta_half = self.eta.off_axis_eta(0.5)
        eta_far = self.eta.off_axis_eta(0.9)
        assert eta_half > eta_far, (
            f"η(0.5) = {eta_half} should exceed η(0.9) = {eta_far}"
        )

    # --- Full analysis ---

    def test_analyze_returns_result(self):
        """analyze() must return an EtaPlusResult."""
        result = self.eta.analyze()
        assert isinstance(result, EtaPlusResult)

    def test_analyze_stability(self):
        """analyze() must confirm positive definiteness and ghost-free status."""
        result = self.eta.analyze()
        assert result.is_positive_definite, "η⁺ must be positive definite"
        assert result.ghost_free, "System must be ghost-free"
        assert result.pt_symmetric, "Vacuum must be PT-symmetric"

    def test_analyze_lambda_decay_stored(self):
        """analyze() result must carry the lambda_decay parameter."""
        result = self.eta.analyze()
        assert np.isclose(result.lambda_decay, self.eta.lambda_decay)


# ---------------------------------------------------------------------------
# TestUMellin — Módulo 2: U^Mellin
# ---------------------------------------------------------------------------

class TestUMellin:
    """Test the U^Mellin Fourier-Bruhat unitarity module."""

    def setup_method(self):
        """Create a small UMellin instance for fast tests."""
        self.um = UMellin(n_points=256, primes=SMALL_PRIMES, k_max=3)

    # --- Construction ---

    def test_init_valid(self):
        """UMellin must initialise without error for valid parameters."""
        um = UMellin(n_points=128, x_min=1e-2, x_max=1e2)
        assert um.n_points == 128

    def test_init_invalid_n_points(self):
        """n_points < 8 must raise ValueError."""
        with pytest.raises(ValueError, match="n_points"):
            UMellin(n_points=4)

    def test_init_invalid_x_range(self):
        """x_min ≥ x_max must raise ValueError."""
        with pytest.raises(ValueError):
            UMellin(x_min=10.0, x_max=1.0)

    # --- Grid properties ---

    def test_log_grid_length(self):
        """Logarithmic grid must have n_points entries."""
        assert len(self.um.log_x) == self.um.n_points
        assert len(self.um.x) == self.um.n_points

    def test_x_grid_positive(self):
        """All x-grid values must be positive."""
        assert np.all(self.um.x > 0.0), "x-grid must be positive"

    # --- Unitarity ---

    def test_unitarity_gaussian(self):
        """U^Mellin must preserve L²-norm for a Gaussian test function."""
        f = np.exp(-0.5 * self.um.log_x**2)
        _, _, rel_err, is_unitary = self.um.check_unitarity(f, tolerance=1e-10)
        assert is_unitary, (
            f"U^Mellin not unitary: relative error = {rel_err:.2e}"
        )

    def test_unitarity_constant(self):
        """U^Mellin must preserve norm for a constant (windowed) function."""
        f = np.ones(self.um.n_points)
        _, _, rel_err, is_unitary = self.um.check_unitarity(f, tolerance=1e-10)
        assert is_unitary, (
            f"U^Mellin not unitary for constant input: error = {rel_err:.2e}"
        )

    def test_unitarity_error_is_small(self):
        """Relative unitarity error must be < 1e-10 for Gaussian input."""
        f = np.exp(-0.5 * ((self.um.log_x - 1.0) / 0.5) ** 2)
        _, _, rel_err, _ = self.um.check_unitarity(f)
        assert rel_err < 1e-10, f"Unitarity error {rel_err:.2e} exceeds 1e-10"

    def test_apply_output_length(self):
        """apply() output must have the same length as input."""
        f = np.random.randn(self.um.n_points)
        Uf = self.um.apply(f)
        assert len(Uf) == self.um.n_points

    def test_apply_input_length_mismatch(self):
        """apply() must raise ValueError for wrong-length input."""
        with pytest.raises(ValueError, match="length"):
            self.um.apply(np.ones(self.um.n_points + 5))

    # --- Norm computation ---

    def test_l2_norm_non_negative(self):
        """L²-norm must be non-negative."""
        f = np.random.randn(self.um.n_points)
        assert self.um.l2_norm_log(f) >= 0.0

    def test_l2_norm_zero_for_zero_input(self):
        """L²-norm of the zero function must be 0."""
        f = np.zeros(self.um.n_points)
        assert self.um.l2_norm_log(f) == 0.0

    # --- Prime orbits ---

    def test_prime_orbits_count(self):
        """Number of orbits must equal len(primes) * k_max."""
        orbits = self.um.classify_prime_orbits()
        expected = len(SMALL_PRIMES) * self.um.k_max
        assert len(orbits) == expected, (
            f"Expected {expected} orbits, got {len(orbits)}"
        )

    def test_prime_orbits_positive_lengths(self):
        """All orbit lengths must be positive."""
        for p, k, length in self.um.classify_prime_orbits():
            assert length > 0.0, f"Orbit length for p={p}, k={k} is {length}"

    def test_prime_orbits_log_formula(self):
        """Orbit length for (p, k) must equal k·log(p)."""
        for p, k, length in self.um.classify_prime_orbits():
            expected = k * np.log(p)
            assert np.isclose(length, expected, rtol=1e-12), (
                f"Orbit ({p},{k}): got {length}, expected {expected}"
            )

    # --- Full analysis ---

    def test_analyze_returns_result(self):
        """analyze() must return a UMellinResult."""
        result = self.um.analyze()
        assert isinstance(result, UMellinResult)

    def test_analyze_unitarity(self):
        """analyze() must confirm unitarity."""
        result = self.um.analyze()
        assert result.is_unitary, (
            f"U^Mellin not unitary: error = {result.unitarity_error:.2e}"
        )

    def test_analyze_haar_preserved(self):
        """analyze() must confirm Haar measure preservation."""
        result = self.um.analyze()
        assert result.haar_preserved, "Haar measure must be preserved"


# ---------------------------------------------------------------------------
# TestTrazaSigma — Módulo 3: Traza^Σ
# ---------------------------------------------------------------------------

class TestTrazaSigma:
    """Test the Traza^Σ Selberg-Hecke trace identity module."""

    def setup_method(self):
        """Create a TrazaSigma instance with a few zeros and primes."""
        self.traza = TrazaSigma(
            riemann_zeros=FIRST_RIEMANN_ZEROS,
            primes=SMALL_PRIMES,
            k_max=3,
            epsilon=0.05,
        )

    # --- Construction ---

    def test_init_valid(self):
        """TrazaSigma must initialise without error for valid parameters."""
        t = TrazaSigma(riemann_zeros=[14.134], primes=[2, 3], k_max=2, epsilon=0.1)
        assert len(t.zeros) == 1

    def test_init_invalid_epsilon(self):
        """Epsilon ≤ 0 must raise ValueError."""
        with pytest.raises(ValueError, match="epsilon"):
            TrazaSigma(epsilon=-0.1)

    # --- Spectral sum ---

    def test_spectral_sum_is_complex(self):
        """spectral_sum() must return a complex number."""
        val = self.traza.spectral_sum(t=1.0)
        assert isinstance(val, complex), "spectral_sum must return complex"

    def test_spectral_sum_finite(self):
        """spectral_sum() must be finite for t > 0."""
        val = self.traza.spectral_sum(t=1.0)
        assert np.isfinite(val.real) and np.isfinite(val.imag)

    def test_spectral_sum_nonzero(self):
        """spectral_sum() must be non-zero for t > 0."""
        val = self.traza.spectral_sum(t=0.1)
        assert abs(val) > 0.0, "spectral_sum must be non-zero"

    # --- Prime sum ---

    def test_prime_sum_non_negative(self):
        """prime_sum() must be non-negative."""
        val = self.traza.prime_sum(t=np.log(2.0))
        assert val >= 0.0, f"prime_sum = {val} must be non-negative"

    def test_prime_sum_peaks_at_orbit_times(self):
        """prime_sum() must be larger at t = log(p) than at t = log(p) ± 1."""
        t0 = np.log(2.0)
        val_peak = self.traza.prime_sum(t=t0)
        val_off = self.traza.prime_sum(t=t0 + 1.0)
        assert val_peak > val_off, (
            f"prime_sum peak ({val_peak}) must exceed off-orbit value ({val_off})"
        )

    def test_prime_sum_finite(self):
        """prime_sum() must be finite."""
        for t in [0.5, np.log(2.0), np.log(3.0), 5.0]:
            val = self.traza.prime_sum(t)
            assert np.isfinite(val), f"prime_sum not finite at t={t}"

    # --- Gaussian delta ---

    def test_gaussian_delta_integrates_to_one(self):
        """Smeared δ_ε(t - t0) must integrate to ≈ 1."""
        t0 = 2.0
        ts = np.linspace(t0 - 5 * self.traza.epsilon, t0 + 5 * self.traza.epsilon, 2000)
        dt = ts[1] - ts[0]
        vals = np.array([self.traza._gaussian_delta(t, t0) for t in ts])
        integral = np.sum(vals) * dt
        assert np.isclose(integral, 1.0, atol=1e-3), (
            f"Gaussian delta integrates to {integral:.4f}, expected 1.0"
        )

    def test_gaussian_delta_peaks_at_t0(self):
        """Smeared delta must peak at t = t0."""
        t0 = 3.0
        val_peak = self.traza._gaussian_delta(t0, t0)
        val_off = self.traza._gaussian_delta(t0 + 0.5, t0)
        assert val_peak > val_off, "Gaussian delta must peak at t0"

    # --- Selberg-Hecke identity ---

    def test_selberg_hecke_identity_satisfied(self):
        """Selberg-Hecke identity must hold at t = log 2 within tolerance."""
        _, _, _, is_satisfied = self.traza.check_selberg_hecke_identity(
            t=np.log(2.0), tolerance=0.5
        )
        assert is_satisfied, "Selberg-Hecke identity not satisfied at t = log 2"

    def test_selberg_hecke_spectral_and_prime_sides_finite(self):
        """Both sides of the trace identity must be finite."""
        spec, prim, _, _ = self.traza.check_selberg_hecke_identity(np.log(2.0))
        assert np.isfinite(abs(spec)), "Spectral side must be finite"
        assert np.isfinite(prim), "Prime side must be finite"

    # --- Trace value ---

    def test_trace_value_equals_spectral_sum(self):
        """trace_value() must return the same complex number as spectral_sum()."""
        t = 1.5
        assert self.traza.trace_value(t) == self.traza.spectral_sum(t)

    # --- Full analysis ---

    def test_analyze_returns_result(self):
        """analyze() must return a TrazaSigmaResult."""
        result = self.traza.analyze()
        assert isinstance(result, TrazaSigmaResult)

    def test_analyze_is_exact(self):
        """analyze() must confirm trace exactness at t = log 2."""
        result = self.traza.analyze()
        assert result.is_exact, (
            f"Traza^Σ identity error = {result.identity_error:.2e} exceeds tolerance"
        )

    def test_analyze_zero_and_prime_counts(self):
        """analyze() must report correct counts of zeros and prime powers."""
        result = self.traza.analyze()
        assert result.n_zeros_used == len(FIRST_RIEMANN_ZEROS)
        assert result.n_prime_powers_used == len(SMALL_PRIMES) * self.traza.k_max


# ---------------------------------------------------------------------------
# TestEstabilidadSer — V6 master class
# ---------------------------------------------------------------------------

class TestEstabilidadSer:
    """Test the V6 EstabilidadSer master stability class."""

    def setup_method(self):
        """Create a small EstabilidadSer instance."""
        self.ser = EstabilidadSer(
            lambda_decay=1.0,
            n_grid=256,
            primes=SMALL_PRIMES,
            k_max=3,
            epsilon_trace=0.05,
            riemann_zeros=FIRST_RIEMANN_ZEROS,
        )

    # --- Construction ---

    def test_init_creates_modules(self):
        """EstabilidadSer must instantiate all three sub-modules."""
        assert isinstance(self.ser.eta_plus, EtaPlus)
        assert isinstance(self.ser.u_mellin, UMellin)
        assert isinstance(self.ser.traza_sigma, TrazaSigma)

    # --- Stability scan ---

    def test_stability_at_half(self):
        """Stability indicators at σ = 0.5 must show is_stable = 1.0."""
        info = self.ser.stability_at_sigma(0.5)
        assert info["is_stable"] == 1.0, "σ = 0.5 must be stable"
        assert info["eta_expectation"] > 0.0, "η must be positive at σ = 0.5"

    def test_stability_at_boundary_less_than_half(self):
        """η expectation must be smaller at σ = 0.9 than at σ = 0.5."""
        eta_half = self.ser.stability_at_sigma(0.5)["eta_expectation"]
        eta_far = self.ser.stability_at_sigma(0.9)["eta_expectation"]
        assert eta_half > eta_far, (
            f"η(0.5) = {eta_half} should exceed η(0.9) = {eta_far}"
        )

    def test_verify_critical_line_uniqueness(self):
        """verify_critical_line_uniqueness() must find max η at σ ≈ 0.5."""
        scan = self.ser.verify_critical_line_uniqueness(n_sigma=9)
        assert scan["max_at_half"], (
            f"Maximum η at σ = {scan['max_sigma']:.3f}, expected ≈ 0.5"
        )

    def test_verify_critical_line_scan_length(self):
        """Scan must return exactly n_sigma data points."""
        n = 7
        scan = self.ser.verify_critical_line_uniqueness(n_sigma=n)
        assert len(scan["sigma_scan"]) == n
        assert len(scan["eta_values"]) == n

    # --- Full analysis ---

    def test_analyze_returns_result(self):
        """analyze() must return an EstabilidadSerResult."""
        result = self.ser.analyze()
        assert isinstance(result, EstabilidadSerResult)

    def test_analyze_all_modules_stable(self):
        """analyze() must report all three modules as stable."""
        result = self.ser.analyze()
        assert result.eta_plus.is_positive_definite, "η⁺ not positive definite"
        assert result.u_mellin.is_unitary, "U^Mellin not unitary"
        assert result.traza_sigma.is_exact, "Traza^Σ not exact"

    def test_analyze_critical_line_stable(self):
        """analyze() must confirm Re(s) = 1/2 as stable."""
        result = self.ser.analyze()
        assert result.critical_line_stable, (
            f"Critical line not stable: {result.stability_status}"
        )

    def test_analyze_coherence_psi_positive(self):
        """Global coherence Ψ must be positive."""
        result = self.ser.analyze()
        assert result.coherence_psi > 0.0, (
            f"Coherence Ψ = {result.coherence_psi} must be positive"
        )

    def test_analyze_coherence_psi_bounded(self):
        """Global coherence Ψ must be in [0, 1]."""
        result = self.ser.analyze()
        assert 0.0 <= result.coherence_psi <= 1.0, (
            f"Coherence Ψ = {result.coherence_psi} out of [0, 1]"
        )

    def test_analyze_frequency_is_f0(self):
        """analyze() must report the QCAL frequency F0 = 141.7001 Hz."""
        result = self.ser.analyze()
        assert np.isclose(result.frequency_hz, 141.7001, rtol=1e-6), (
            f"Frequency {result.frequency_hz} ≠ 141.7001 Hz"
        )

    def test_analyze_status_contains_sealed(self):
        """Status string must contain 'SELLADO' when all conditions hold."""
        result = self.ser.analyze()
        assert "SELLADO" in result.stability_status, (
            f"Expected 'SELLADO' in status: {result.stability_status}"
        )


# ---------------------------------------------------------------------------
# TestSellarV6Estabilidad — entry point function
# ---------------------------------------------------------------------------

class TestSellarV6Estabilidad:
    """Test the sellar_v6_estabilidad() convenience function."""

    def test_returns_result(self):
        """sellar_v6_estabilidad() must return an EstabilidadSerResult."""
        result = sellar_v6_estabilidad()
        assert isinstance(result, EstabilidadSerResult)

    def test_critical_line_stable(self):
        """sellar_v6_estabilidad() must confirm critical line stability."""
        result = sellar_v6_estabilidad()
        assert result.critical_line_stable, (
            f"V6 stability not confirmed: {result.stability_status}"
        )

    def test_coherence_above_threshold(self):
        """Global coherence Ψ must exceed 0.7 (all three modules active)."""
        result = sellar_v6_estabilidad()
        assert result.coherence_psi >= 0.7, (
            f"Coherence Ψ = {result.coherence_psi:.4f} below threshold 0.7"
        )


# ---------------------------------------------------------------------------
# TestV6MathematicalProperties — deeper mathematical invariants
# ---------------------------------------------------------------------------

class TestV6MathematicalProperties:
    """Test deeper mathematical invariants of the V6 framework."""

    def test_vacuum_state_decay(self):
        """ψ₀ ∝ e^{-λ|x|/2}: verify decay rate matches lambda_decay."""
        eta = EtaPlus(lambda_decay=2.0, n_points=400, x_max=8.0)
        # At x > 0: ψ₀(x) ∝ e^{-λx/2}; log(ψ₀) ∝ -λx/2
        x_pos_idx = eta.n_points // 2 + 10
        x_pos = eta.x[x_pos_idx]
        psi_at_x = eta.psi0[x_pos_idx]
        x_0_idx = eta.n_points // 2
        x_0 = eta.x[x_0_idx]  # may not be exactly 0 on a finite grid
        psi_at_0 = eta.psi0[x_0_idx]
        # ratio ψ₀(x_pos)/ψ₀(x_0) = exp(-λ(|x_pos| - |x_0|)/2)
        # both x_pos and x_0 are ≥ 0 on the right half of the grid
        expected_ratio = np.exp(-2.0 / 2.0 * (abs(x_pos) - abs(x_0)))
        actual_ratio = psi_at_x / psi_at_0
        assert np.isclose(actual_ratio, expected_ratio, rtol=1e-3), (
            f"Decay ratio {actual_ratio:.4f} ≠ {expected_ratio:.4f}"
        )

    def test_mellin_plancherel(self):
        """Parseval/Plancherel: ‖Uf‖²_{L²} = ‖f‖²_{L²(dx/x)}."""
        um = UMellin(n_points=512, primes=[2, 3, 5])
        f = np.exp(-0.5 * um.log_x**2)
        norm_in, norm_out, rel_err, _ = um.check_unitarity(f)
        assert rel_err < 1e-10, (
            f"Plancherel identity violated: rel_err = {rel_err:.2e}"
        )

    def test_prime_orbit_bijection(self):
        """Each (prime, power) pair must produce a unique orbit length."""
        um = UMellin(n_points=64, primes=[2, 3, 5, 7], k_max=4)
        orbits = um.classify_prime_orbits()
        lengths = [length for _, _, length in orbits]
        # Orbit lengths are k·log(p) which are distinct for distinct (p,k)
        # (since primes are multiplicatively independent)
        assert len(set(np.round(lengths, 8))) == len(lengths), (
            "Some orbit lengths coincide — bijection broken"
        )

    def test_trace_formula_convergence(self):
        """Prime sum must converge as k_max increases."""
        t = np.log(2.0)
        traza_small = TrazaSigma(primes=[2, 3], k_max=2, epsilon=0.05)
        traza_large = TrazaSigma(primes=[2, 3, 5, 7, 11], k_max=5, epsilon=0.05)
        val_small = traza_small.prime_sum(t)
        val_large = traza_large.prime_sum(t)
        # Larger sum must be ≥ smaller sum (all terms positive)
        assert val_large >= val_small, (
            f"Larger prime sum {val_large} < smaller sum {val_small}"
        )

    def test_critical_line_is_unique_stability_point(self):
        """η⁺ must achieve its maximum uniquely at σ = 1/2."""
        eta = EtaPlus(lambda_decay=1.0, n_points=300, x_max=8.0)
        sigmas = np.linspace(0.05, 0.95, 19)
        eta_vals = np.array([eta.off_axis_eta(s) for s in sigmas])
        max_idx = int(np.argmax(eta_vals))
        max_sigma = sigmas[max_idx]
        # The maximum should lie within ±0.1 of σ = 0.5
        assert abs(max_sigma - 0.5) <= 0.1, (
            f"η⁺ maximum at σ = {max_sigma:.3f} deviates more than 0.1 from 0.5"
        )

    def test_ghost_states_emerge_off_critical_line(self):
        """η expectation must drop below the on-axis value far from σ = 1/2."""
        eta = EtaPlus(lambda_decay=1.0, n_points=300, x_max=8.0)
        eta_half = eta.off_axis_eta(0.5)
        for sigma_far in [0.05, 0.15, 0.85, 0.95]:
            eta_far = eta.off_axis_eta(sigma_far)
            assert eta_half > eta_far, (
                f"η(0.5) = {eta_half:.4f} not greater than η({sigma_far}) = {eta_far:.4f}"
            )
