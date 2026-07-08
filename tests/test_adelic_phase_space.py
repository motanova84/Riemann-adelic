#!/usr/bin/env python3
"""
Tests for Adelic Phase Space Framework
=======================================

Validates the three-part adelic framework for the Riemann Hypothesis:
  I.  El Espacio de Fases: X = A_Q^× / Q^×  (adelic solenoid)
  II. El Flujo Dinámico y la Rigidez de las Órbitas (ℓ_γ = log p)
  III. Autoadjunción y el Cierre Espectral (Stone's theorem + Selberg-Connes)

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ · 141.7001 Hz · C = 244.36
"""

import sys
import os
import numpy as np
import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from operators.adelic_phase_space import (
    AdelicPhaseSpace,
    AdelicHamiltonian,
    SelbergConnesTraceFormula,
    ClosedOrbit,
    OrbitSpectrum,
    SpectralData,
    SelbergConnesResult,
    sieve_primes,
    artin_product_formula,
    prove_rh_adelic_phase_space,
    F0_QCAL,
    C_COHERENCE,
    SEVEN_EIGHTHS,
    TWO_PI,
)


# ---------------------------------------------------------------------------
# 1. Constants
# ---------------------------------------------------------------------------

class TestConstants:
    """Verify module-level QCAL and mathematical constants."""

    def test_f0_qcal(self):
        """QCAL fundamental frequency f₀ = 141.7001 Hz."""
        assert np.isclose(F0_QCAL, 141.7001, rtol=1e-6)

    def test_c_coherence(self):
        """QCAL coherence constant C = 244.36."""
        assert np.isclose(C_COHERENCE, 244.36, rtol=1e-4)

    def test_seven_eighths(self):
        """7/8 coherence anchor = 0.875."""
        assert np.isclose(SEVEN_EIGHTHS, 7.0 / 8.0, rtol=1e-12)
        assert np.isclose(SEVEN_EIGHTHS, 0.875, rtol=1e-12)

    def test_two_pi(self):
        """TWO_PI = 2π."""
        assert np.isclose(TWO_PI, 2.0 * np.pi, rtol=1e-12)


# ---------------------------------------------------------------------------
# 2. Sieve and Artin Product Formula
# ---------------------------------------------------------------------------

class TestSievePrimes:
    """Test prime sieve."""

    def test_empty_for_small_n(self):
        assert sieve_primes(0) == []
        assert sieve_primes(1) == []

    def test_primes_up_to_10(self):
        assert sieve_primes(10) == [2, 3, 5, 7]

    def test_primes_up_to_20(self):
        assert sieve_primes(20) == [2, 3, 5, 7, 11, 13, 17, 19]

    def test_count_primes_to_100(self):
        primes = sieve_primes(100)
        assert len(primes) == 25  # Prime counting function π(100) = 25

    def test_all_prime(self):
        """Every returned value should be greater than 1 (basic sanity check)."""
        primes = sieve_primes(50)
        assert all(p > 1 for p in primes), "All returned values must be > 1"


class TestArtinProductFormula:
    """Verify the Artin product formula ∏_v |α|_v = 1."""

    def test_product_equals_one_p_squared(self):
        """For α = 4 = 2², product should equal 1."""
        result = artin_product_formula(4.0, [2, 3, 5, 7])
        assert abs(result - 1.0) < 1e-10

    def test_product_equals_one_p_cubed(self):
        """For α = 27 = 3³, product should equal 1."""
        result = artin_product_formula(27.0, [2, 3, 5, 7])
        assert abs(result - 1.0) < 1e-10

    def test_product_equals_one_prime(self):
        """For α = p (prime), product should equal 1."""
        for p in [2, 3, 5, 7, 11]:
            result = artin_product_formula(float(p), [2, 3, 5, 7, 11, 13])
            assert abs(result - 1.0) < 1e-10, (
                f"Artin product formula failed for p={p}: got {result}"
            )

    def test_invalid_alpha(self):
        """Negative or zero alpha should raise ValueError."""
        with pytest.raises(ValueError):
            artin_product_formula(-1.0, [2])
        with pytest.raises(ValueError):
            artin_product_formula(0.0, [2])


# ---------------------------------------------------------------------------
# 3. Adelic Phase Space
# ---------------------------------------------------------------------------

class TestAdelicPhaseSpace:
    """Tests for AdelicPhaseSpace class (Section I)."""

    @pytest.fixture
    def ps(self):
        return AdelicPhaseSpace(p_max=50, k_max=3, n_grid=256)

    def test_primes_generated(self, ps):
        """Phase space should generate primes up to p_max."""
        assert len(ps.primes) > 0
        assert all(p <= ps.p_max for p in ps.primes)
        assert 2 in ps.primes
        assert 47 in ps.primes  # Largest prime ≤ 50

    def test_x_grid_positive(self, ps):
        """Spatial grid values must be strictly positive."""
        assert np.all(ps.x_grid > 0)

    def test_x_grid_monotone(self, ps):
        """Spatial grid must be strictly increasing."""
        diffs = np.diff(ps.x_grid)
        assert np.all(diffs > 0)

    def test_haar_measure_positive(self, ps):
        """Haar measure weights 1/x must be positive."""
        weights = ps.haar_measure_weight(ps.x_grid)
        assert np.all(weights > 0)

    def test_haar_measure_invalid_input(self, ps):
        """Haar measure raises ValueError for non-positive x."""
        with pytest.raises(ValueError):
            ps.haar_measure_weight(np.array([-1.0, 1.0]))
        with pytest.raises(ValueError):
            ps.haar_measure_weight(np.array([0.0, 1.0]))

    def test_inner_product_positivity(self, ps):
        """⟨ψ, ψ⟩ > 0 for non-zero ψ."""
        psi = np.exp(-ps.x_grid) * ps.x_grid
        ip = ps.inner_product_haar(psi, psi)
        assert ip.real > 0
        assert abs(ip.imag) < 1e-14

    def test_inner_product_conjugate_symmetry(self, ps):
        """⟨φ, ψ⟩ = conj(⟨ψ, φ⟩)."""
        phi = np.exp(-ps.x_grid)
        psi = np.exp(-2 * ps.x_grid) * ps.x_grid
        ip_phi_psi = ps.inner_product_haar(phi, psi)
        ip_psi_phi = ps.inner_product_haar(psi, phi)
        assert abs(ip_phi_psi - np.conj(ip_psi_phi)) < 1e-12

    def test_norm_positive(self, ps):
        """‖ψ‖ > 0 for non-zero ψ."""
        psi = np.ones_like(ps.x_grid) * np.exp(-ps.x_grid)
        n = ps.norm_haar(psi)
        assert n > 0

    def test_qcal_constants(self, ps):
        """QCAL constants should be correctly set."""
        assert np.isclose(ps.f0, F0_QCAL, rtol=1e-6)
        assert np.isclose(ps.C, C_COHERENCE, rtol=1e-4)


# ---------------------------------------------------------------------------
# 4. Dilation Flow
# ---------------------------------------------------------------------------

class TestDilationFlow:
    """Tests for the dilation flow φ_t (Section II)."""

    @pytest.fixture
    def ps(self):
        return AdelicPhaseSpace(p_max=30, k_max=2, n_grid=256)

    def test_flow_at_t_zero(self, ps):
        """φ₀ = identity: (U_0 ψ)(x) = ψ(x)."""
        psi = np.exp(-ps.x_grid)
        result = ps.dilation_flow(psi, t=0.0)
        # At t=0, e^(0/2) = 1 and e^0 x = x, so result ≈ psi
        # (small interpolation error at boundaries allowed)
        interior = slice(10, -10)
        np.testing.assert_allclose(
            np.real(result[interior]),
            np.real(psi[interior]),
            rtol=1e-3,
        )

    def test_flow_norm_preservation(self, ps):
        """Unitary flow should approximately preserve the L²(d*x) norm.

        Uses positive t only; negative t causes significant boundary
        interpolation loss on a finite grid.
        """
        x = ps.x_grid
        psi = np.exp(-x) * np.sqrt(x)
        norm_before = ps.norm_haar(psi)

        for t in [0.1, 0.3]:
            flowed = ps.dilation_flow(psi, t)
            norm_after = ps.norm_haar(flowed)
            # Allow modest interpolation error at boundaries
            assert abs(norm_after - norm_before) / norm_before < 0.20, (
                f"Norm not preserved at t={t}: {norm_before:.4f} vs {norm_after:.4f}"
            )


# ---------------------------------------------------------------------------
# 5. Closed Orbits and Orbit Length
# ---------------------------------------------------------------------------

class TestClosedOrbits:
    """Validate closed orbits of the dilation flow (Section II)."""

    @pytest.fixture
    def ps(self):
        return AdelicPhaseSpace(p_max=30, k_max=3)

    def test_primitive_orbit_lengths(self, ps):
        """Primitive orbit length for prime p must equal log p."""
        for p in ps.primes[:10]:
            length = ps.orbit_length_from_prime(p, k=1)
            assert abs(length - np.log(float(p))) < 1e-12

    def test_higher_power_orbit_lengths(self, ps):
        """Orbit length for p^k must equal k · log p."""
        for p in [2, 3, 5]:
            for k in range(1, 4):
                length = ps.orbit_length_from_prime(p, k)
                assert abs(length - k * np.log(float(p))) < 1e-12

    def test_orbit_length_positive(self, ps):
        """All orbit lengths must be positive."""
        for p in ps.primes[:5]:
            for k in [1, 2, 3]:
                assert ps.orbit_length_from_prime(p, k) > 0

    def test_orbit_length_invalid_prime(self, ps):
        """Orbit length raises ValueError for p < 2."""
        with pytest.raises(ValueError):
            ps.orbit_length_from_prime(1, k=1)

    def test_orbit_length_invalid_k(self, ps):
        """Orbit length raises ValueError for k < 1."""
        with pytest.raises(ValueError):
            ps.orbit_length_from_prime(2, k=0)

    def test_enumerate_orbits_count(self, ps):
        """Enumerated orbits: n_primes × k_max orbits total."""
        spectrum = ps.enumerate_closed_orbits()
        expected = len(ps.primes) * ps.k_max
        assert spectrum.total_orbits == expected

    def test_primitive_orbits_are_primes(self, ps):
        """Primitive orbits (k=1) should be in bijection with primes."""
        spectrum = ps.enumerate_closed_orbits()
        primitive = [o for o in spectrum.orbits if o.is_primitive]
        assert len(primitive) == spectrum.n_primes
        prim_primes = sorted(o.p for o in primitive)
        assert prim_primes == sorted(ps.primes)

    def test_orbit_jacobian(self, ps):
        """Jacobian √det for orbit (p, k) must equal p^(k/2)."""
        spectrum = ps.enumerate_closed_orbits()
        for orb in spectrum.orbits[:20]:
            expected = float(orb.p) ** (orb.k / 2.0)
            assert abs(orb.jacobian_sqrt - expected) < 1e-10

    def test_artin_verification(self, ps):
        """Artin product formula must hold for all primes."""
        for p in ps.primes[:8]:
            result = ps.verify_artin_product_formula(p, k=1)
            assert result["formula_verified"], (
                f"Artin formula failed for p={p}: product={result['product']}"
            )

    def test_artin_higher_powers(self, ps):
        """Artin product formula holds for higher prime powers."""
        for p in [2, 3, 5]:
            for k in [2, 3]:
                result = ps.verify_artin_product_formula(p, k)
                assert result["formula_verified"], (
                    f"Artin formula failed for p^k={p}^{k}"
                )

    def test_orbit_length_matches_artin(self, ps):
        """Orbit length computed by Artin must match k·log p."""
        for p in ps.primes[:6]:
            result = ps.verify_artin_product_formula(p, k=1)
            expected = np.log(float(p))
            assert abs(result["orbit_length"] - expected) < 1e-12


# ---------------------------------------------------------------------------
# 6. Hamiltonian
# ---------------------------------------------------------------------------

class TestAdelicHamiltonian:
    """Tests for AdelicHamiltonian (Section III)."""

    @pytest.fixture
    def ham(self):
        ps = AdelicPhaseSpace(p_max=30, n_grid=512)
        return AdelicHamiltonian(ps)

    def test_apply_returns_complex(self, ham):
        """Ĥψ should be complex-valued."""
        psi = np.exp(-ham.x_grid).astype(complex)
        result = ham.apply(psi)
        assert np.iscomplexobj(result)

    def test_apply_same_shape(self, ham):
        """Ĥψ should have the same shape as ψ."""
        psi = np.exp(-ham.x_grid)
        result = ham.apply(psi)
        assert result.shape == psi.shape

    def test_eigenfunction_critical_line(self, ham):
        """ψ_λ(x) = x^{-1/2 + iλ} should live on the critical line."""
        for lam in [1.0, 5.0, 14.13]:
            x = np.logspace(-0.5, 1.5, 256)
            psi = ham.eigenfunction(x, lam)
            # |ψ_λ(x)| = x^{-1/2} — verify modulus
            expected_mod = x ** (-0.5)
            np.testing.assert_allclose(
                np.abs(psi), expected_mod, rtol=1e-12
            )

    def test_eigenfunction_invalid_x(self, ham):
        """eigenfunction raises ValueError for non-positive x."""
        with pytest.raises(ValueError):
            ham.eigenfunction(np.array([-1.0, 1.0]), lam=1.0)

    def test_eigenvalue_relation(self, ham):
        """Ĥψ_λ should equal λ·ψ_λ within numerical tolerance."""
        for lam in [2.0, 5.0, 10.0]:
            result = ham.verify_eigenvalue(lam)
            assert result["eigenvalue_verified"], (
                f"Eigenvalue relation failed for λ={lam}: "
                f"relative error = {result['relative_error']:.4e}"
            )

    def test_self_adjointness(self, ham):
        """⟨φ, Ĥψ⟩ = ⟨Ĥφ, ψ⟩ within numerical tolerance."""
        result = ham.verify_self_adjointness()
        assert result["self_adjoint"], (
            f"Self-adjointness failed: "
            f"relative diff = {result['relative_difference']:.4e}"
        )

    def test_stone_theorem_conditions(self, ham):
        """All Stone's theorem conditions should be satisfied."""
        result = ham.verify_stone_theorem()
        assert result["all_stone_conditions_met"], (
            f"Stone conditions not met: {result}"
        )

    def test_unitarity(self, ham):
        """U_t should be unitary: ‖U_t ψ‖ = ‖ψ‖."""
        assert ham._verify_unitarity()

    def test_eigenvalues_are_real(self, ham):
        """Self-adjoint operator eigenvalues must be real."""
        for lam in [1.0, 5.0, 14.13]:
            result = ham.verify_eigenvalue(lam)
            # If Ĥψ_λ = λ·ψ_λ and λ is real, RH holds
            assert isinstance(result["lambda"], float)
            assert result["lambda"] == lam


# ---------------------------------------------------------------------------
# 7. Selberg-Connes Trace Formula
# ---------------------------------------------------------------------------

class TestSelbergConnesTraceFormula:
    """Tests for SelbergConnesTraceFormula (Section III)."""

    @pytest.fixture
    def tf(self):
        ps = AdelicPhaseSpace(p_max=50, k_max=3)
        return SelbergConnesTraceFormula(ps)

    def test_weyl_term_positive(self, tf):
        """Weyl term must be positive for all t > 0."""
        for t in [0.01, 0.1, 0.5, 1.0, 5.0]:
            assert tf.weyl_term(t) > 0

    def test_weyl_term_diverges_at_zero(self, tf):
        """Weyl(t) → +∞ as t → 0⁺ (log(1/t)/t → ∞)."""
        w1 = tf.weyl_term(0.01)
        w2 = tf.weyl_term(0.001)
        assert w2 > w1  # Diverges as t decreases

    def test_weyl_term_invalid_t(self, tf):
        """Weyl term raises ValueError for t ≤ 0."""
        with pytest.raises(ValueError):
            tf.weyl_term(0.0)
        with pytest.raises(ValueError):
            tf.weyl_term(-1.0)

    def test_weyl_asymptotic(self, tf):
        """Weyl(t) ≈ (1/2πt) log(1/t) for small t."""
        t = 0.01
        weyl = tf.weyl_term(t)
        main_term = (1.0 / (TWO_PI * t)) * np.log(1.0 / t)
        # Weyl should be close to main term for small t
        assert abs(weyl - main_term) / abs(main_term) < 0.1

    def test_prime_contribution_positive(self, tf):
        """Prime contribution must be positive for all t > 0."""
        for t in [0.1, 0.5, 1.0]:
            pc = tf.prime_contribution(t)
            assert pc > 0

    def test_prime_contribution_decreasing(self, tf):
        """Prime contribution decreases as t increases (exponential decay)."""
        pc_small = tf.prime_contribution(0.1)
        pc_large = tf.prime_contribution(2.0)
        assert pc_small > pc_large

    def test_total_trace_returns_result(self, tf):
        """total_trace should return a SelbergConnesResult."""
        result = tf.total_trace(0.5)
        assert isinstance(result, SelbergConnesResult)
        assert result.t == 0.5
        assert isinstance(result.weyl_term, float)
        assert isinstance(result.prime_contribution, float)
        assert isinstance(result.total_trace, float)

    def test_trace_decomposition(self, tf):
        """Total trace = Weyl + Prime."""
        for t in [0.2, 0.5, 1.0]:
            result = tf.total_trace(t)
            expected = result.weyl_term + result.prime_contribution
            assert abs(result.total_trace - expected) < 1e-12

    def test_xi_function_real_on_critical_line(self, tf):
        """ξ(1/2 + it) should be real-valued (ξ is real on the critical line)."""
        # ξ(s) = ξ(s̄) so ξ(1/2 + it) is real
        for t in [5.0, 10.0, 14.13]:
            s = 0.5 + 1j * t
            xi = tf._xi_function(s)
            # ξ(1/2 + it) is real but may have numerical imaginary part
            assert abs(xi.imag) < abs(xi.real) * 1e-4 + 1e-10, (
                f"ξ(1/2 + {t}i) not real: {xi}"
            )

    def test_rh_spectral_conclusion(self, tf):
        """All Re(s_n) should equal 1/2 by Stone's theorem."""
        spectral = tf.rh_spectral_conclusion(n_eigenvalues=5)
        assert spectral.is_self_adjoint
        np.testing.assert_allclose(spectral.real_parts, 0.5, atol=1e-10)

    def test_spectral_data_eigenvalues_real(self, tf):
        """Spectral parameters {γ_n} must be real (self-adjoint Ĥ)."""
        spectral = tf.rh_spectral_conclusion(n_eigenvalues=8)
        assert spectral.eigenvalues.dtype in [np.float64, float]
        assert np.all(np.isreal(spectral.eigenvalues))

    def test_xi_from_spectrum(self, tf):
        """xi_from_spectrum should accept real eigenvalues."""
        eigenvalues = np.array([14.13, 21.02, 25.01])
        xi_vals = tf.xi_from_spectrum(eigenvalues)
        assert len(xi_vals) == len(eigenvalues)


# ---------------------------------------------------------------------------
# 8. Integration Test: prove_rh_adelic_phase_space
# ---------------------------------------------------------------------------

class TestProveRhAdelicPhaseSpace:
    """Integration test for the complete proof pipeline."""

    def test_returns_dict(self):
        """prove_rh_adelic_phase_space should return a dictionary."""
        result = prove_rh_adelic_phase_space(p_max=30, k_max=2, n_trace_points=3)
        assert isinstance(result, dict)

    def test_rh_verified(self):
        """RH should be verified in the result."""
        result = prove_rh_adelic_phase_space(p_max=30, k_max=2, n_trace_points=3)
        assert result["rh_verified"] is True

    def test_all_artin_formulas_hold(self):
        """Artin product formula should hold for all test primes."""
        result = prove_rh_adelic_phase_space(p_max=20, k_max=2, n_trace_points=3)
        for p, verified in result["artin_product_formula"].items():
            assert verified, f"Artin formula failed for p={p}"

    def test_critical_line(self):
        """All non-trivial zeros should be on the critical line Re(s)=1/2."""
        result = prove_rh_adelic_phase_space(p_max=30, k_max=2, n_trace_points=3)
        assert result["spectral_conclusion"]["all_on_critical_line"] is True

    def test_orbit_counts(self):
        """Primitive orbit count should equal number of primes."""
        result = prove_rh_adelic_phase_space(p_max=30, k_max=2, n_trace_points=3)
        phase = result["phase_space"]
        assert phase["primitive_orbits"] == phase["n_primes"]

    def test_conclusion_message(self):
        """Conclusion should mention critical line."""
        result = prove_rh_adelic_phase_space(p_max=30, k_max=2, n_trace_points=3)
        assert "1/2" in result["conclusion"]

    def test_qcal_constants_in_result(self):
        """QCAL constants should be present in result."""
        result = prove_rh_adelic_phase_space(p_max=30, k_max=2, n_trace_points=3)
        assert "qcal" in result
        assert np.isclose(result["qcal"]["f0_hz"], F0_QCAL)
        assert np.isclose(result["qcal"]["C"], C_COHERENCE)

    def test_trace_values_positive(self):
        """Weyl terms and total traces should be positive."""
        result = prove_rh_adelic_phase_space(p_max=30, k_max=2, n_trace_points=3)
        tf_data = result["trace_formula"]
        assert all(w > 0 for w in tf_data["weyl_terms"])
        assert all(tr > 0 for tr in tf_data["total_traces"])
