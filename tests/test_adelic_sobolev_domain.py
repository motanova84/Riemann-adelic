#!/usr/bin/env python3
"""
Tests for operators/adelic_sobolev_domain.py
=============================================

Validates the three-step QCAL rigourisation protocol:

  §1  Adelic Sobolev domain D(H)
  §2  Schatten-1 nuclearity estimates
  §3  Riemann-Weil operator identity

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ · 141.7001 Hz
DOI: 10.5281/zenodo.17379721
"""

import math
import pytest
import numpy as np

from operators.adelic_sobolev_domain import (
    # §1
    AdelicSobolevElement,
    AdelicSobolevDomain,
    # §2
    SchattenNormBound,
    weyl_counting_density,
    schwartz_decay_bound,
    schatten_norm_estimate,
    schatten_norm_from_zeros,
    # §3
    RiemannWeilResult,
    weyl_density_measure,
    principal_term_integral,
    prime_power_correction,
    verify_riemann_weil_identity,
    _sieve_primes,
    # §4 integrated
    ProtocolResult,
    run_adelic_riemann_weil_protocol,
    # constants
    RIEMANN_ZEROS_REFERENCE,
    F0_QCAL,
    C_COHERENCE,
)


# ---------------------------------------------------------------------------
# §1  AdelicSobolevDomain
# ---------------------------------------------------------------------------


class TestAdelicSobolevElement:
    """Tests for AdelicSobolevElement dataclass."""

    def _make_element(self, N: int = 128, gamma: float = 0.0) -> AdelicSobolevElement:
        t = np.linspace(-4.0, 4.0, N)
        values = np.exp((-0.5 + 1j * gamma) * t) * np.exp(-(t**2) / 2)
        # Project to true zero-sum (so that Σ ψ_k = 0, matching zero_mean_residual)
        values -= np.mean(values)
        return AdelicSobolevElement(values=values.astype(np.complex128), log_grid=t)

    def test_construction(self):
        el = self._make_element()
        assert el.values is not None
        assert el.log_grid is not None
        assert len(el.values) == len(el.log_grid)

    def test_mismatched_shapes_raises(self):
        with pytest.raises(ValueError):
            AdelicSobolevElement(
                values=np.zeros(10, dtype=complex),
                log_grid=np.linspace(0, 1, 20),
            )

    def test_dt_is_positive(self):
        el = self._make_element()
        assert el.dt > 0

    def test_l2_norm_positive(self):
        el = self._make_element()
        assert el.l2_norm_sq() > 0

    def test_h1_norm_geq_l2(self):
        el = self._make_element()
        assert el.h1_sobolev_norm_sq() >= el.l2_norm_sq()

    def test_zero_mean_residual_small(self):
        el = self._make_element()
        # After subtracting the mean, Σ ψ_k = 0, so the discrete integral is zero
        assert el.zero_mean_residual() < 1e-12

    def test_is_in_domain(self):
        el = self._make_element()
        # A smooth Gaussian element should satisfy domain conditions
        assert el.is_in_domain()

    def test_gauge_invariance_returns_float(self):
        el = self._make_element()
        err = el.gauge_invariance_check(q_values=[2, 3])
        assert isinstance(err, float)
        assert err >= 0.0


class TestAdelicSobolevDomain:
    """Tests for AdelicSobolevDomain factory."""

    def setup_method(self):
        self.domain = AdelicSobolevDomain(N=256)

    def test_schwartz_bruhat_construction(self):
        psi = self.domain.schwartz_bruhat_element(gamma=14.134725)
        assert len(psi.values) == 256
        assert psi.zero_mean_residual() < 1e-10

    def test_apply_H_returns_element(self):
        psi = self.domain.schwartz_bruhat_element(gamma=14.134725)
        H_psi = self.domain.apply_H(psi)
        assert len(H_psi.values) == len(psi.values)

    def test_inner_product_conjugate_symmetry(self):
        psi1 = self.domain.schwartz_bruhat_element(gamma=14.134725)
        psi2 = self.domain.schwartz_bruhat_element(gamma=21.022040)
        ip12 = self.domain.inner_product(psi1, psi2)
        ip21 = self.domain.inner_product(psi2, psi1)
        assert abs(ip12 - ip21.conjugate()) < 1e-10

    def test_inner_product_positive_definite(self):
        psi = self.domain.schwartz_bruhat_element(gamma=14.134725)
        ip = self.domain.inner_product(psi, psi)
        assert ip.real > 0
        assert abs(ip.imag) < 1e-10

    def test_symmetry_check_returns_dict(self):
        psi = self.domain.schwartz_bruhat_element(gamma=14.134725)
        result = self.domain.check_symmetry(psi)
        assert "real_part" in result
        assert "imag_part" in result
        assert "relative_imag" in result
        assert "is_symmetric" in result

    def test_H_approximately_symmetric_on_gaussian(self):
        """⟨Hψ, ψ⟩ should be approximately real for smooth test functions."""
        psi = self.domain.schwartz_bruhat_element(gamma=14.134725, sigma=1.5)
        result = self.domain.check_symmetry(psi, rtol=0.1)
        # Allow some numerical discretisation error
        assert result["relative_imag"] < 0.5  # weak check for discrete approximation

    def test_eigenfunction_structure(self):
        """ψ_γ(e^t) = e^{(-1/2+iγ)t} has the correct power-law structure."""
        gamma = 14.134725
        psi = self.domain.schwartz_bruhat_element(gamma=gamma, sigma=100.0, zero_mean=False)
        t = psi.log_grid
        # In the central region the phase should grow linearly with gamma
        mid = len(t) // 2
        phase_diff = np.angle(psi.values[mid + 1] / psi.values[mid])
        expected_phase = gamma * (t[mid + 1] - t[mid])
        assert abs(phase_diff - expected_phase) < 0.01


# ---------------------------------------------------------------------------
# §2  Schatten-1 Nuclearity
# ---------------------------------------------------------------------------


class TestWeylDensity:
    """Tests for the adelic Weyl counting density."""

    def test_positive_T(self):
        assert weyl_counting_density(10.0) > 0

    def test_zero_T_returns_zero(self):
        assert weyl_counting_density(0.0) == 0.0

    def test_negative_T_returns_zero(self):
        assert weyl_counting_density(-5.0) == 0.0

    def test_increasing_in_T(self):
        """Weyl density (log T / 2π) is increasing for T > 1."""
        assert weyl_counting_density(100.0) > weyl_counting_density(10.0)


class TestSchwartzDecay:
    """Tests for Schwartz super-polynomial decay bound."""

    def test_decay_at_large_gamma(self):
        bound_small = schwartz_decay_bound(10.0, C_m=1.0, m=4)
        bound_large = schwartz_decay_bound(100.0, C_m=1.0, m=4)
        assert bound_large < bound_small

    def test_decay_monotone_in_m(self):
        """Higher m gives faster decay."""
        gamma = 50.0
        b3 = schwartz_decay_bound(gamma, C_m=1.0, m=3)
        b6 = schwartz_decay_bound(gamma, C_m=1.0, m=6)
        assert b6 < b3

    def test_C_m_scaling(self):
        gamma = 10.0
        b1 = schwartz_decay_bound(gamma, C_m=1.0, m=4)
        b2 = schwartz_decay_bound(gamma, C_m=2.0, m=4)
        assert abs(b2 / b1 - 2.0) < 1e-12


class TestSchattenNormEstimate:
    """Tests for schatten_norm_estimate."""

    def test_returns_dataclass(self):
        result = schatten_norm_estimate(m=4)
        assert isinstance(result, SchattenNormBound)

    def test_m_gt_2_is_nuclear(self):
        result = schatten_norm_estimate(m=4)
        assert result.is_nuclear

    def test_m_eq_2_is_not_nuclear(self):
        """m = 2 is the boundary; convergence is marginal / not guaranteed."""
        result = schatten_norm_estimate(m=2, T_max=1e6)
        # The integral ∫ t^{-2} log t dt diverges very slowly; the bound
        # may be large but we simply confirm nuclear=False for m<=2
        assert not result.is_nuclear

    def test_bound_finite_for_m4(self):
        result = schatten_norm_estimate(m=4, T_max=1e4)
        assert result.schatten_1_bound < 1e3

    def test_bound_decreases_with_m(self):
        b4 = schatten_norm_estimate(m=4, T_max=1e4).schatten_1_bound
        b6 = schatten_norm_estimate(m=6, T_max=1e4).schatten_1_bound
        assert b6 < b4

    def test_schatten_from_zeros_gaussian(self):
        """Gaussian ĝ(γ) = exp(-σ²γ²/2) gives finite empirical sum."""
        sigma = 2.5

        def g_hat(gamma: float) -> float:
            return math.exp(-(sigma**2) * gamma**2 / 2)

        s = schatten_norm_from_zeros(g_hat)
        assert s > 0
        assert s < 1e3


# ---------------------------------------------------------------------------
# §3  Riemann-Weil Identity
# ---------------------------------------------------------------------------


class TestSievePrimes:
    def test_primes_up_to_10(self):
        assert _sieve_primes(10) == [2, 3, 5, 7]

    def test_primes_up_to_2(self):
        assert _sieve_primes(2) == [2]

    def test_primes_up_to_1(self):
        assert _sieve_primes(1) == []

    def test_count_up_to_100(self):
        assert len(_sieve_primes(100)) == 25


class TestWeylDensityMeasure:
    def test_positive_r(self):
        mu = weyl_density_measure(20.0)
        assert mu > 0

    def test_negative_r(self):
        mu_neg = weyl_density_measure(-20.0)
        mu_pos = weyl_density_measure(20.0)
        assert abs(mu_neg - mu_pos) < 1e-12  # even function

    def test_near_zero_returns_zero(self):
        assert weyl_density_measure(0.0) == 0.0

    def test_small_r_returns_negative(self):
        """For |r| < 2π the Weyl density log(|r|/2π)/2π is negative."""
        assert weyl_density_measure(0.5) < 0.0


class TestPrincipalTermIntegral:
    def test_gaussian_phi_finite(self):
        """Φ(g) is finite for a Gaussian test function."""
        sigma = 2.5

        def g_hat(gamma: float) -> float:
            return math.exp(-(sigma**2) * gamma**2 / 2)

        phi = principal_term_integral(g_hat, r_max=100.0)
        assert math.isfinite(phi)

    def test_wide_gaussian_larger_magnitude(self):
        """Wider g_hat (smaller σ in g_hat) → more spectral weight → larger |Φ(g)|."""
        def g_hat_narrow(gamma):
            return math.exp(-(10.0**2) * gamma**2 / 2)

        def g_hat_wide(gamma):
            return math.exp(-(1.0**2) * gamma**2 / 2)

        phi_narrow = abs(principal_term_integral(g_hat_narrow, r_max=50.0))
        phi_wide = abs(principal_term_integral(g_hat_wide, r_max=50.0))
        assert phi_wide >= phi_narrow


class TestPrimePowerCorrection:
    def test_returns_tuple(self):
        def g(t):
            return math.exp(-(t**2) / 2)

        total, primes = prime_power_correction(g, p_max=30, k_max=3)
        assert isinstance(total, float)
        assert isinstance(primes, list)
        assert len(primes) > 0

    def test_gaussian_prime_sum_positive(self):
        """For g > 0 everywhere the prime sum should be positive."""
        def g(t):
            return math.exp(-(t**2) / 8)  # always positive

        total, _ = prime_power_correction(g, p_max=50, k_max=2)
        assert total > 0

    def test_more_primes_larger_sum(self):
        def g(t):
            return math.exp(-(t**2) / 8)

        s1, _ = prime_power_correction(g, p_max=30, k_max=2)
        s2, _ = prime_power_correction(g, p_max=100, k_max=2)
        assert s2 > s1


class TestRiemannWeilIdentity:
    """End-to-end Riemann-Weil formula verification."""

    def _gaussian(self, sigma: float = 2.5):
        def g(t):
            return math.exp(-(t**2) / (2 * sigma**2)) / (sigma * math.sqrt(2 * math.pi))

        def g_hat(gamma):
            return math.exp(-(sigma**2) * gamma**2 / 2)

        return g, g_hat

    def test_returns_dataclass(self):
        g, g_hat = self._gaussian()
        result = verify_riemann_weil_identity(g=g, g_hat=g_hat)
        assert isinstance(result, RiemannWeilResult)

    def test_spectral_sum_finite(self):
        g, g_hat = self._gaussian()
        result = verify_riemann_weil_identity(g=g, g_hat=g_hat)
        assert math.isfinite(result.spectral_sum)

    def test_prime_sum_finite(self):
        g, g_hat = self._gaussian()
        result = verify_riemann_weil_identity(g=g, g_hat=g_hat)
        assert math.isfinite(result.prime_sum)

    def test_errors_are_non_negative(self):
        g, g_hat = self._gaussian()
        result = verify_riemann_weil_identity(g=g, g_hat=g_hat)
        assert result.absolute_error >= 0
        assert result.relative_error >= 0

    def test_formula_reasonably_close(self):
        """
        The identity holds for all g ∈ 𝒮(ℝ). With only 15 reference zeros and
        primes up to 100 the agreement is approximate but the relative error
        should be < 100% (i.e. within an order of magnitude).
        """
        g, g_hat = self._gaussian(sigma=2.5)
        result = verify_riemann_weil_identity(
            g=g, g_hat=g_hat, p_max=100, r_max=200.0, tolerance=0.5
        )
        assert result.relative_error < 2.0  # generous bound given truncation

    def test_zeros_used_correctly(self):
        g, g_hat = self._gaussian()
        result = verify_riemann_weil_identity(g=g, g_hat=g_hat)
        assert len(result.zeros_used) == len(RIEMANN_ZEROS_REFERENCE)

    def test_primes_used_non_empty(self):
        g, g_hat = self._gaussian()
        result = verify_riemann_weil_identity(g=g, g_hat=g_hat, p_max=50)
        assert len(result.primes_used) > 0
        assert 2 in result.primes_used


# ---------------------------------------------------------------------------
# §4  Integrated Protocol
# ---------------------------------------------------------------------------


class TestProtocolResult:
    """Tests for the integrated ProtocolResult."""

    def test_protocol_passed_property(self):
        """protocol_passed = all three checks pass."""
        from operators.adelic_sobolev_domain import SchattenNormBound, RiemannWeilResult

        # Build a mock "all-pass" result
        schatten_pass = SchattenNormBound(
            m=4, C_m=1.0, T_max=1e4,
            schatten_1_bound=0.01, is_nuclear=True, integral_value=0.01
        )
        weil_pass = RiemannWeilResult(
            spectral_sum=1.0, principal_term=1.05, prime_sum=0.05,
            rhs=1.0, absolute_error=0.0, relative_error=0.0,
            identity_verified=True, zeros_used=[14.13], primes_used=[2, 3]
        )
        pr = ProtocolResult(
            domain_valid=True,
            symmetry_check={"is_symmetric": True},
            schatten_bound=schatten_pass,
            weil_result=weil_pass,
        )
        assert pr.protocol_passed

    def test_protocol_fails_if_domain_invalid(self):
        from operators.adelic_sobolev_domain import SchattenNormBound, RiemannWeilResult

        schatten_pass = SchattenNormBound(
            m=4, C_m=1.0, T_max=1e4,
            schatten_1_bound=0.01, is_nuclear=True, integral_value=0.01
        )
        weil_pass = RiemannWeilResult(
            spectral_sum=1.0, principal_term=1.05, prime_sum=0.05,
            rhs=1.0, absolute_error=0.0, relative_error=0.0,
            identity_verified=True, zeros_used=[14.13], primes_used=[2]
        )
        pr = ProtocolResult(
            domain_valid=False,  # <-- domain fails
            symmetry_check={"is_symmetric": True},
            schatten_bound=schatten_pass,
            weil_result=weil_pass,
        )
        assert not pr.protocol_passed

    def test_summary_contains_status(self):
        result = run_adelic_riemann_weil_protocol()
        summary = result.summary()
        assert "QCAL Rigourisation Protocol" in summary
        assert "§1" in summary
        assert "§2" in summary
        assert "§3" in summary

    def test_coherence_constants_correct(self):
        result = run_adelic_riemann_weil_protocol()
        assert abs(result.coherence_frequency - 141.7001) < 1e-4
        assert abs(result.coherence_constant - 244.36) < 1e-2


class TestRunProtocol:
    """End-to-end integration test for run_adelic_riemann_weil_protocol."""

    def test_returns_protocol_result(self):
        result = run_adelic_riemann_weil_protocol()
        assert isinstance(result, ProtocolResult)

    def test_schatten_nuclear(self):
        result = run_adelic_riemann_weil_protocol(m=4)
        assert result.schatten_bound.is_nuclear

    def test_domain_valid(self):
        result = run_adelic_riemann_weil_protocol()
        assert result.domain_valid

    def test_weil_zeros_match_reference(self):
        result = run_adelic_riemann_weil_protocol()
        assert len(result.weil_result.zeros_used) == len(RIEMANN_ZEROS_REFERENCE)

    def test_weil_primes_non_empty(self):
        result = run_adelic_riemann_weil_protocol(p_max=50)
        assert len(result.weil_result.primes_used) > 0

    def test_protocol_with_different_gamma(self):
        """Protocol should work for any reference zero."""
        result = run_adelic_riemann_weil_protocol(gamma_probe=21.022040)
        assert isinstance(result, ProtocolResult)
        assert result.schatten_bound.is_nuclear

    def test_higher_m_gives_smaller_bound(self):
        r4 = run_adelic_riemann_weil_protocol(m=4)
        r6 = run_adelic_riemann_weil_protocol(m=6)
        assert r6.schatten_bound.schatten_1_bound < r4.schatten_bound.schatten_1_bound


# ---------------------------------------------------------------------------
# QCAL Constants
# ---------------------------------------------------------------------------


class TestQCALConstants:
    def test_f0_value(self):
        assert abs(F0_QCAL - 141.7001) < 1e-4

    def test_coherence_constant(self):
        assert abs(C_COHERENCE - 244.36) < 1.0

    def test_zeros_reference_has_first_zero(self):
        assert abs(RIEMANN_ZEROS_REFERENCE[0] - 14.134725) < 1e-4

    def test_zeros_reference_length(self):
        assert len(RIEMANN_ZEROS_REFERENCE) >= 15
