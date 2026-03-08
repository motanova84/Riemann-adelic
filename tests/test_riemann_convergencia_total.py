#!/usr/bin/env python3
"""
Tests for riemann_convergencia_total — Integración de los Cuatro Dominios
==========================================================================

87 tests across 10 classes covering:

- Constants and module-level attributes
- Helper utilities (_sieve_primes, _first_n_primes, _harmonic_mean)
- GeometryDomain (Berry phase, torus eigenvalues, adelic coherence)
- NumberTheoryDomain (Weil formula, zero sum, prime sum)
- QuantumDomain (Berry-Keating operator, GUE statistics)
- ConscienceDomain (harmonic mean, coherence threshold)
- ConvergenciaTotal (pipeline, certificate, mensaje_final)
- Result dataclasses
- Mathematical properties (harmonic mean bounds, Berry invariant, Weil balance)
- Edge cases

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz
"""

import hashlib
import json
import math
import sys
from pathlib import Path

import numpy as np
import pytest

# ---------------------------------------------------------------------------
# Path setup: add operators directory so imports work both as standalone tests
# and when pytest is run from the repo root.
# ---------------------------------------------------------------------------
_REPO_ROOT = Path(__file__).parent.parent
sys.path.insert(0, str(_REPO_ROOT / "operators"))

from riemann_convergencia_total import (
    # Constants
    F_BASE,
    F_MANIFEST,
    C_COHERENCE,
    PHI,
    BERRY_PHASE_FACTOR,
    PSI_THRESHOLD,
    HARMONIC_RATIO,
    _RIEMANN_ZEROS,
    # Helpers
    _sieve_primes,
    _first_n_primes,
    _harmonic_mean,
    # Result dataclasses
    GeometryResult,
    NumberTheoryResult,
    QuantumResult,
    ConscienceResult,
    ConvergenciaResult,
    # Domain classes
    GeometryDomain,
    NumberTheoryDomain,
    QuantumDomain,
    ConscienceDomain,
    # Integrator
    ConvergenciaTotal,
    # Convenience function
    demostrar_convergencia,
)


# ===========================================================================
# Class 1: Constants
# ===========================================================================


class TestConstants:
    """Module-level QCAL constants."""

    def test_f_base(self):
        assert F_BASE == pytest.approx(141.7001, rel=1e-6)

    def test_f_manifest(self):
        assert F_MANIFEST == pytest.approx(888.0, rel=1e-6)

    def test_berry_phase_factor_exact(self):
        """Berry phase factor must be exactly 7/8."""
        assert BERRY_PHASE_FACTOR == 7.0 / 8.0

    def test_berry_phase_decimal(self):
        assert BERRY_PHASE_FACTOR == pytest.approx(0.875)

    def test_psi_threshold(self):
        assert PSI_THRESHOLD == pytest.approx(0.888)

    def test_harmonic_ratio(self):
        """f_manifest / f_base ≈ 2π (harmonic coupling)."""
        ratio = F_MANIFEST / F_BASE
        assert ratio == pytest.approx(HARMONIC_RATIO, rel=1e-6)

    def test_harmonic_ratio_approx_two_pi(self):
        """The harmonic ratio should be within 1% of 2π."""
        assert abs(HARMONIC_RATIO - 2 * math.pi) / (2 * math.pi) < 0.01

    def test_c_coherence(self):
        assert C_COHERENCE == pytest.approx(244.36, rel=1e-6)

    def test_phi_golden_ratio(self):
        assert PHI == pytest.approx((1 + math.sqrt(5)) / 2, rel=1e-10)

    def test_riemann_zeros_non_empty(self):
        assert len(_RIEMANN_ZEROS) >= 10

    def test_first_riemann_zero(self):
        """First zero imaginary part ≈ 14.1347."""
        assert _RIEMANN_ZEROS[0] == pytest.approx(14.1347, abs=1e-3)

    def test_riemann_zeros_ascending(self):
        """Zeros should be in ascending order."""
        assert all(
            _RIEMANN_ZEROS[i] < _RIEMANN_ZEROS[i + 1]
            for i in range(len(_RIEMANN_ZEROS) - 1)
        )


# ===========================================================================
# Class 2: Helper utilities
# ===========================================================================


class TestHelpers:
    """Tests for _sieve_primes, _first_n_primes, _harmonic_mean."""

    # -- sieve primes ---------------------------------------------------------

    def test_sieve_primes_basic(self):
        primes = _sieve_primes(10)
        assert primes == [2, 3, 5, 7]

    def test_sieve_primes_empty(self):
        assert _sieve_primes(1) == []
        assert _sieve_primes(0) == []

    def test_sieve_primes_includes_upper_bound(self):
        primes = _sieve_primes(7)
        assert 7 in primes

    def test_sieve_primes_count(self):
        """π(100) = 25."""
        assert len(_sieve_primes(100)) == 25

    def test_sieve_primes_all_prime(self):
        for p in _sieve_primes(50):
            for d in range(2, int(p ** 0.5) + 1):
                assert p % d != 0

    # -- first n primes -------------------------------------------------------

    def test_first_n_primes_basic(self):
        assert _first_n_primes(5) == [2, 3, 5, 7, 11]

    def test_first_n_primes_one(self):
        assert _first_n_primes(1) == [2]

    def test_first_n_primes_length(self):
        assert len(_first_n_primes(20)) == 20

    def test_first_n_primes_zero(self):
        assert _first_n_primes(0) == []

    # -- harmonic mean --------------------------------------------------------

    def test_harmonic_mean_equal_values(self):
        """H(a, a, a) = a."""
        assert _harmonic_mean([3.0, 3.0, 3.0]) == pytest.approx(3.0)

    def test_harmonic_mean_less_equal_arithmetic(self):
        """H ≤ arithmetic mean (AM-HM inequality)."""
        vals = [0.9, 0.95, 0.98]
        hm = _harmonic_mean(vals)
        am = sum(vals) / len(vals)
        assert hm <= am + 1e-12

    def test_harmonic_mean_sensitive_to_minimum(self):
        """Harmonic mean is dominated by the smallest value."""
        high = [0.99, 0.99, 0.10]
        hm = _harmonic_mean(high)
        assert hm < 0.99

    def test_harmonic_mean_zero_raises(self):
        with pytest.raises(ValueError):
            _harmonic_mean([1.0, 0.0, 1.0])

    def test_harmonic_mean_negative_raises(self):
        with pytest.raises(ValueError):
            _harmonic_mean([-0.5, 1.0])

    def test_harmonic_mean_empty_raises(self):
        with pytest.raises(ValueError):
            _harmonic_mean([])

    def test_harmonic_mean_single_value(self):
        assert _harmonic_mean([0.5]) == pytest.approx(0.5)

    def test_harmonic_mean_below_threshold_if_weak(self):
        """Harmonic mean < PSI_THRESHOLD when one input is very weak (< 0.7).

        For H(a, 1.0, 1.0) < 0.888 we need a < 3/(0.888*3 - 2) ≈ 0.726.
        """
        weak = [0.5, 1.0, 1.0]
        assert _harmonic_mean(weak) < PSI_THRESHOLD


# ===========================================================================
# Class 3: GeometryDomain
# ===========================================================================


class TestGeometryDomain:
    """Tests for GeometryDomain."""

    @pytest.fixture
    def domain(self):
        return GeometryDomain(n_primes=30)

    def test_initialization(self, domain):
        assert domain.n_primes == 30
        assert len(domain.primes) == 30
        assert len(domain.log_primes) == 30

    def test_minimum_primes(self):
        """Should enforce minimum of 2 primes."""
        d = GeometryDomain(n_primes=1)
        assert d.n_primes >= 2

    def test_first_prime_is_2(self, domain):
        assert domain.primes[0] == 2

    def test_berry_phase_factor(self, domain):
        factor, _ = domain.berry_phase()
        assert factor == pytest.approx(BERRY_PHASE_FACTOR)
        assert factor == pytest.approx(7.0 / 8.0)

    def test_berry_phase_value(self, domain):
        _, value = domain.berry_phase()
        assert value == pytest.approx(7.0 / 8.0 * 2 * math.pi, rel=1e-10)

    def test_torus_eigenvalues_count(self, domain):
        eigs = domain.torus_eigenvalues(n_max=5)
        assert len(eigs) == 11  # -5 to 5 inclusive

    def test_torus_eigenvalues_spacing(self, domain):
        eigs = domain.torus_eigenvalues(n_max=5)
        expected_spacing = 2 * math.pi / domain.torus_length
        spacings = np.diff(eigs)
        assert np.allclose(spacings, expected_spacing, rtol=1e-10)

    def test_torus_eigenvalues_zero_mode(self, domain):
        eigs = domain.torus_eigenvalues(n_max=5)
        assert 0.0 in eigs

    def test_adelic_coherence_range(self, domain):
        c = domain.adelic_coherence()
        assert 0.0 <= c <= 1.0

    def test_compute_returns_result(self, domain):
        r = domain.compute()
        assert isinstance(r, GeometryResult)

    def test_psi_geom_range(self, domain):
        r = domain.compute()
        assert 0.0 <= r.psi_geom <= 1.0

    def test_psi_geom_above_threshold(self, domain):
        r = domain.compute()
        assert r.psi_geom >= PSI_THRESHOLD

    def test_berry_phase_factor_in_result(self, domain):
        r = domain.compute()
        assert r.berry_phase_factor == pytest.approx(BERRY_PHASE_FACTOR)

    def test_custom_torus_length(self):
        d = GeometryDomain(n_primes=10, torus_length=50.0)
        assert d.torus_length == pytest.approx(50.0)

    def test_n_primes_in_result(self, domain):
        r = domain.compute()
        assert r.n_primes == 30


# ===========================================================================
# Class 4: NumberTheoryDomain
# ===========================================================================


class TestNumberTheoryDomain:
    """Tests for NumberTheoryDomain (Weil formula)."""

    @pytest.fixture
    def domain(self):
        return NumberTheoryDomain(primes_upto=200)

    def test_initialization(self, domain):
        assert domain.primes_upto == 200
        assert len(domain.primes) > 0
        assert 2 in domain.primes

    def test_primes_upto_minimum(self):
        d = NumberTheoryDomain(primes_upto=5)
        assert d.primes_upto >= 5

    def test_center_is_first_zero(self, domain):
        assert domain._center == pytest.approx(_RIEMANN_ZEROS[0], rel=1e-6)

    def test_gaussian_phi_at_center(self, domain):
        """Φ(t₀) = 1 since it's centred there."""
        phi_at_center = domain._gaussian_phi(domain._center)
        assert phi_at_center == pytest.approx(1.0, rel=1e-10)

    def test_gaussian_phi_decays(self, domain):
        """Φ should decrease away from the centre."""
        phi_c = domain._gaussian_phi(domain._center)
        phi_far = domain._gaussian_phi(domain._center + 10 * domain.SIGMA)
        assert phi_far < phi_c

    def test_gaussian_phi_hat_at_zero(self, domain):
        """Φ̂(0) = σ/2π (max of the transform)."""
        phi_hat_0 = domain._gaussian_phi_hat(0.0)
        expected = domain.SIGMA / (2 * math.pi)
        assert phi_hat_0 == pytest.approx(expected, rel=1e-10)

    def test_weyl_measure_below_two_pi(self, domain):
        """μ(r) = 0 for r ≤ 2π."""
        assert domain._weyl_measure(1.0) == pytest.approx(0.0)
        assert domain._weyl_measure(2 * math.pi) == pytest.approx(0.0)

    def test_weyl_measure_increasing(self, domain):
        """μ(r) is monotonically increasing."""
        r1, r2 = 10.0, 50.0
        assert domain._weyl_measure(r1) < domain._weyl_measure(r2)

    def test_zero_sum_lhs_positive(self, domain):
        lhs = domain.zero_sum_lhs()
        assert lhs > 0

    def test_zero_sum_lhs_custom_zeros(self, domain):
        zeros = [14.1347, 21.022]
        lhs = domain.zero_sum_lhs(zeros=zeros)
        assert lhs > 0

    def test_compute_returns_result(self, domain):
        r = domain.compute()
        assert isinstance(r, NumberTheoryResult)

    def test_psi_nt_range(self, domain):
        r = domain.compute()
        assert 0.0 <= r.psi_nt <= 1.0

    def test_psi_nt_above_threshold(self, domain):
        r = domain.compute()
        assert r.psi_nt >= PSI_THRESHOLD

    def test_weil_discrepancy_bounded(self, domain):
        r = domain.compute()
        assert 0.0 <= r.weil_discrepancy <= 1.0

    def test_n_primes_used_in_result(self, domain):
        r = domain.compute()
        assert r.n_primes_used > 0


# ===========================================================================
# Class 5: QuantumDomain
# ===========================================================================


class TestQuantumDomain:
    """Tests for QuantumDomain (Berry-Keating + GUE)."""

    @pytest.fixture
    def domain(self):
        return QuantumDomain(N=50)

    def test_initialization(self, domain):
        assert domain.N == 50
        assert domain.f0 == pytest.approx(F_BASE)

    def test_minimum_N(self):
        d = QuantumDomain(N=5)
        assert d.N >= 10

    def test_build_berry_keating_shape(self, domain):
        H = domain._build_berry_keating()
        assert H.shape == (50, 50)

    def test_build_berry_keating_hermitian(self, domain):
        """Ĥ_BK must be Hermitian (self-adjoint)."""
        H = domain._build_berry_keating()
        error = float(np.linalg.norm(H - H.conj().T) / (np.linalg.norm(H) + 1e-15))
        assert error < 1e-10

    def test_build_resonance_shape(self, domain):
        H_res = domain._build_resonance()
        assert H_res.shape == (50, 50)

    def test_build_resonance_diagonal(self, domain):
        """Resonance coupling should be diagonal."""
        H_res = domain._build_resonance()
        off_diag = np.abs(H_res) - np.abs(np.diag(np.diag(H_res)))
        assert np.allclose(off_diag, 0.0)

    def test_psi_berry_keating_range(self, domain):
        psi_bk, _ = domain._psi_berry_keating()
        assert 0.0 <= psi_bk <= 1.0

    def test_psi_berry_keating_above_threshold(self, domain):
        psi_bk, _ = domain._psi_berry_keating()
        assert psi_bk >= PSI_THRESHOLD

    def test_psi_gue_range(self, domain):
        psi_gue, ks = domain._psi_gue()
        assert 0.0 <= psi_gue <= 1.0

    def test_psi_gue_above_threshold(self, domain):
        psi_gue, _ = domain._psi_gue()
        assert psi_gue >= PSI_THRESHOLD

    def test_ks_distance_nonneg(self, domain):
        _, ks = domain._psi_gue()
        assert ks >= 0.0

    def test_compute_returns_result(self, domain):
        r = domain.compute()
        assert isinstance(r, QuantumResult)

    def test_psi_quant_range(self, domain):
        r = domain.compute()
        assert 0.0 <= r.psi_quant <= 1.0

    def test_psi_quant_above_threshold(self, domain):
        r = domain.compute()
        assert r.psi_quant >= PSI_THRESHOLD

    def test_psi_quant_is_average(self, domain):
        """Ψ_quant should equal (Ψ_BK + Ψ_GUE) / 2."""
        r = domain.compute()
        expected = (r.psi_berry_keating + r.psi_gue) / 2.0
        assert r.psi_quant == pytest.approx(expected, rel=1e-10)

    def test_eigenvalue_count_positive(self, domain):
        r = domain.compute()
        assert r.eigenvalue_count >= 0


# ===========================================================================
# Class 6: ConscienceDomain
# ===========================================================================


class TestConscienceDomain:
    """Tests for ConscienceDomain (harmonic mean, threshold)."""

    @pytest.fixture
    def domain(self):
        return ConscienceDomain()

    def test_compute_returns_result(self, domain):
        r = domain.compute(0.95, 0.99, 0.96)
        assert isinstance(r, ConscienceResult)

    def test_harmonic_mean_is_harmonic(self, domain):
        """C should equal 3 / (1/a + 1/b + 1/c)."""
        a, b, c = 0.9, 0.95, 0.98
        r = domain.compute(a, b, c)
        expected = 3.0 / (1.0 / a + 1.0 / b + 1.0 / c)
        assert r.C == pytest.approx(expected, rel=1e-8)

    def test_coherent_above_threshold(self, domain):
        r = domain.compute(0.95, 0.99, 0.96)
        assert r.is_coherent is True
        assert r.C >= PSI_THRESHOLD

    def test_incoherent_below_threshold(self, domain):
        """If any input is far below threshold, C < PSI_THRESHOLD."""
        r = domain.compute(0.5, 0.99, 0.99)
        assert r.C < PSI_THRESHOLD
        assert r.is_coherent is False

    def test_equal_inputs_preserved(self, domain):
        """If all inputs equal x, harmonic mean = x."""
        x = 0.94
        r = domain.compute(x, x, x)
        assert r.C == pytest.approx(x, rel=1e-8)

    def test_c_leq_arithmetic_mean(self, domain):
        """H ≤ arithmetic mean."""
        a, b, c = 0.9, 0.95, 0.98
        r = domain.compute(a, b, c)
        am = (a + b + c) / 3.0
        assert r.C <= am + 1e-12

    def test_inputs_stored_in_result(self, domain):
        r = domain.compute(0.92, 0.97, 0.94)
        assert r.psi_geom_input == pytest.approx(0.92)
        assert r.psi_nt_input == pytest.approx(0.97)
        assert r.psi_quant_input == pytest.approx(0.94)

    def test_zero_input_handled(self, domain):
        """Zero input should be clamped to tiny positive value, not raise."""
        r = domain.compute(0.0, 0.99, 0.99)
        assert r.C >= 0.0

    def test_c_dominated_by_weakest_domain(self, domain):
        """Harmonic mean is dominated by smallest value."""
        r_weak = domain.compute(0.5, 1.0, 1.0)
        r_strong = domain.compute(0.99, 1.0, 1.0)
        assert r_weak.C < r_strong.C


# ===========================================================================
# Class 7: ConvergenciaTotal pipeline
# ===========================================================================


class TestConvergenciaTotal:
    """Tests for ConvergenciaTotal integrator."""

    @pytest.fixture
    def conv(self):
        return ConvergenciaTotal(
            n_primes_geom=20,
            primes_upto_nt=100,
            N_quantum=30,
            verbose=False,
        )

    @pytest.fixture
    def result(self, conv):
        return conv.ejecutar()

    def test_ejecutar_returns_result(self, result):
        assert isinstance(result, ConvergenciaResult)

    def test_psi_total_above_threshold(self, result):
        assert result.psi_total >= PSI_THRESHOLD

    def test_is_convergent(self, result):
        assert result.is_convergent is True

    def test_f_base(self, result):
        assert result.f_base == pytest.approx(F_BASE)

    def test_f_manifest(self, result):
        assert result.f_manifest == pytest.approx(F_MANIFEST)

    def test_harmonic_ratio(self, result):
        assert result.harmonic_ratio == pytest.approx(HARMONIC_RATIO, rel=1e-6)

    def test_ratio_vs_two_pi(self, result):
        """harmonic_ratio ≈ 2π → ratio_vs_two_pi ≈ 1."""
        assert result.ratio_vs_two_pi == pytest.approx(HARMONIC_RATIO / (2 * math.pi), rel=1e-6)

    def test_geometry_result_present(self, result):
        assert isinstance(result.geometry, GeometryResult)

    def test_number_theory_result_present(self, result):
        assert isinstance(result.number_theory, NumberTheoryResult)

    def test_quantum_result_present(self, result):
        assert isinstance(result.quantum, QuantumResult)

    def test_conscience_result_present(self, result):
        assert isinstance(result.conscience, ConscienceResult)

    def test_certificate_sha256_is_hex(self, result):
        """SHA-256 digest should be a 64-character hex string."""
        assert len(result.certificate_sha256) == 64
        int(result.certificate_sha256, 16)  # Should not raise

    def test_certificate_deterministic(self, conv):
        """Running twice with the same inputs must produce the same certificate."""
        r1 = conv.ejecutar()
        r2 = conv.ejecutar()
        assert r1.certificate_sha256 == r2.certificate_sha256

    def test_mensaje_final_present(self, result):
        assert len(result.mensaje_final) > 0

    def test_mensaje_final_contains_frequencies(self, result):
        """Message should mention both frequencies."""
        msg = result.mensaje_final
        assert str(F_BASE) in msg or "141" in msg
        assert str(F_MANIFEST) in msg or "888" in msg

    def test_psi_total_is_mean_of_four(self, result):
        """Ψ_total = (Ψ_geom + Ψ_nt + Ψ_quant + C) / 4."""
        expected = (
            result.geometry.psi_geom
            + result.number_theory.psi_nt
            + result.quantum.psi_quant
            + result.conscience.C
        ) / 4.0
        assert result.psi_total == pytest.approx(expected, rel=1e-8)


# ===========================================================================
# Class 8: SHA-256 certificate properties
# ===========================================================================


class TestCertificate:
    """Tests for certificate generation and determinism."""

    @pytest.fixture
    def make_cert(self):
        return ConvergenciaTotal._make_certificate

    def test_sha256_of_known_input(self, make_cert):
        payload = {"test": 1, "value": 2.0}
        sha = make_cert(payload)
        canonical = json.dumps(payload, sort_keys=True, default=str)
        expected = hashlib.sha256(canonical.encode()).hexdigest()
        assert sha == expected

    def test_sha256_different_payloads(self, make_cert):
        sha1 = make_cert({"a": 1})
        sha2 = make_cert({"a": 2})
        assert sha1 != sha2

    def test_sha256_sort_keys(self, make_cert):
        """Dict ordering must not affect the certificate."""
        sha1 = make_cert({"a": 1, "b": 2})
        sha2 = make_cert({"b": 2, "a": 1})
        assert sha1 == sha2

    def test_sha256_length_always_64(self, make_cert):
        for payload in [{}, {"x": 0}, {"long_key": "value" * 10}]:
            assert len(make_cert(payload)) == 64

    def test_certificate_from_run_is_reproducible(self):
        """Two ConvergenciaTotal runs with identical params → same SHA."""
        params = dict(n_primes_geom=20, primes_upto_nt=100, N_quantum=30, verbose=False)
        r1 = ConvergenciaTotal(**params).ejecutar()
        r2 = ConvergenciaTotal(**params).ejecutar()
        assert r1.certificate_sha256 == r2.certificate_sha256


# ===========================================================================
# Class 9: Mathematical properties
# ===========================================================================


class TestMathematicalProperties:
    """Core mathematical property tests."""

    def test_berry_phase_topological_invariant(self):
        """Berry phase factor 7/8 is exact, not fitted."""
        assert BERRY_PHASE_FACTOR == 7.0 / 8.0
        # Should survive float round-trip
        assert float(BERRY_PHASE_FACTOR) == 0.875

    def test_harmonic_ratio_two_pi_proximity(self):
        """f_manifest / f_base ≈ 2π within 1%."""
        ratio = F_MANIFEST / F_BASE
        two_pi = 2 * math.pi
        assert abs(ratio - two_pi) / two_pi < 0.01

    def test_harmonic_mean_upper_bound_by_arith(self):
        """H(a,b,c) ≤ (a+b+c)/3 always."""
        for vals in [
            [0.9, 0.95, 0.98],
            [0.8, 0.99, 0.95],
            [0.5, 0.7, 0.9],
        ]:
            hm = _harmonic_mean(vals)
            am = sum(vals) / len(vals)
            assert hm <= am + 1e-10

    def test_weil_lhs_positive(self):
        """Σ_n Φ(t_n) should be positive for a Gaussian test function."""
        nt = NumberTheoryDomain(primes_upto=50)
        lhs = nt.zero_sum_lhs()
        assert lhs > 0

    def test_gue_wigner_surmise_property(self):
        """Wigner surmise CDF should be monotone and range [0,1]."""
        zeros = np.array(_RIEMANN_ZEROS)
        spacings = np.diff(np.sort(zeros))
        mean_sp = float(np.mean(spacings))
        s_sorted = np.sort(spacings / mean_sp)
        wigner_cdf = 1.0 - np.exp(-np.pi * s_sorted ** 2 / 4.0)
        assert np.all(wigner_cdf >= 0.0)
        assert np.all(wigner_cdf <= 1.0)
        assert np.all(np.diff(wigner_cdf) >= -1e-12)

    def test_total_coherence_is_mean_of_four(self):
        """Ψ_total = arithmetic mean of four domain coherences."""
        r = ConvergenciaTotal(
            n_primes_geom=15, primes_upto_nt=50, N_quantum=20, verbose=False
        ).ejecutar()
        expected = (
            r.geometry.psi_geom
            + r.number_theory.psi_nt
            + r.quantum.psi_quant
            + r.conscience.C
        ) / 4.0
        assert r.psi_total == pytest.approx(expected, rel=1e-8)

    def test_conscience_is_harmonic_mean_of_three(self):
        """C = harmonic_mean(Ψ_geom, Ψ_nt, Ψ_quant)."""
        r = ConvergenciaTotal(
            n_primes_geom=15, primes_upto_nt=50, N_quantum=20, verbose=False
        ).ejecutar()
        expected = _harmonic_mean([
            max(r.geometry.psi_geom, 1e-15),
            max(r.number_theory.psi_nt, 1e-15),
            max(r.quantum.psi_quant, 1e-15),
        ])
        assert r.conscience.C == pytest.approx(expected, rel=1e-6)

    def test_all_domains_above_zero(self):
        r = ConvergenciaTotal(
            n_primes_geom=15, primes_upto_nt=50, N_quantum=20, verbose=False
        ).ejecutar()
        assert r.geometry.psi_geom > 0
        assert r.number_theory.psi_nt > 0
        assert r.quantum.psi_quant > 0
        assert r.conscience.C > 0


# ===========================================================================
# Class 10: demostrar_convergencia convenience function + edge cases
# ===========================================================================


class TestDemostrarConvergencia:
    """Tests for the demostrar_convergencia wrapper and edge cases."""

    def test_returns_convergencia_result(self):
        r = demostrar_convergencia(
            n_primes_geom=10, primes_upto_nt=30, N_quantum=15, verbose=False
        )
        assert isinstance(r, ConvergenciaResult)

    def test_above_psi_threshold(self):
        r = demostrar_convergencia(
            n_primes_geom=10, primes_upto_nt=30, N_quantum=15, verbose=False
        )
        assert r.psi_total >= PSI_THRESHOLD

    def test_is_convergent(self):
        r = demostrar_convergencia(
            n_primes_geom=10, primes_upto_nt=30, N_quantum=15, verbose=False
        )
        assert r.is_convergent is True

    def test_mensaje_hecho_esta(self):
        r = demostrar_convergencia(
            n_primes_geom=10, primes_upto_nt=30, N_quantum=15, verbose=False
        )
        assert "HECHO ESTÁ" in r.mensaje_final or "141" in r.mensaje_final

    def test_default_parameters(self):
        """Default ConvergenciaTotal should converge."""
        r = ConvergenciaTotal(verbose=False).ejecutar()
        assert r.is_convergent is True

    def test_large_primes_geom(self):
        d = GeometryDomain(n_primes=50)
        r = d.compute()
        assert r.psi_geom >= 0.0

    def test_many_primes_nt(self):
        d = NumberTheoryDomain(primes_upto=300)
        r = d.compute()
        assert r.psi_nt >= 0.0

    def test_large_quantum_N(self):
        d = QuantumDomain(N=200)
        r = d.compute()
        assert r.psi_quant >= 0.0

    def test_geometry_deterministic(self):
        """Same GeometryDomain should give same result."""
        d = GeometryDomain(n_primes=20)
        r1 = d.compute()
        r2 = d.compute()
        assert r1.psi_geom == pytest.approx(r2.psi_geom)

    def test_number_theory_deterministic(self):
        d = NumberTheoryDomain(primes_upto=100)
        r1 = d.compute()
        r2 = d.compute()
        assert r1.psi_nt == pytest.approx(r2.psi_nt)

    def test_quantum_deterministic(self):
        d = QuantumDomain(N=40)
        r1 = d.compute()
        r2 = d.compute()
        assert r1.psi_quant == pytest.approx(r2.psi_quant)
