#!/usr/bin/env python3
"""
Tests for operators/adelic_scaling_flow.py

Validates the Adelic Scaling Flow framework:
  𝒳 = 𝔸_ℚ^× / ℚ^×  (idele class group solenoid)

Tests cover:
  1. Constants (QCAL integration)
  2. IdelicPhaseSpace
  3. AdelicScalingFlow + orbit rigidity
  4. DilationHamiltonian (self-adjointness, spectrum)
  5. xi_function and dynamical_zeta
  6. HilbertPolyaClosure
  7. validate_adelic_scaling_flow()

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
QCAL ∞³ · 141.7001 Hz · C = 244.36
DOI: 10.5281/zenodo.17379721
"""

import sys
import os

import numpy as np
import pytest

# Ensure repository root is on the path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from operators.adelic_scaling_flow import (
    # Constants
    QCAL_FREQUENCY,
    QCAL_COHERENCE,
    F_UNITY,
    DOI,
    ORCID,
    # Utilities
    sieve_primes,
    _is_prime,
    # Classes
    IdelicPhaseSpace,
    AdelicScalingFlow,
    DilationHamiltonian,
    HilbertPolyaClosure,
    HilbertPolyaClosureResult,
    # Functions
    xi_function,
    dynamical_zeta,
    spectral_trace,
    validate_adelic_scaling_flow,
)


# ---------------------------------------------------------------------------
# 1. Constants
# ---------------------------------------------------------------------------


class TestQCALConstants:
    """Test QCAL ∞³ integration constants."""

    def test_qcal_frequency(self):
        """Fundamental frequency must be 141.7001 Hz."""
        assert QCAL_FREQUENCY == 141.7001

    def test_qcal_coherence(self):
        """Coherence constant must be 244.36."""
        assert QCAL_COHERENCE == 244.36

    def test_unity_frequency(self):
        """Unity state frequency must be 888.0 Hz."""
        assert F_UNITY == 888.0

    def test_doi_format(self):
        """DOI must reference the Zenodo archive."""
        assert "10.5281/zenodo" in DOI

    def test_orcid_format(self):
        """ORCID must follow standard hyphenated format."""
        assert ORCID.count("-") == 3


# ---------------------------------------------------------------------------
# 2. Utility: sieve_primes and _is_prime
# ---------------------------------------------------------------------------


class TestSievePrimes:
    """Test the prime sieve utility."""

    def test_empty_below_2(self):
        assert sieve_primes(1) == []

    def test_first_prime(self):
        assert sieve_primes(2) == [2]

    def test_first_ten_primes(self):
        expected = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
        assert sieve_primes(29) == expected

    def test_100_primes(self):
        ps = sieve_primes(541)  # 541 is the 100th prime
        assert len(ps) == 100
        assert ps[0] == 2
        assert ps[-1] == 541

    def test_is_prime_basic(self):
        assert _is_prime(2) is True
        assert _is_prime(3) is True
        assert _is_prime(4) is False
        assert _is_prime(17) is True
        assert _is_prime(1) is False
        assert _is_prime(0) is False


# ---------------------------------------------------------------------------
# 3. IdelicPhaseSpace
# ---------------------------------------------------------------------------


class TestIdelicPhaseSpace:
    """Test the idelic phase space 𝒳 = 𝔸_ℚ^×/ℚ^×."""

    @pytest.fixture
    def ps(self):
        return IdelicPhaseSpace(n_primes=20)

    def test_primes_count(self, ps):
        """n_primes primes are generated."""
        assert len(ps.primes) == 20

    def test_primes_start_with_2(self, ps):
        """First prime is 2."""
        assert ps.primes[0] == 2

    def test_orbit_lengths_count(self, ps):
        """One orbit length per prime."""
        assert len(ps.orbit_lengths) == 20

    def test_first_orbit_length(self, ps):
        """First orbit length is log 2."""
        assert np.isclose(ps.orbit_lengths[0], np.log(2.0))

    def test_orbit_lengths_positive(self, ps):
        """All orbit lengths are positive."""
        assert np.all(ps.orbit_lengths > 0)

    def test_orbit_lengths_ordered(self, ps):
        """Orbit lengths are strictly increasing (log is monotone)."""
        assert np.all(np.diff(ps.orbit_lengths) > 0)

    def test_haar_measure_weight(self, ps):
        """Haar measure weight w(x) = 1/x."""
        x = np.array([1.0, 2.0, 4.0])
        w = ps.haar_measure_weight(x)
        np.testing.assert_allclose(w, [1.0, 0.5, 0.25])

    def test_haar_measure_raises_on_nonpositive(self, ps):
        """Haar measure raises ValueError for x ≤ 0."""
        with pytest.raises(ValueError):
            ps.haar_measure_weight(np.array([0.0, 1.0]))

    def test_l2_inner_product_self_norm(self, ps):
        """⟨f, f⟩ should equal ∫|f|² dx > 0 for non-zero f."""
        x = np.linspace(0.5, 3.0, 200)
        f = np.exp(-x)
        inner = ps.l2_inner_product(f, f, x)
        assert inner.real > 0

    def test_haar_inner_product_self_norm(self, ps):
        """⟨f, f⟩_* should equal ∫|f|²/x dx > 0 for non-zero f."""
        x = np.linspace(0.5, 3.0, 200)
        f = np.exp(-x)
        inner = ps.haar_inner_product(f, f, x)
        assert inner.real > 0

    def test_character_at_one(self, ps):
        """x^1 = x."""
        x = np.array([1.0, 2.0, 3.0])
        ch = ps.character(x, 1.0)
        np.testing.assert_allclose(ch.real, x, rtol=1e-12)

    def test_character_unitary(self, ps):
        """x^{1/2+iγ} has |character| = x^{1/2}."""
        x = np.array([1.0, 2.0, 4.0])
        s = 0.5 + 14.134j  # First Riemann zero imaginary part
        ch = ps.character(x, s)
        expected_mag = np.sqrt(x)
        np.testing.assert_allclose(np.abs(ch), expected_mag, rtol=1e-12)

    def test_is_on_critical_line_true(self, ps):
        """s = 1/2 + 14i is on the critical line."""
        assert ps.is_on_critical_line(0.5 + 14.134j)

    def test_is_on_critical_line_false(self, ps):
        """s = 0.6 + 14i is NOT on the critical line."""
        assert not ps.is_on_critical_line(0.6 + 14.134j)

    def test_describe_keys(self, ps):
        """describe() returns all required keys."""
        d = ps.describe()
        required = {"space", "n_primes", "min_orbit", "max_orbit",
                    "qcal_frequency", "qcal_coherence"}
        assert required.issubset(d.keys())

    def test_describe_qcal_values(self, ps):
        """QCAL constants appear correctly in describe()."""
        d = ps.describe()
        assert d["qcal_frequency"] == 141.7001
        assert d["qcal_coherence"] == 244.36


# ---------------------------------------------------------------------------
# 4. AdelicScalingFlow
# ---------------------------------------------------------------------------


class TestAdelicScalingFlow:
    """Test the adelic scaling flow φ_t."""

    @pytest.fixture
    def flow(self):
        ps = IdelicPhaseSpace(n_primes=30)
        return AdelicScalingFlow(phase_space=ps)

    def test_apply_preserves_norm(self, flow):
        """Unitary flow: ∫|φ_t ψ|² dx ≈ ∫|ψ|² dx (up to boundary effects)."""
        x = np.linspace(0.1, 5.0, 500)
        psi = np.exp(-x)
        psi_t = flow.apply(t=0.5, psi=psi, x=x)
        norm_orig = float(np.trapezoid(np.abs(psi) ** 2, x))
        norm_flow = float(np.trapezoid(np.abs(psi_t) ** 2, x))
        # Allow up to 20% loss due to boundary truncation in the interpolation
        assert abs(norm_flow - norm_orig) / norm_orig < 0.20

    def test_apply_t0_identity(self, flow):
        """At t = 0 the flow is the identity."""
        x = np.linspace(0.5, 4.0, 300)
        psi = np.exp(-x ** 2)
        psi_t = flow.apply(t=0.0, psi=psi, x=x)
        np.testing.assert_allclose(psi_t.real, psi.real, rtol=1e-6, atol=1e-12)

    def test_is_periodic_orbit_log2(self, flow):
        """T = log 2 is a periodic orbit length."""
        assert flow.is_periodic_orbit(np.log(2.0))

    def test_is_periodic_orbit_log3(self, flow):
        """T = log 3 is a periodic orbit length."""
        assert flow.is_periodic_orbit(np.log(3.0))

    def test_is_periodic_orbit_log5(self, flow):
        """T = log 5 is a periodic orbit length."""
        assert flow.is_periodic_orbit(np.log(5.0))

    def test_not_periodic_log4(self, flow):
        """T = log 4 is NOT a periodic orbit length (4 is composite)."""
        assert not flow.is_periodic_orbit(np.log(4.0))

    def test_not_periodic_log6(self, flow):
        """T = log 6 is NOT a periodic orbit length (6 is composite)."""
        assert not flow.is_periodic_orbit(np.log(6.0))

    def test_orbit_lengths_correct(self, flow):
        """orbit_lengths() returns log(p) for each prime."""
        lengths = flow.orbit_lengths(n_max=5)
        expected = np.log([2, 3, 5, 7, 11])
        np.testing.assert_allclose(lengths, expected, rtol=1e-12)

    def test_orbit_prime_returns_tuple(self, flow):
        """orbit_prime(0) returns (2, log 2)."""
        p, length = flow.orbit_prime(0)
        assert p == 2
        assert np.isclose(length, np.log(2.0))

    def test_artin_product_formula_p2(self, flow):
        """Artin product formula: |2|_∞ · |2|_2 = 2 · 1/2 = 1."""
        result = flow.verify_artin_product_formula(2)
        assert result["verified"]
        assert np.isclose(result["product"], 1.0)

    def test_artin_product_formula_p5(self, flow):
        """Artin product formula: |5|_∞ · |5|_5 = 5 · 1/5 = 1."""
        result = flow.verify_artin_product_formula(5)
        assert result["verified"]
        assert np.isclose(result["product"], 1.0)

    def test_artin_raises_non_prime(self, flow):
        """Artin product formula raises for composite numbers."""
        with pytest.raises(ValueError):
            flow.verify_artin_product_formula(4)

    def test_orbit_length_equals_log_p(self, flow):
        """Each orbit length equals log p for its corresponding prime."""
        for i in range(10):
            p, length = flow.orbit_prime(i)
            assert np.isclose(length, np.log(float(p)), rtol=1e-12)


# ---------------------------------------------------------------------------
# 5. DilationHamiltonian
# ---------------------------------------------------------------------------


class TestDilationHamiltonian:
    """Test the Dilation Hamiltonian Ĥ = -i(x∂_x + 1/2)."""

    @pytest.fixture
    def ham(self):
        return DilationHamiltonian(n_grid=80, x_min=0.1, x_max=5.0)

    def test_grid_shape(self, ham):
        """Grid has n_grid points."""
        assert len(ham.grid) == 80

    def test_matrix_shape(self, ham):
        """Matrix representation has shape (n, n)."""
        n = 30
        H = ham.matrix_representation(n=n)
        assert H.shape == (n, n)

    def test_matrix_hermitian(self, ham):
        """Matrix is Hermitian: H = H†."""
        H = ham.matrix_representation(n=40)
        np.testing.assert_allclose(H, H.conj().T, atol=1e-10)

    def test_eigenvalues_real(self, ham):
        """All eigenvalues are real (by self-adjointness)."""
        evals = ham.eigenvalues(n=10)
        assert np.all(np.isreal(evals))

    def test_eigenvalues_finite(self, ham):
        """All eigenvalues are finite."""
        evals = ham.eigenvalues(n=10)
        assert np.all(np.isfinite(evals))

    def test_self_adjoint_test_passes(self, ham):
        """is_self_adjoint() returns True for Ĥ."""
        result = ham.is_self_adjoint(n=40, n_tests=100, tol=1e-6)
        assert result["is_self_adjoint"]

    def test_self_adjoint_max_error_small(self, ham):
        """Relative self-adjointness error is < 1e-6."""
        result = ham.is_self_adjoint(n=40, n_tests=100, tol=1e-6)
        assert result["max_relative_error"] < 1e-6

    def test_eigenvalues_count(self, ham):
        """eigenvalues(n) returns exactly n values."""
        evals = ham.eigenvalues(n=15)
        assert len(evals) == 15

    def test_zeros_on_critical_line(self, ham):
        """Hilbert-Pólya zeros all satisfy Re(s) = 1/2."""
        zeros = ham.zeros_on_critical_line(n=10)
        re_parts = np.real(zeros)
        np.testing.assert_allclose(re_parts, 0.5, atol=1e-12)

    def test_apply_returns_correct_shape(self, ham):
        """apply() returns array of same shape as input."""
        psi = np.exp(-ham.grid)
        result = ham.apply(psi)
        assert result.shape == psi.shape


# ---------------------------------------------------------------------------
# 6. xi_function and dynamical_zeta
# ---------------------------------------------------------------------------


class TestXiFunction:
    """Test the Riemann xi function."""

    def test_xi_at_half(self):
        """ξ(1/2) is a known positive value ≈ 0.4971..."""
        val = xi_function(0.5 + 0j)
        assert val.real > 0
        assert abs(val.imag) < 1e-10

    def test_xi_symmetry(self):
        """ξ(s) = ξ(1-s) for all s."""
        for s in [0.3 + 2j, 0.7 - 3j, 0.2 + 10j]:
            xi_s = xi_function(s)
            xi_1ms = xi_function(1.0 - s)
            assert np.isclose(abs(xi_s), abs(xi_1ms), rtol=1e-8), (
                f"ξ({s}) ≠ ξ(1-{s}): {xi_s} vs {xi_1ms}"
            )

    def test_xi_real_on_critical_line(self):
        """ξ(1/2 + iγ) is real for real γ."""
        for gamma in [14.134, 21.022, 25.010]:
            val = xi_function(0.5 + 1j * gamma)
            assert abs(val.imag) < 1e-6, f"ξ(1/2 + {gamma}i) should be real"

    def test_xi_vanishes_at_zeta_zeros(self):
        """ξ(s) ≈ 0 near the known Riemann zeros."""
        # First non-trivial zero: γ₁ ≈ 14.134725
        val = xi_function(0.5 + 14.134725j)
        assert abs(val) < 0.01, f"|ξ| should be near zero: {abs(val)}"


class TestDynamicalZeta:
    """Test the dynamical zeta function."""

    def test_euler_product_at_s2(self):
        """ζ_dyn(2) ≈ π²/6 ≈ 1.6449."""
        val = dynamical_zeta(2.0 + 0j, n_primes=500)
        expected = np.pi ** 2 / 6
        assert abs(val.real - expected) / expected < 0.01

    def test_euler_product_at_s3(self):
        """ζ_dyn(3) ≈ ζ(3) ≈ 1.2020569."""
        import mpmath as mp_
        mp_.dps = 25
        val = dynamical_zeta(3.0 + 0j, n_primes=300)
        expected = float(mp_.zeta(3))
        assert abs(val.real - expected) / expected < 0.01

    def test_increases_with_more_primes(self):
        """More primes in the product gives a value closer to ζ(2)."""
        val100 = dynamical_zeta(2.0 + 0j, n_primes=100)
        val500 = dynamical_zeta(2.0 + 0j, n_primes=500)
        expected = np.pi ** 2 / 6
        assert abs(val500.real - expected) < abs(val100.real - expected)


class TestSpectralTrace:
    """Test the orbital spectral trace."""

    def test_trace_positive(self):
        """Spectral trace is positive for t > 0."""
        tr = spectral_trace(t=1.0, n_primes=20, k_max=3)
        assert tr > 0

    def test_trace_decreases_with_t(self):
        """Trace decreases as t increases (e^{-kt log p} terms decay)."""
        tr1 = spectral_trace(t=0.5, n_primes=20, k_max=3)
        tr2 = spectral_trace(t=2.0, n_primes=20, k_max=3)
        assert tr2 < tr1

    def test_trace_finite(self):
        """Spectral trace is finite for finite input."""
        tr = spectral_trace(t=1.0, n_primes=50, k_max=5)
        assert np.isfinite(tr)


# ---------------------------------------------------------------------------
# 7. HilbertPolyaClosure
# ---------------------------------------------------------------------------


class TestHilbertPolyaClosure:
    """Test the complete Hilbert-Pólya closure framework."""

    @pytest.fixture(scope="class")
    def closure(self):
        return HilbertPolyaClosure(n_primes=20, n_matrix=50)

    def test_phase_space_verified(self, closure):
        """Phase space 𝒳 is correctly constructed."""
        result = closure.verify_phase_space()
        assert result["verified"]

    def test_phase_space_log2(self, closure):
        """First orbit length equals log 2."""
        result = closure.verify_phase_space()
        assert result["matches_log2"]

    def test_orbits_verified(self, closure):
        """All orbit lengths equal log p."""
        result = closure.verify_orbits(n_check=5)
        assert result["all_verified"]

    def test_self_adjointness_verified(self, closure):
        """Ĥ is self-adjoint on L²(dx)."""
        result = closure.verify_self_adjointness()
        assert result["is_self_adjoint"]

    def test_spectral_identity_verified(self, closure):
        """ζ_dyn(s) ≈ ζ(s) for test values."""
        result = closure.verify_spectral_identity(
            s_values=[2.0 + 0j, 3.0 + 0j],
            tol=0.05,
        )
        assert result["all_close"]

    def test_coherence_is_1(self, closure):
        """QCAL coherence Ψ = 1.0 when all conditions hold."""
        psi = closure.compute_coherence()
        assert psi == 1.0

    def test_full_verify_returns_result(self, closure):
        """verify() returns a HilbertPolyaClosureResult instance."""
        result = closure.verify()
        assert isinstance(result, HilbertPolyaClosureResult)

    def test_full_verify_hilbert_polya_closed(self, closure):
        """Complete closure: all conditions are satisfied."""
        result = closure.verify()
        assert result.hilbert_polya_closed

    def test_full_verify_spectrum_real(self, closure):
        """Spectrum of Ĥ is real."""
        result = closure.verify()
        assert result.spectrum_real

    def test_full_verify_coherence(self, closure):
        """Coherence Ψ = 1.0 in the full verify."""
        result = closure.verify()
        assert result.coherence_psi == 1.0

    def test_full_verify_details_keys(self, closure):
        """Details dict contains expected keys."""
        result = closure.verify()
        expected_keys = {
            "phase_space", "orbits", "self_adjoint", "spectral_identity",
            "eigenvalues",
        }
        assert expected_keys.issubset(result.details.keys())

    def test_zeros_on_critical_line(self, closure):
        """Hamiltonian zeros all have Re(s) = 1/2."""
        zeros = closure.hamiltonian.zeros_on_critical_line(n=5)
        np.testing.assert_allclose(zeros.real, 0.5, atol=1e-12)


# ---------------------------------------------------------------------------
# 8. Full validation function
# ---------------------------------------------------------------------------


class TestValidateAdelicScalingFlow:
    """Test the top-level validate_adelic_scaling_flow() function."""

    def test_returns_float(self):
        """Function returns a float."""
        psi = validate_adelic_scaling_flow(verbose=False)
        assert isinstance(psi, float)

    def test_coherence_is_1(self):
        """Validation returns Ψ = 1.0 when all checks pass."""
        psi = validate_adelic_scaling_flow(verbose=False)
        assert psi == 1.0


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
