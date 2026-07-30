#!/usr/bin/env python3
"""
Tests for operators/idele_class_flow.py

Validates the Idele Class Flow framework:
  C_ℚ = 𝔸_ℚ^×/ℚ^×  (idele class group)

Tests cover:
  1. Constants (QCAL integration)
  2. Utility functions (_sieve, _is_prime)
  3. IdeleClassFlow instantiation
  4. Orbit lengths and orbit_length()
  5. Artin product formula
  6. Orbit rigidity theorem
  7. Spectral determinant Δ(s) = 1/ζ(s)
  8. Generator T = -ix∂_x (self-adjointness)
  9. validate() / validate_idele_class_flow()

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
QCAL ∞³ · 141.7001 Hz · C = 244.36
DOI: 10.5281/zenodo.17379721
"""

import sys
import os

import numpy as np
import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from operators.idele_class_flow import (
    # Constants
    QCAL_FREQUENCY,
    QCAL_COHERENCE,
    DOI,
    ORCID,
    # Utilities
    _sieve,
    _is_prime,
    # Main class and data
    IdeleClassFlow,
    OrbitData,
    # Functions
    validate_idele_class_flow,
)


# ---------------------------------------------------------------------------
# 1. Constants
# ---------------------------------------------------------------------------


class TestQCALConstants:
    """Verify QCAL ∞³ integration constants."""

    def test_frequency(self):
        """QCAL fundamental frequency must be 141.7001 Hz."""
        assert QCAL_FREQUENCY == 141.7001

    def test_coherence(self):
        """Coherence constant must be 244.36."""
        assert QCAL_COHERENCE == 244.36

    def test_doi(self):
        """DOI must reference the Zenodo archive."""
        assert "10.5281/zenodo" in DOI

    def test_orcid(self):
        """ORCID must have standard hyphenated format."""
        assert ORCID.count("-") == 3


# ---------------------------------------------------------------------------
# 2. Utility: _sieve and _is_prime
# ---------------------------------------------------------------------------


class TestSieve:
    """Test the prime sieve utility."""

    def test_empty_below_2(self):
        assert _sieve(1) == []

    def test_first_prime_only(self):
        assert _sieve(2) == [2]

    def test_primes_up_to_30(self):
        expected = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
        assert _sieve(29) == expected

    def test_100th_prime(self):
        ps = _sieve(541)
        assert len(ps) == 100
        assert ps[-1] == 541


class TestIsPrime:
    """Test the primality test."""

    def test_0_not_prime(self):
        assert not _is_prime(0)

    def test_1_not_prime(self):
        assert not _is_prime(1)

    def test_2_prime(self):
        assert _is_prime(2)

    def test_3_prime(self):
        assert _is_prime(3)

    def test_4_not_prime(self):
        assert not _is_prime(4)

    def test_17_prime(self):
        assert _is_prime(17)

    def test_100_not_prime(self):
        assert not _is_prime(100)

    def test_541_prime(self):
        assert _is_prime(541)


# ---------------------------------------------------------------------------
# 3. IdeleClassFlow: instantiation
# ---------------------------------------------------------------------------


class TestIdeleClassFlowInit:
    """Test IdeleClassFlow construction."""

    def test_default_n_primes(self):
        flow = IdeleClassFlow(n_primes=10)
        assert flow.n_primes == 10

    def test_primes_count(self):
        flow = IdeleClassFlow(n_primes=10)
        assert len(flow.primes) == 10

    def test_primes_start_with_2(self):
        flow = IdeleClassFlow(n_primes=5)
        assert flow.primes[0] == 2

    def test_primes_are_prime(self):
        flow = IdeleClassFlow(n_primes=20)
        for p in flow.primes:
            assert _is_prime(p), f"{p} is not prime"

    def test_orbit_lengths_positive(self):
        flow = IdeleClassFlow(n_primes=10)
        assert np.all(flow.all_orbit_lengths() > 0)

    def test_orbit_lengths_monotone(self):
        flow = IdeleClassFlow(n_primes=20)
        L = flow.all_orbit_lengths()
        assert np.all(np.diff(L) > 0)


# ---------------------------------------------------------------------------
# 4. Orbit lengths
# ---------------------------------------------------------------------------


class TestOrbitLength:
    """Test orbit_length() and all_orbit_lengths()."""

    @pytest.fixture
    def flow(self):
        return IdeleClassFlow(n_primes=30)

    def test_orbit_length_2(self, flow):
        """ℓ_γ(2) = log 2."""
        assert np.isclose(flow.orbit_length(2), np.log(2))

    def test_orbit_length_3(self, flow):
        """ℓ_γ(3) = log 3."""
        assert np.isclose(flow.orbit_length(3), np.log(3))

    def test_orbit_length_5(self, flow):
        """ℓ_γ(5) = log 5."""
        assert np.isclose(flow.orbit_length(5), np.log(5))

    def test_orbit_length_101(self, flow):
        """ℓ_γ(101) = log 101."""
        assert np.isclose(flow.orbit_length(101), np.log(101))

    def test_orbit_length_raises_composite(self, flow):
        """orbit_length raises ValueError for composite input."""
        with pytest.raises(ValueError):
            flow.orbit_length(4)

    def test_orbit_length_raises_1(self, flow):
        """orbit_length raises ValueError for 1."""
        with pytest.raises(ValueError):
            flow.orbit_length(1)

    def test_all_lengths_equal_log_p(self, flow):
        """all_orbit_lengths() == [log p for p in primes]."""
        expected = np.log(np.array(flow.primes, dtype=float))
        np.testing.assert_allclose(flow.all_orbit_lengths(), expected, rtol=1e-12)

    def test_all_lengths_first_is_log2(self, flow):
        """First orbit length is log 2."""
        assert np.isclose(flow.all_orbit_lengths()[0], np.log(2))

    def test_orbit_length_positive(self, flow):
        """All orbit lengths are positive."""
        L = flow.all_orbit_lengths()
        assert np.all(L > 0)


# ---------------------------------------------------------------------------
# 5. Artin product formula
# ---------------------------------------------------------------------------


class TestArtinProductFormula:
    """Test the Artin product formula ∏_v |p|_v = 1."""

    @pytest.fixture
    def flow(self):
        return IdeleClassFlow(n_primes=30)

    def test_artin_returns_orbit_data(self, flow):
        """artin_product_formula() returns an OrbitData instance."""
        od = flow.artin_product_formula(2)
        assert isinstance(od, OrbitData)

    def test_artin_p2(self, flow):
        """Artin product formula holds for p = 2."""
        od = flow.artin_product_formula(2)
        assert od.verified
        assert np.isclose(od.artin_product, 1.0)
        assert od.prime == 2

    def test_artin_p3(self, flow):
        """Artin product formula holds for p = 3."""
        od = flow.artin_product_formula(3)
        assert od.verified
        assert np.isclose(od.artin_product, 1.0)

    def test_artin_p5(self, flow):
        """Artin product formula holds for p = 5."""
        od = flow.artin_product_formula(5)
        assert od.verified

    def test_artin_p7(self, flow):
        """Artin product formula holds for p = 7."""
        od = flow.artin_product_formula(7)
        assert od.verified

    def test_artin_p541(self, flow):
        """Artin product formula holds for p = 541 (100th prime)."""
        od = flow.artin_product_formula(541)
        assert od.verified
        assert np.isclose(od.artin_product, 1.0)

    def test_artin_archimedean_norm_p(self, flow):
        """Archimedean norm |p|_∞ = p."""
        for p in [2, 3, 5, 7, 11]:
            od = flow.artin_product_formula(p)
            assert np.isclose(od.archimedean_norm, float(p))

    def test_artin_p_adic_norm(self, flow):
        """p-adic norm |p|_p = 1/p."""
        for p in [2, 3, 5, 7, 11]:
            od = flow.artin_product_formula(p)
            assert np.isclose(od.p_adic_norm, 1.0 / float(p))

    def test_artin_orbit_length(self, flow):
        """Orbit length from Artin data equals log p."""
        for p in [2, 3, 5, 7]:
            od = flow.artin_product_formula(p)
            assert np.isclose(od.length, np.log(float(p)))

    def test_artin_raises_composite(self, flow):
        """artin_product_formula raises ValueError for composite input."""
        with pytest.raises(ValueError):
            flow.artin_product_formula(6)

    def test_artin_raises_zero(self, flow):
        """artin_product_formula raises ValueError for 0."""
        with pytest.raises(ValueError):
            flow.artin_product_formula(0)


# ---------------------------------------------------------------------------
# 6. Orbit rigidity theorem
# ---------------------------------------------------------------------------


class TestOrbitRigidity:
    """Test verify_orbit_rigidity()."""

    @pytest.fixture
    def flow(self):
        return IdeleClassFlow(n_primes=20)

    def test_rigidity_all_verified(self, flow):
        """All 10 orbits are verified."""
        result = flow.verify_orbit_rigidity(n_check=10)
        assert result["all_verified"]

    def test_rigidity_no_ghost_orbits(self, flow):
        """No ghost orbits exist."""
        result = flow.verify_orbit_rigidity(n_check=10)
        assert result["no_ghost_orbits"]

    def test_rigidity_n_checked(self, flow):
        """Number of checked orbits matches request."""
        result = flow.verify_orbit_rigidity(n_check=5)
        assert result["n_checked"] == 5

    def test_rigidity_orbit_data_length(self, flow):
        """orbit_data has correct length."""
        result = flow.verify_orbit_rigidity(n_check=8)
        assert len(result["orbit_data"]) == 8

    def test_rigidity_each_orbit_verified(self, flow):
        """Each individual orbit is verified."""
        result = flow.verify_orbit_rigidity(n_check=10)
        for od in result["orbit_data"]:
            assert od.verified, f"Prime {od.prime} orbit not verified"


# ---------------------------------------------------------------------------
# 7. Spectral determinant Δ(s) = 1/ζ(s)
# ---------------------------------------------------------------------------


class TestSpectralDeterminant:
    """Test the spectral determinant Δ(s) = ∏_p (1 - p^{-s})."""

    @pytest.fixture
    def flow(self):
        return IdeleClassFlow(n_primes=200)

    def test_det_at_s2(self, flow):
        """Δ(2)^{-1} ≈ π²/6 ≈ 1.6449."""
        inv_det = flow.inverse_spectral_determinant(2.0 + 0j)
        expected = np.pi ** 2 / 6
        assert abs(inv_det.real - expected) / expected < 0.001

    def test_det_at_s3(self, flow):
        """Δ(3)^{-1} ≈ ζ(3) ≈ 1.2021."""
        import mpmath as mp_
        mp_.dps = 25
        inv_det = flow.inverse_spectral_determinant(3.0 + 0j)
        zeta3 = float(mp_.zeta(3))
        assert abs(inv_det.real - zeta3) / zeta3 < 0.001

    def test_det_is_small_at_s2(self, flow):
        """Δ(2) ≈ 1/ζ(2) is small."""
        det = flow.spectral_determinant(2.0 + 0j)
        expected = 1.0 / (np.pi ** 2 / 6)
        assert abs(abs(det) - expected) / expected < 0.01

    def test_inv_det_times_det_equals_1(self, flow):
        """Δ(s) × Δ(s)^{-1} = 1."""
        s = 2.0 + 0j
        det = flow.spectral_determinant(s)
        inv = flow.inverse_spectral_determinant(s)
        assert np.isclose(det * inv, 1.0, atol=1e-12)

    def test_verify_spectral_determinant(self, flow):
        """verify_spectral_determinant() confirms Δ^{-1} ≈ ζ."""
        result = flow.verify_spectral_determinant(
            s_values=[2.0 + 0j, 3.0 + 0j],
            tol=0.01,
        )
        assert result["all_verified"]

    def test_det_finite(self, flow):
        """Spectral determinant is finite."""
        det = flow.spectral_determinant(2.0 + 0j)
        assert np.isfinite(det)

    def test_det_nonzero_for_s_large(self, flow):
        """Δ(s) ≠ 0 for Re(s) >> 1."""
        det = flow.spectral_determinant(10.0 + 0j)
        assert abs(det) > 0

    def test_more_primes_better_approx(self):
        """More primes in the Euler product → better approximation of ζ(2)."""
        flow100 = IdeleClassFlow(n_primes=100)
        flow300 = IdeleClassFlow(n_primes=300)
        expected = np.pi ** 2 / 6
        err100 = abs(flow100.inverse_spectral_determinant(2.0).real - expected)
        err300 = abs(flow300.inverse_spectral_determinant(2.0).real - expected)
        assert err300 < err100


# ---------------------------------------------------------------------------
# 8. Generator T = -ix∂_x
# ---------------------------------------------------------------------------


class TestGeneratorSelfAdjoint:
    """Test the generator T = -ix∂_x on L²(d*x)."""

    @pytest.fixture
    def flow(self):
        return IdeleClassFlow(n_primes=10)

    def test_matrix_shape(self, flow):
        """Generator matrix has shape (n, n)."""
        n = 30
        T = flow.generator_matrix(n=n)
        assert T.shape == (n, n)

    def test_matrix_hermitian(self, flow):
        """Generator matrix is Hermitian."""
        T = flow.generator_matrix(n=30)
        np.testing.assert_allclose(T, T.conj().T, atol=1e-10)

    def test_eigenvalues_real(self, flow):
        """Eigenvalues of T are real."""
        T = flow.generator_matrix(n=30)
        evals = np.linalg.eigvalsh(T)
        assert np.all(np.isreal(evals))

    def test_self_adjoint_verified(self, flow):
        """verify_generator_self_adjoint() returns True."""
        result = flow.verify_generator_self_adjoint(n=40, n_tests=100)
        assert result["is_self_adjoint"]

    def test_max_error_small(self, flow):
        """Relative self-adjointness error < 1e-8."""
        result = flow.verify_generator_self_adjoint(n=40, n_tests=100)
        assert result["max_relative_error"] < 1e-8

    def test_eigenvalues_real_flag(self, flow):
        """eigenvalues_real flag is True."""
        result = flow.verify_generator_self_adjoint(n=40, n_tests=100)
        assert result["eigenvalues_real"]


# ---------------------------------------------------------------------------
# 9. validate() and validate_idele_class_flow()
# ---------------------------------------------------------------------------


class TestValidate:
    """Test the full validation."""

    def test_validate_returns_float(self):
        """validate_idele_class_flow() returns a float."""
        psi = validate_idele_class_flow(verbose=False)
        assert isinstance(psi, float)

    def test_validate_coherence_1(self):
        """validate_idele_class_flow() returns Ψ = 1.0."""
        psi = validate_idele_class_flow(verbose=False)
        assert psi == 1.0

    def test_flow_validate_method(self):
        """IdeleClassFlow.validate() also returns Ψ = 1.0."""
        flow = IdeleClassFlow(n_primes=20)
        psi = flow.validate(verbose=False)
        assert psi == 1.0


# ---------------------------------------------------------------------------
# 10. Mathematical properties
# ---------------------------------------------------------------------------


class TestMathematicalProperties:
    """Test fundamental mathematical properties of the framework."""

    @pytest.fixture
    def flow(self):
        return IdeleClassFlow(n_primes=50)

    def test_first_orbit_log2(self, flow):
        """The shortest orbit has length log 2 (smallest prime)."""
        L = flow.all_orbit_lengths()
        assert np.isclose(L[0], np.log(2))

    def test_orbit_lengths_distinct(self, flow):
        """All orbit lengths are distinct (primes are distinct)."""
        L = flow.all_orbit_lengths()
        assert len(np.unique(np.round(L, 12))) == len(L)

    def test_orbit_lengths_match_log_primes(self, flow):
        """All orbit lengths match the log of their corresponding prime."""
        for p, length in zip(flow.primes, flow.all_orbit_lengths()):
            assert np.isclose(length, np.log(float(p)), rtol=1e-12)

    def test_artin_product_all_primes(self, flow):
        """Artin product formula holds for all primes in the model."""
        for p in flow.primes[:20]:
            od = flow.artin_product_formula(p)
            assert od.verified, f"Failed for p = {p}"

    def test_spectral_determinant_euler_identity(self, flow):
        """Euler product identity: 1/ζ(2) = ∏_p (1 - p^{-2})."""
        det = flow.spectral_determinant(2.0 + 0j, n_primes=200)
        expected = 6.0 / (np.pi ** 2)  # 1/ζ(2)
        assert abs(abs(det) - expected) / expected < 0.02


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
