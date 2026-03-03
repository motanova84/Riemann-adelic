#!/usr/bin/env python3
"""
Tests for the corrected Wu-Sprung Hamiltonian.

Validates the full mathematical derivation chain:
  WKB → density of states → smooth+oscillatory decomposition
  → trace formula → inverse Abel transform
  → prime-encoded oscillatory potential V_osc(x)
  → corrected Hamiltonian H = -d²/dx² + V_Abel + ε·V_osc

Tests cover:
1. Prime sieve correctness
2. Abel turning point formula
3. Abel inversion (smooth potential)
4. Oscillatory prime potential
5. Full Wu-Sprung potential
6. Hamiltonian construction and properties
7. WuSprungHamiltonian class
8. Spectrum properties
"""

import numpy as np
import pytest
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from operators.riemann_operator_H_corrected import (
    sieve_primes,
    abel_turning_point,
    abel_turning_point_array,
    v_abel_from_turning_point,
    v_osc,
    v_wusprung,
    construct_hamiltonian,
    compute_spectrum,
    WuSprungHamiltonian,
    PI,
    F0,
    C_QCAL,
)


# ---------------------------------------------------------------------------
# 1. Prime Sieve Tests
# ---------------------------------------------------------------------------

class TestSievePrimes:
    """Test prime sieve generation."""

    def test_no_primes_below_2(self):
        """No primes for n_max < 2."""
        assert sieve_primes(0) == []
        assert sieve_primes(1) == []

    def test_primes_up_to_10(self):
        """Primes ≤ 10 are 2, 3, 5, 7."""
        assert sieve_primes(10) == [2, 3, 5, 7]

    def test_primes_up_to_2(self):
        """Single prime 2."""
        assert sieve_primes(2) == [2]

    def test_primes_up_to_20(self):
        """Primes ≤ 20."""
        expected = [2, 3, 5, 7, 11, 13, 17, 19]
        assert sieve_primes(20) == expected

    def test_primes_up_to_50(self):
        """Primes ≤ 50: 15 primes."""
        primes = sieve_primes(50)
        assert len(primes) == 15
        assert primes[0] == 2
        assert primes[-1] == 47

    def test_primes_up_to_100(self):
        """There are 25 primes ≤ 100."""
        assert len(sieve_primes(100)) == 25

    def test_all_prime(self):
        """All returned values are prime."""
        primes = sieve_primes(50)
        for p in primes:
            for d in range(2, p):
                assert p % d != 0, f"{p} is not prime"

    def test_no_composites(self):
        """No composite numbers in result."""
        primes = sieve_primes(30)
        composites = {4, 6, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 22, 24, 25, 26, 27, 28}
        for c in composites:
            assert c not in primes


# ---------------------------------------------------------------------------
# 2. Abel Turning Point Tests
# ---------------------------------------------------------------------------

class TestAbelTurningPoint:
    """Test the classical turning point formula x_t(E) = (2√E/π)(log(2E/π) - 2)."""

    def test_positive_energy_required(self):
        """E ≤ 0 should raise ValueError."""
        with pytest.raises(ValueError):
            abel_turning_point(0.0)
        with pytest.raises(ValueError):
            abel_turning_point(-1.0)

    def test_formula_at_E1(self):
        """Verify formula at E = 1: x_t(E) = (2*sqrt(E)/pi)*(log(2*E/pi) - 2)."""
        E = 1.0
        expected = (2.0 * np.sqrt(E) / PI) * (np.log(2.0 * E / PI) - 2.0)
        assert abs(abel_turning_point(E) - expected) < 1e-14

    def test_formula_at_E100(self):
        """Verify formula at E = 100."""
        E = 100.0
        expected = (2.0 * np.sqrt(E) / PI) * (np.log(2.0 * E / PI) - 2.0)
        assert abs(abel_turning_point(E) - expected) < 1e-10

    def test_monotone_increasing_large_E(self):
        """x_t(E) should be monotone increasing for large E."""
        E_vals = np.linspace(20.0, 500.0, 50)
        x_vals = np.array([abel_turning_point(E) for E in E_vals])
        diffs = np.diff(x_vals)
        assert np.all(diffs > 0), "x_t(E) must be monotone increasing for large E"

    def test_array_matches_scalar(self):
        """Vectorized result matches scalar computation."""
        E_vals = np.array([10.0, 50.0, 100.0, 200.0])
        scalar_results = np.array([abel_turning_point(E) for E in E_vals])
        array_result = abel_turning_point_array(E_vals)
        np.testing.assert_allclose(array_result, scalar_results, rtol=1e-12)

    def test_array_input(self):
        """Array input returns array."""
        E_arr = np.linspace(10.0, 100.0, 20)
        x_t = abel_turning_point_array(E_arr)
        assert x_t.shape == E_arr.shape

    def test_sqrt_scaling(self):
        """x_t scales roughly as √E for large E (dominant term)."""
        E1, E2 = 100.0, 400.0
        x1 = abel_turning_point(E1)
        x2 = abel_turning_point(E2)
        # Ratio should be between 1 and E2/E1 (√(E2/E1) = 2 for E2=4·E1)
        ratio = x2 / x1
        assert 1.5 < ratio < 4.0


# ---------------------------------------------------------------------------
# 3. Abel Inversion (V_Abel) Tests
# ---------------------------------------------------------------------------

class TestVAbel:
    """Test smooth Abel potential from inverse Abel transform."""

    def test_output_shape(self):
        """V_Abel has the same shape as input x."""
        x = np.linspace(0.5, 20.0, 100)
        V = v_abel_from_turning_point(x)
        assert V.shape == x.shape

    def test_positive_potential(self):
        """V_Abel(x) > 0 for positive x in physical range."""
        x = np.linspace(1.0, 20.0, 50)
        V = v_abel_from_turning_point(x)
        assert np.all(V > 0), "V_Abel must be positive in physical domain"

    def test_monotone_increasing(self):
        """V_Abel should be monotone increasing (confining potential)."""
        x = np.linspace(2.0, 25.0, 100)
        V = v_abel_from_turning_point(x)
        diffs = np.diff(V)
        assert np.all(diffs >= 0), "V_Abel must be non-decreasing"

    def test_finite_values(self):
        """All potential values are finite."""
        x = np.linspace(0.5, 30.0, 200)
        V = v_abel_from_turning_point(x)
        assert np.all(np.isfinite(V))

    def test_scalar_input(self):
        """Works with scalar wrapped in array."""
        x = np.array([5.0])
        V = v_abel_from_turning_point(x)
        assert len(V) == 1
        assert V[0] > 0

    def test_different_grid_sizes(self):
        """Different grid sizes give consistent results."""
        x = np.array([5.0, 10.0, 15.0])
        V1 = v_abel_from_turning_point(x, n_grid=5000)
        V2 = v_abel_from_turning_point(x, n_grid=20000)
        np.testing.assert_allclose(V1, V2, rtol=0.01)


# ---------------------------------------------------------------------------
# 4. Oscillatory Prime Potential Tests
# ---------------------------------------------------------------------------

class TestVOsc:
    """Test oscillatory prime-encoded potential V_osc(x)."""

    def test_output_shape(self):
        """V_osc has the same shape as input x."""
        x = np.linspace(0.0, 10.0, 100)
        primes = sieve_primes(20)
        V = v_osc(x, primes)
        assert V.shape == x.shape

    def test_real_output(self):
        """V_osc returns real values."""
        x = np.linspace(0.0, 10.0, 50)
        primes = sieve_primes(30)
        V = v_osc(x, primes)
        assert np.all(np.isreal(V))
        assert V.dtype == np.float64

    def test_finite_values(self):
        """V_osc is finite everywhere."""
        x = np.linspace(0.0, 50.0, 200)
        primes = sieve_primes(50)
        V = v_osc(x, primes)
        assert np.all(np.isfinite(V))

    def test_zero_phases(self):
        """Zero phases (default) give a specific formula."""
        x = np.array([1.0])
        primes = [2]
        V = v_osc(x, primes, phases=None, p_max=10)
        expected = (np.log(2.0) / np.sqrt(2.0)) * np.cos(np.log(2.0))
        assert abs(V[0] - expected) < 1e-12

    def test_custom_phases(self):
        """Custom phases shift the cosine."""
        x = np.array([0.0])
        primes = [2]
        phi = np.array([PI / 2])
        V = v_osc(x, primes, phases=phi, p_max=10)
        # cos(0 + PI/2) = 0
        expected = (np.log(2.0) / np.sqrt(2.0)) * 0.0
        assert abs(V[0] - expected) < 1e-12

    def test_phases_length_mismatch_raises(self):
        """Mismatched phases length should raise ValueError."""
        x = np.array([1.0, 2.0])
        primes = sieve_primes(20)
        n_primes = len([p for p in primes if p <= 20])
        bad_phases = np.zeros(n_primes + 1)
        with pytest.raises(ValueError):
            v_osc(x, primes, phases=bad_phases, p_max=20)

    def test_p_max_filter(self):
        """p_max correctly filters primes."""
        x = np.linspace(0.0, 5.0, 20)
        primes_full = sieve_primes(100)
        V_small = v_osc(x, primes_full, p_max=10)
        V_large = v_osc(x, primes_full, p_max=100)
        # More primes should generally give different result
        # (only equal if additional primes contribute zero, unlikely)
        assert not np.allclose(V_small, V_large)

    def test_oscillatory_behavior(self):
        """V_osc exhibits oscillations (not monotone)."""
        x = np.linspace(0.1, 20.0, 300)
        primes = sieve_primes(50)
        V = v_osc(x, primes)
        dV = np.diff(V)
        sign_changes = np.sum(np.diff(np.sign(dV)) != 0)
        assert sign_changes > 10, "V_osc must have multiple oscillations"

    def test_single_prime_formula(self):
        """Single prime p=3 matches analytic formula."""
        x = np.array([2.0, 5.0])
        primes_only_3 = [3]
        V = v_osc(x, primes_only_3, phases=None, p_max=10)
        log3 = np.log(3.0)
        expected = (log3 / np.sqrt(3.0)) * np.cos(x * log3)
        np.testing.assert_allclose(V, expected, rtol=1e-12)

    def test_prime_imprint(self):
        """V_osc encodes prime frequencies log p in Fourier decomposition."""
        x = np.linspace(0.0, 100.0, 10000)
        primes = [2]
        V = v_osc(x, primes)
        # Fourier transform should peak near frequency log(2)/(2π)
        fft_V = np.abs(np.fft.rfft(V))
        freqs = np.fft.rfftfreq(len(x), d=(x[1] - x[0]))
        peak_freq = freqs[np.argmax(fft_V[1:])]
        expected_freq = np.log(2.0) / (2.0 * PI)
        # Allow ±20% tolerance due to discrete FFT resolution
        assert abs(peak_freq - expected_freq) < 0.2 * expected_freq


# ---------------------------------------------------------------------------
# 5. Full Wu-Sprung Potential Tests
# ---------------------------------------------------------------------------

class TestVWuSprung:
    """Test combined potential V = V_Abel + ε·V_osc."""

    def test_output_shape(self):
        """v_wusprung returns array of same shape as x."""
        x = np.linspace(1.0, 20.0, 50)
        primes = sieve_primes(30)
        V = v_wusprung(x, primes)
        assert V.shape == x.shape

    def test_epsilon_zero_equals_abel(self):
        """For ε = 0, full potential reduces to V_Abel."""
        x = np.linspace(2.0, 20.0, 50)
        primes = sieve_primes(30)
        V_full = v_wusprung(x, primes, epsilon=0.0)
        V_abel = v_abel_from_turning_point(x)
        np.testing.assert_allclose(V_full, V_abel, rtol=1e-10)

    def test_decomposition_linearity(self):
        """V(x) = V_Abel(x) + ε·V_osc(x) exactly."""
        x = np.linspace(2.0, 20.0, 30)
        primes = sieve_primes(20)
        eps = 0.5
        V_combined = v_wusprung(x, primes, epsilon=eps)
        V_abel = v_abel_from_turning_point(x)
        V_osc_part = v_osc(x, primes)
        np.testing.assert_allclose(
            V_combined, V_abel + eps * V_osc_part, rtol=1e-10
        )

    def test_finite_potential(self):
        """Full potential is finite everywhere."""
        x = np.linspace(0.5, 25.0, 100)
        primes = sieve_primes(50)
        V = v_wusprung(x, primes)
        assert np.all(np.isfinite(V))

    def test_epsilon_scaling(self):
        """Difference V(ε) - V_Abel scales linearly with ε."""
        x = np.linspace(2.0, 15.0, 30)
        primes = sieve_primes(20)
        eps1, eps2 = 1.0, 2.0
        V1 = v_wusprung(x, primes, epsilon=eps1)
        V2 = v_wusprung(x, primes, epsilon=eps2)
        V0 = v_abel_from_turning_point(x)
        diff1 = V1 - V0
        diff2 = V2 - V0
        np.testing.assert_allclose(diff2, 2.0 * diff1, rtol=1e-10)


# ---------------------------------------------------------------------------
# 6. Hamiltonian Construction Tests
# ---------------------------------------------------------------------------

class TestConstructHamiltonian:
    """Test Hamiltonian matrix construction."""

    @pytest.fixture
    def small_H(self):
        x = np.linspace(2.0, 20.0, 50)
        primes = sieve_primes(20)
        H, V = construct_hamiltonian(x, primes, epsilon=0.1)
        return H, V, x

    def test_symmetric(self, small_H):
        """H is symmetric (Hermitian for real case)."""
        H, V, x = small_H
        assert np.max(np.abs(H - H.T)) < 1e-12

    def test_correct_shape(self, small_H):
        """H has shape (n, n)."""
        H, V, x = small_H
        n = len(x)
        assert H.shape == (n, n)

    def test_tridiagonal_structure(self, small_H):
        """Off-diagonal structure is tridiagonal (kinetic + diagonal potential)."""
        H, V, x = small_H
        n = len(x)
        # Beyond second super/sub-diagonal should be zero
        for i in range(n):
            for j in range(n):
                if abs(i - j) > 1:
                    assert abs(H[i, j]) < 1e-12, (
                        f"Non-tridiagonal element H[{i},{j}] = {H[i, j]}"
                    )

    def test_potential_diagonal(self, small_H):
        """Potential appears on diagonal of H."""
        H, V, x = small_H
        dx = x[1] - x[0]
        kinetic_diag = 2.0 / dx**2
        # H[i,i] = kinetic_diag + V[i]
        for i in range(len(x)):
            expected = kinetic_diag + V[i]
            assert abs(H[i, i] - expected) < 1e-8

    def test_positive_definite_large_potential(self):
        """With strongly confining potential, H is positive definite."""
        x = np.linspace(2.0, 10.0, 30)
        primes = sieve_primes(10)
        H, V = construct_hamiltonian(x, primes, epsilon=0.0)
        eigenvals, _ = np.linalg.eigh(H)
        # Lowest eigenvalue should be positive (confining Hamiltonian)
        assert eigenvals[0] > 0, "Lowest eigenvalue must be positive"


# ---------------------------------------------------------------------------
# 7. WuSprungHamiltonian Class Tests
# ---------------------------------------------------------------------------

class TestWuSprungHamiltonian:
    """Test the WuSprungHamiltonian class."""

    @pytest.fixture
    def default_H(self):
        return WuSprungHamiltonian(
            x_min=1.0, x_max=20.0, n_points=100, p_max=20, epsilon=1.0
        )

    def test_initialization(self, default_H):
        """Class initializes without error."""
        assert default_H is not None

    def test_grid_shape(self, default_H):
        """Spatial grid has correct length."""
        assert len(default_H.x) == 100

    def test_grid_boundaries(self, default_H):
        """Grid starts at x_min and ends at x_max."""
        assert abs(default_H.x[0] - 1.0) < 1e-10
        assert abs(default_H.x[-1] - 20.0) < 1e-10

    def test_primes_generated(self, default_H):
        """Primes up to p_max are generated."""
        primes_ref = sieve_primes(20)
        assert default_H.primes == primes_ref

    def test_n_primes_property(self, default_H):
        """n_primes property matches length of primes list."""
        assert default_H.n_primes == len(default_H.primes)

    def test_hamiltonian_shape(self, default_H):
        """Hamiltonian matrix has shape (n_points, n_points)."""
        n = default_H.n_points
        assert default_H.H.shape == (n, n)

    def test_hamiltonian_symmetric(self, default_H):
        """Hamiltonian is symmetric."""
        assert np.max(np.abs(default_H.H - default_H.H.T)) < 1e-12

    def test_potential_components(self, default_H):
        """V = V_Abel + ε·V_osc."""
        V_expected = default_H.V_abel + default_H.epsilon * default_H.V_oscillatory
        np.testing.assert_allclose(default_H.V, V_expected, rtol=1e-10)

    def test_v_abel_method(self, default_H):
        """v_abel method returns correct smooth potential."""
        x_test = np.array([5.0, 10.0])
        V_method = default_H.v_abel(x_test)
        V_func = v_abel_from_turning_point(
            x_test,
            E_min=default_H.E_min,
            E_max=default_H.E_max,
            n_grid=default_H.n_grid,
        )
        np.testing.assert_allclose(V_method, V_func, rtol=1e-10)

    def test_v_prime_method(self, default_H):
        """v_prime method returns correct oscillatory potential."""
        x_test = np.array([3.0, 7.0])
        V_method = default_H.v_prime(x_test)
        V_func = v_osc(x_test, default_H.primes, phases=default_H.phases, p_max=default_H.p_max)
        np.testing.assert_allclose(V_method, V_func, rtol=1e-10)

    def test_potential_method(self, default_H):
        """potential method returns V_Abel + ε·V_osc."""
        x_test = np.linspace(2.0, 15.0, 20)
        V_method = default_H.potential(x_test)
        V_expected = default_H.v_abel(x_test) + default_H.epsilon * default_H.v_prime(x_test)
        np.testing.assert_allclose(V_method, V_expected, rtol=1e-10)

    def test_compute_spectrum(self, default_H):
        """compute_spectrum returns correct number of eigenvalues."""
        eigvals, eigvecs = default_H.compute_spectrum(n_eigenvalues=5)
        assert len(eigvals) == 5
        assert eigvecs.shape == (100, 5)

    def test_eigenvalues_real(self, default_H):
        """All eigenvalues are real."""
        eigvals, _ = default_H.compute_spectrum(n_eigenvalues=5)
        assert np.all(np.isreal(eigvals))

    def test_eigenvalues_sorted(self, default_H):
        """Eigenvalues are returned in ascending order."""
        eigvals, _ = default_H.compute_spectrum(n_eigenvalues=10)
        assert np.all(np.diff(eigvals) >= 0)

    def test_eigenvectors_normalized(self, default_H):
        """Eigenvectors are normalized."""
        _, eigvecs = default_H.compute_spectrum(n_eigenvalues=5)
        for i in range(5):
            norm = np.linalg.norm(eigvecs[:, i])
            assert abs(norm - 1.0) < 1e-8

    def test_epsilon_zero_reduces_to_smooth(self):
        """ε = 0 gives Hamiltonian with only V_Abel."""
        H_obj = WuSprungHamiltonian(
            x_min=2.0, x_max=15.0, n_points=50, p_max=10, epsilon=0.0
        )
        np.testing.assert_allclose(H_obj.V, H_obj.V_abel, rtol=1e-10)

    def test_invalid_x_min_raises(self):
        """x_min ≤ 0 should raise ValueError."""
        with pytest.raises(ValueError):
            WuSprungHamiltonian(x_min=0.0)

    def test_invalid_domain_raises(self):
        """x_max ≤ x_min should raise ValueError."""
        with pytest.raises(ValueError):
            WuSprungHamiltonian(x_min=10.0, x_max=5.0)

    def test_repr(self, default_H):
        """__repr__ returns a descriptive string."""
        r = repr(default_H)
        assert "WuSprungHamiltonian" in r
        assert "p_max=20" in r

    def test_positive_eigenvalues(self, default_H):
        """Lowest eigenvalues are positive (confining potential)."""
        eigvals, _ = default_H.compute_spectrum(n_eigenvalues=3)
        assert eigvals[0] > 0, "Lowest eigenvalue must be positive"

    def test_different_epsilon_different_spectrum(self):
        """Different ε values give different spectra."""
        params = dict(x_min=2.0, x_max=20.0, n_points=80, p_max=20)
        H1 = WuSprungHamiltonian(epsilon=0.0, **params)
        H2 = WuSprungHamiltonian(epsilon=1.0, **params)
        e1, _ = H1.compute_spectrum(n_eigenvalues=5)
        e2, _ = H2.compute_spectrum(n_eigenvalues=5)
        # Spectra should differ due to oscillatory correction
        assert not np.allclose(e1, e2, atol=1e-6)


# ---------------------------------------------------------------------------
# 8. Spectrum (standalone function) Tests
# ---------------------------------------------------------------------------

class TestComputeSpectrum:
    """Test standalone compute_spectrum function."""

    def test_returns_sorted(self):
        """compute_spectrum returns sorted eigenvalues."""
        H = np.array([[3.0, 1.0], [1.0, 2.0]])
        eigvals, _ = compute_spectrum(H)
        assert eigvals[0] <= eigvals[1]

    def test_n_eigenvalues_parameter(self):
        """n_eigenvalues parameter limits returned count."""
        n = 20
        H = np.diag(np.arange(1.0, n + 1))
        eigvals, eigvecs = compute_spectrum(H, n_eigenvalues=5)
        assert len(eigvals) == 5
        assert eigvecs.shape == (n, 5)

    def test_all_eigenvalues_when_none(self):
        """n_eigenvalues=None returns all eigenvalues."""
        n = 10
        H = np.diag(np.arange(1.0, n + 1))
        eigvals, _ = compute_spectrum(H, n_eigenvalues=None)
        assert len(eigvals) == n

    def test_symmetric_input(self):
        """Works correctly for symmetric real matrix."""
        A = np.random.default_rng(0).standard_normal((10, 10))
        H = A + A.T  # Make symmetric
        eigvals, eigvecs = compute_spectrum(H)
        assert len(eigvals) == 10
        assert np.all(np.isreal(eigvals))


# ---------------------------------------------------------------------------
# 9. Physical Constants Tests
# ---------------------------------------------------------------------------

class TestConstants:
    """Test QCAL physical constants."""

    def test_fundamental_frequency(self):
        """f₀ = 141.7001 Hz."""
        assert abs(F0 - 141.7001) < 1e-6

    def test_qcal_coherence_constant(self):
        """C_QCAL = 244.36."""
        assert abs(C_QCAL - 244.36) < 1e-6

    def test_pi_value(self):
        """PI is correct."""
        assert abs(PI - np.pi) < 1e-15


# ---------------------------------------------------------------------------
# 10. Integration Tests
# ---------------------------------------------------------------------------

class TestIntegration:
    """Integration tests for the full pipeline."""

    def test_full_pipeline(self):
        """Complete pipeline: construct → spectrum → validate positivity."""
        primes = sieve_primes(30)
        x = np.linspace(2.0, 25.0, 200)

        # Build potential
        V = v_wusprung(x, primes, epsilon=0.5)
        assert V.shape == x.shape
        assert np.all(np.isfinite(V))

        # Build Hamiltonian
        H, _ = construct_hamiltonian(x, primes, epsilon=0.5)
        assert H.shape == (200, 200)
        assert np.max(np.abs(H - H.T)) < 1e-10

        # Compute spectrum
        eigvals, eigvecs = compute_spectrum(H, n_eigenvalues=10)
        assert len(eigvals) == 10
        assert np.all(eigvals > 0)

    def test_class_pipeline(self):
        """WuSprungHamiltonian full pipeline."""
        H = WuSprungHamiltonian(
            x_min=2.0, x_max=20.0, n_points=100, p_max=20, epsilon=1.0
        )
        assert H.n_primes > 0
        eigvals, eigvecs = H.compute_spectrum(n_eigenvalues=5)
        assert len(eigvals) == 5
        assert np.all(eigvals > 0)
        assert np.all(np.isfinite(eigvals))

    def test_prime_encoding_in_potential(self):
        """Primes encode their log-frequencies in V_osc spectrum."""
        x = np.linspace(0.0, 200.0, 20000)
        primes = [2, 3]
        V = v_osc(x, primes, p_max=10)
        dx = x[1] - x[0]
        freqs = np.fft.rfftfreq(len(x), d=dx)
        fft_mag = np.abs(np.fft.rfft(V))

        # Find peaks
        peak_freqs = freqs[np.argsort(fft_mag[1:])[-5:] + 1]

        # Expected frequencies: log(p)/(2*PI)
        expected_freqs = sorted([np.log(p) / (2 * PI) for p in [2, 3]])

        # At least one prime frequency should appear in the top peaks
        found = any(
            any(abs(pf - ef) < 0.05 for ef in expected_freqs)
            for pf in peak_freqs
        )
        assert found, (
            f"Prime frequencies {expected_freqs} not found in V_osc FFT peaks {sorted(peak_freqs)}"
        )

    def test_abel_turning_point_inversion_consistency(self):
        """V_Abel(x_t(E)) ≈ E (inversion consistency)."""
        E_vals = np.array([20.0, 50.0, 100.0, 200.0])
        x_t_vals = abel_turning_point_array(E_vals)
        V_recovered = v_abel_from_turning_point(
            x_t_vals, E_min=1.0, E_max=500.0, n_grid=50000
        )
        # Should recover E within reasonable tolerance of interpolation
        np.testing.assert_allclose(V_recovered, E_vals, rtol=0.05)


if __name__ == "__main__":
    pytest.main([__file__, "-v", "-s"])
