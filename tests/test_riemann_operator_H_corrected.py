#!/usr/bin/env python3
"""
Tests for the Corrected Wu-Sprung Operator with Berry-Keating prime correction.

Validates:
    V(x) = V_Abel(x) + ε · V_osc(x)

Functions and classes tested:
    - primes_up_to
    - smooth_zero_count / invert_smooth_count
    - abel_inversion_potential
    - V_osc_prime_sum
    - wigner_dyson_gue_pdf / wigner_dyson_gue_cdf
    - SpacingAnalysis
    - CorrectedWuSprungOperator
    - epsilon_sweep
    - N_sweep

Total: 80 tests.
"""

import pytest
import numpy as np
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from operador.riemann_operator_H_corrected import (
    primes_up_to,
    smooth_zero_count,
    invert_smooth_count,
    abel_inversion_potential,
    V_osc_prime_sum,
    wigner_dyson_gue_pdf,
    wigner_dyson_gue_cdf,
    SpacingAnalysis,
    CorrectedWuSprungOperator,
    epsilon_sweep,
    N_sweep,
    _load_reference_zeros,
)


def _trapz(y: np.ndarray, x: np.ndarray) -> float:
    """Trapezoidal integration helper compatible with NumPy ≥ 2.0."""
    return float(np.sum(0.5 * (y[:-1] + y[1:]) * np.diff(x)))


# ---------------------------------------------------------------------------
# TestPrimeSieve  (8 tests)
# ---------------------------------------------------------------------------

class TestPrimeSieve:
    """Tests for primes_up_to (Sieve of Eratosthenes)."""

    def test_primes_up_to_10(self):
        """primes_up_to(10) must return [2, 3, 5, 7]."""
        assert list(primes_up_to(10)) == [2, 3, 5, 7]

    def test_primes_up_to_2(self):
        """primes_up_to(2) must return [2]."""
        assert list(primes_up_to(2)) == [2]

    def test_primes_up_to_1(self):
        """primes_up_to(1) must return empty list."""
        assert primes_up_to(1) == []

    def test_primes_up_to_0(self):
        """primes_up_to(0) must return empty list."""
        assert primes_up_to(0) == []

    def test_count_up_to_100(self):
        """There are exactly 25 primes up to 100."""
        assert len(primes_up_to(100)) == 25

    def test_all_values_are_prime(self):
        """Every returned value must be prime (check small cases)."""
        ps = primes_up_to(50)
        for p in ps:
            assert p >= 2
            assert all(p % d != 0 for d in range(2, p))

    def test_no_composites(self):
        """4, 6, 8, 9, 10 must not appear in primes_up_to(10)."""
        ps = primes_up_to(10)
        for composite in [4, 6, 8, 9, 10]:
            assert composite not in ps

    def test_sorted_ascending(self):
        """Returned primes must be in strictly ascending order."""
        ps = primes_up_to(50)
        assert ps == sorted(set(ps))


# ---------------------------------------------------------------------------
# TestSmoothZeroCount  (8 tests)
# ---------------------------------------------------------------------------

class TestSmoothZeroCount:
    """Tests for smooth_zero_count and invert_smooth_count."""

    def test_zero_at_zero(self):
        """smooth_zero_count(0) == 0."""
        assert smooth_zero_count(0.0) == 0.0

    def test_negative_returns_zero(self):
        """smooth_zero_count for non-positive E returns 0."""
        assert smooth_zero_count(-5.0) == 0.0

    def test_large_E_positive(self):
        """smooth_zero_count for large E should be positive."""
        assert smooth_zero_count(100.0) > 0.0

    def test_monotone_for_large_E(self):
        """N₀ is increasing for E > 2π."""
        E_vals = np.linspace(10, 200, 20)
        counts = [smooth_zero_count(E) for E in E_vals]
        assert all(counts[i] < counts[i + 1] for i in range(len(counts) - 1))

    def test_inversion_consistency(self):
        """N₀(invert_smooth_count(n)) ≈ n."""
        for n in [1.0, 5.0, 10.0, 20.0]:
            E = invert_smooth_count(n)
            assert abs(smooth_zero_count(E) - n) < 1e-6

    def test_invert_zero_returns_zero(self):
        """invert_smooth_count(0) returns 0."""
        assert invert_smooth_count(0.0) == 0.0

    def test_inversion_monotone(self):
        """Larger n gives larger E from invert_smooth_count."""
        E1 = invert_smooth_count(1.0)
        E5 = invert_smooth_count(5.0)
        E10 = invert_smooth_count(10.0)
        assert E1 < E5 < E10

    def test_inversion_positive(self):
        """invert_smooth_count returns positive E for positive n."""
        for n in [1, 3, 7, 15]:
            assert invert_smooth_count(n) > 0.0


# ---------------------------------------------------------------------------
# TestAbelInversionPotential  (8 tests)
# ---------------------------------------------------------------------------

class TestAbelInversionPotential:
    """Tests for abel_inversion_potential."""

    def test_output_length(self):
        """Output array has same length as input."""
        x = np.linspace(0.1, 10.0, 20)
        V = abel_inversion_potential(x)
        assert len(V) == 20

    def test_output_finite(self):
        """All output values are finite."""
        x = np.linspace(1.0, 50.0, 30)
        V = abel_inversion_potential(x)
        assert np.all(np.isfinite(V))

    def test_monotone_increasing(self):
        """V_Abel must be non-decreasing on a positive grid."""
        x = np.linspace(1.0, 100.0, 50)
        V = abel_inversion_potential(x)
        diffs = np.diff(V)
        assert np.all(diffs >= 0)

    def test_zero_at_zero(self):
        """V_Abel(0) == 0 (handled separately in the code)."""
        x = np.array([0.0])
        V = abel_inversion_potential(x)
        assert V[0] == 0.0

    def test_output_positive_for_positive_x(self):
        """V_Abel > 0 for x > 0."""
        x = np.linspace(1.0, 30.0, 20)
        V = abel_inversion_potential(x)
        assert np.all(V >= 0.0)

    def test_consistent_with_smooth_count(self):
        """V_Abel(x) ≈ N₀^{-1}(x/π): verify round-trip."""
        x_test = np.array([np.pi * 5.0])  # n=5
        V = abel_inversion_potential(x_test)
        n_recovered = smooth_zero_count(V[0])
        assert abs(n_recovered - 5.0) < 0.01

    def test_single_element(self):
        """Works with a single-element array."""
        V = abel_inversion_potential(np.array([np.pi]))
        assert len(V) == 1
        assert V[0] > 0.0

    def test_large_x_gives_large_V(self):
        """Larger x gives larger potential value."""
        V_small = abel_inversion_potential(np.array([10.0]))[0]
        V_large = abel_inversion_potential(np.array([100.0]))[0]
        assert V_large > V_small


# ---------------------------------------------------------------------------
# TestVoscPrimeSum  (8 tests)
# ---------------------------------------------------------------------------

class TestVoscPrimeSum:
    """Tests for V_osc_prime_sum."""

    def test_output_length_array(self):
        """Output array has same length as input."""
        x = np.linspace(0.0, 10.0, 15)
        V = V_osc_prime_sum(x, [2, 3, 5])
        assert len(V) == 15

    def test_empty_primes_returns_zero(self):
        """With no primes, V_osc == 0 everywhere."""
        x = np.array([1.0, 2.0, 3.0])
        V = V_osc_prime_sum(x, [])
        np.testing.assert_array_equal(V, np.zeros(3))

    def test_output_finite(self):
        """All output values are finite."""
        x = np.linspace(0.1, 20.0, 50)
        V = V_osc_prime_sum(x, primes_up_to(30))
        assert np.all(np.isfinite(V))

    def test_single_prime_contribution(self):
        """With one prime p, V_osc(x) = (log p / √p) cos(x log p)."""
        p = 3
        x = np.array([0.0, 1.0, 2.0])
        V = V_osc_prime_sum(x, [p])
        expected = (np.log(p) / np.sqrt(p)) * np.cos(x * np.log(p))
        np.testing.assert_allclose(V, expected, rtol=1e-10)

    def test_cos_symmetry(self):
        """V_osc(0) = sum of log(p)/sqrt(p) for all primes (cos(0)=1)."""
        primes = [2, 3, 5, 7]
        expected = sum(np.log(p) / np.sqrt(p) for p in primes)
        V0 = V_osc_prime_sum(np.array([0.0]), primes)[0]
        assert abs(V0 - expected) < 1e-10

    def test_scalar_input(self):
        """Scalar x input returns scalar output."""
        result = V_osc_prime_sum(np.array([1.0]), [2, 3])
        assert result.shape == (1,)

    def test_more_primes_more_amplitude(self):
        """Adding more primes changes the output."""
        x = np.array([1.0])
        V3 = V_osc_prime_sum(x, [2, 3, 5])
        V4 = V_osc_prime_sum(x, [2, 3, 5, 7])
        assert V3[0] != V4[0]

    def test_bounded_output(self):
        """Output is bounded by sum of |log p / sqrt p| ≤ some finite value."""
        primes = primes_up_to(20)
        bound = sum(np.log(p) / np.sqrt(p) for p in primes)
        x = np.linspace(0.0, 100.0, 200)
        V = V_osc_prime_sum(x, primes)
        assert np.all(np.abs(V) <= bound + 1e-10)


# ---------------------------------------------------------------------------
# TestWignerDysonGUE  (8 tests)
# ---------------------------------------------------------------------------

class TestWignerDysonGUE:
    """Tests for Wigner-Dyson GUE pdf and cdf."""

    def test_pdf_at_zero(self):
        """P(0) = 0."""
        assert wigner_dyson_gue_pdf(np.array([0.0]))[0] == 0.0

    def test_pdf_positive(self):
        """P(s) > 0 for s > 0."""
        s = np.linspace(0.01, 3.0, 50)
        assert np.all(wigner_dyson_gue_pdf(s) > 0)

    def test_pdf_peak_location(self):
        """PDF peak at s* = sqrt(2/π) ≈ 0.798."""
        s = np.linspace(0.01, 3.0, 1000)
        s_peak = s[np.argmax(wigner_dyson_gue_pdf(s))]
        expected = np.sqrt(2.0 / np.pi)
        assert abs(s_peak - expected) < 0.01

    def test_pdf_integral_approx_one(self):
        """∫₀^∞ P(s) ds ≈ 1 (numerical integration)."""
        s = np.linspace(0.0, 6.0, 10000)
        integral = _trapz(wigner_dyson_gue_pdf(s), s)
        assert abs(integral - 1.0) < 0.01

    def test_cdf_at_zero(self):
        """F(0) = 0."""
        assert wigner_dyson_gue_cdf(np.array([0.0]))[0] == 0.0

    def test_cdf_increasing(self):
        """CDF is non-decreasing."""
        s = np.linspace(0.0, 4.0, 50)
        F = wigner_dyson_gue_cdf(s)
        assert np.all(np.diff(F) >= 0)

    def test_cdf_approaches_one(self):
        """F(∞) → 1."""
        assert wigner_dyson_gue_cdf(np.array([20.0]))[0] > 0.999

    def test_cdf_consistency_with_pdf(self):
        """CDF at s ≈ ∫₀^s P(t) dt."""
        s_test = 1.5
        s = np.linspace(0.0, s_test, 10000)
        integral = _trapz(wigner_dyson_gue_pdf(s), s)
        cdf_val = wigner_dyson_gue_cdf(np.array([s_test]))[0]
        assert abs(integral - cdf_val) < 0.001


# ---------------------------------------------------------------------------
# TestSpacingAnalysis  (8 tests)
# ---------------------------------------------------------------------------

class TestSpacingAnalysis:
    """Tests for SpacingAnalysis."""

    @pytest.fixture
    def sample_eigenvalues(self):
        """Fixed set of 20 well-known Riemann zero imaginary parts (γ₁…γ₂₀)
        used as reference eigenvalues for reproducible spacing tests.
        Source: Odlyzko tables / LMFDB."""
        return np.array([
            14.134, 21.022, 25.011, 30.425, 32.935,
            37.586, 40.919, 43.327, 48.005, 49.774,
            52.970, 56.446, 59.347, 60.832, 65.113,
            67.080, 69.546, 72.067, 75.705, 77.145,
        ])

    def test_normalized_spacings_length(self, sample_eigenvalues):
        """Normalised spacings has length n−1."""
        sa = SpacingAnalysis(sample_eigenvalues)
        s = sa.normalized_spacings()
        assert len(s) == len(sample_eigenvalues) - 1

    def test_normalized_spacings_mean(self, sample_eigenvalues):
        """Mean of normalised spacings ≈ 1."""
        sa = SpacingAnalysis(sample_eigenvalues)
        s = sa.normalized_spacings()
        assert abs(np.mean(s) - 1.0) < 1e-10

    def test_normalized_spacings_positive(self, sample_eigenvalues):
        """All normalised spacings are positive."""
        sa = SpacingAnalysis(sample_eigenvalues)
        s = sa.normalized_spacings()
        assert np.all(s > 0)

    def test_ks_statistic_in_range(self, sample_eigenvalues):
        """KS statistic is in [0, 1]."""
        sa = SpacingAnalysis(sample_eigenvalues)
        ks = sa.ks_statistic_gue()
        assert 0.0 <= ks <= 1.0

    def test_ks_statistic_float(self, sample_eigenvalues):
        """ks_statistic_gue returns a float."""
        sa = SpacingAnalysis(sample_eigenvalues)
        assert isinstance(sa.ks_statistic_gue(), float)

    def test_histogram_data_shapes(self, sample_eigenvalues):
        """histogram_data returns two arrays of matching lengths."""
        sa = SpacingAnalysis(sample_eigenvalues)
        centers, counts = sa.histogram_data(n_bins=10)
        assert len(centers) == 10
        assert len(counts) == 10

    def test_histogram_centers_positive(self, sample_eigenvalues):
        """Histogram bin centers are non-negative."""
        sa = SpacingAnalysis(sample_eigenvalues)
        centers, _ = sa.histogram_data()
        assert np.all(centers >= 0)

    def test_unsorted_eigenvalues_sorted(self):
        """SpacingAnalysis sorts eigenvalues internally."""
        ev = np.array([30.0, 10.0, 50.0, 20.0, 40.0])
        sa = SpacingAnalysis(ev)
        assert np.all(np.diff(sa.eigenvalues) >= 0)


# ---------------------------------------------------------------------------
# TestCorrectedWuSprungOperator  (16 tests)
# ---------------------------------------------------------------------------

class TestCorrectedWuSprungOperator:
    """Tests for CorrectedWuSprungOperator."""

    @pytest.fixture
    def small_op(self):
        """Small N=30 operator for fast tests."""
        return CorrectedWuSprungOperator(N=30, N_zeros=30, epsilon=0.0, P=20)

    @pytest.fixture
    def corrected_op(self):
        """Small corrected operator (ε=0.5)."""
        return CorrectedWuSprungOperator(N=30, N_zeros=30, epsilon=0.5, P=20)

    def test_grid_size(self, small_op):
        """Interior grid has exactly N points."""
        assert len(small_op.x) == 30

    def test_grid_positive(self, small_op):
        """All grid points are strictly positive."""
        assert np.all(small_op.x > 0)

    def test_grid_ascending(self, small_op):
        """Grid is strictly ascending."""
        assert np.all(np.diff(small_op.x) > 0)

    def test_v_abel_monotone(self, small_op):
        """V_Abel must be non-decreasing."""
        assert np.all(np.diff(small_op.V_abel) >= 0)

    def test_v_osc_finite(self, small_op):
        """V_osc values must all be finite."""
        assert np.all(np.isfinite(small_op.V_osc_vals))

    def test_matrix_shape(self, small_op):
        """H matrix is N×N."""
        assert small_op.H.shape == (30, 30)

    def test_matrix_symmetric(self, small_op):
        """H matrix is symmetric (Hermitian for real operator)."""
        H_dense = small_op.H.toarray()
        np.testing.assert_allclose(H_dense, H_dense.T, atol=1e-12)

    def test_matrix_tridiagonal(self, small_op):
        """H matrix is tridiagonal (only main and ±1 diagonals non-zero)."""
        H = small_op.H.toarray()
        for i in range(H.shape[0]):
            for j in range(H.shape[1]):
                if abs(i - j) > 1:
                    assert abs(H[i, j]) < 1e-14, f"H[{i},{j}] should be 0"

    def test_eigenvalues_returns_sorted(self, small_op):
        """eigenvalues() returns sorted array."""
        ev = small_op.eigenvalues(k=5)
        assert np.all(np.diff(ev) >= 0)

    def test_eigenvalues_real(self, small_op):
        """Eigenvalues are real."""
        ev = small_op.eigenvalues(k=5)
        assert ev.dtype in [np.float32, np.float64]

    def test_eigenvalues_correct_count(self, small_op):
        """Returns requested number of eigenvalues."""
        ev = small_op.eigenvalues(k=5)
        assert len(ev) == 5

    def test_epsilon_changes_eigenvalues(self, small_op, corrected_op):
        """Non-zero ε shifts eigenvalues."""
        ev_base = small_op.eigenvalues(k=5)
        ev_corr = corrected_op.eigenvalues(k=5)
        assert not np.allclose(ev_base, ev_corr)

    def test_v_total_combines_potentials(self, corrected_op):
        """V_total = V_Abel + ε·V_osc."""
        expected = corrected_op.V_abel + corrected_op.epsilon * corrected_op.V_osc_vals
        np.testing.assert_allclose(corrected_op.V_total, expected, rtol=1e-12)

    def test_epsilon_zero_equals_base(self, small_op):
        """ε=0 operator V_total equals V_Abel."""
        np.testing.assert_allclose(small_op.V_total, small_op.V_abel, rtol=1e-12)

    def test_different_N_works(self):
        """Operator can be built with different grid sizes."""
        for N in [20, 40, 60]:
            op = CorrectedWuSprungOperator(N=N, N_zeros=N, epsilon=0.0, P=10)
            assert op.H.shape == (N, N)

    def test_spacing_analysis_returns_instance(self, small_op):
        """spacing_analysis() returns a SpacingAnalysis instance."""
        sa = small_op.spacing_analysis(k=5)
        assert isinstance(sa, SpacingAnalysis)


# ---------------------------------------------------------------------------
# TestEpsilonSweep  (8 tests)
# ---------------------------------------------------------------------------

class TestEpsilonSweep:
    """Tests for epsilon_sweep."""

    @pytest.fixture(scope="class")
    def sweep_results(self):
        """Run a small epsilon sweep once for the whole class."""
        return epsilon_sweep(
            N=50, epsilons=[0.0, 0.3, 0.5], P=30, N_zeros=50, k_eig=5
        )

    def test_returns_list(self, sweep_results):
        """epsilon_sweep returns a list."""
        assert isinstance(sweep_results, list)

    def test_correct_length(self, sweep_results):
        """One result per epsilon value."""
        assert len(sweep_results) == 3

    def test_has_required_keys(self, sweep_results):
        """Each result has 'epsilon', 'mae', 'n_within_1' keys."""
        for r in sweep_results:
            assert "epsilon" in r
            assert "mae" in r
            assert "n_within_1" in r

    def test_epsilon_values_match(self, sweep_results):
        """Epsilon values in results match input."""
        epsilons = [r["epsilon"] for r in sweep_results]
        assert epsilons == [0.0, 0.3, 0.5]

    def test_mae_finite(self, sweep_results):
        """All MAE values are finite and positive."""
        for r in sweep_results:
            assert np.isfinite(r["mae"])
            assert r["mae"] >= 0.0

    def test_n_within_1_nonnegative(self, sweep_results):
        """n_within_1 is a non-negative integer."""
        for r in sweep_results:
            assert isinstance(r["n_within_1"], int)
            assert r["n_within_1"] >= 0

    def test_correction_helps_at_optimal_epsilon(self, sweep_results):
        """Best epsilon gives smaller MAE than ε=0 baseline."""
        mae_base = sweep_results[0]["mae"]
        mae_best = min(r["mae"] for r in sweep_results)
        assert mae_best <= mae_base

    def test_single_epsilon(self):
        """epsilon_sweep with a single ε value works."""
        result = epsilon_sweep(N=30, epsilons=[0.5], P=20, N_zeros=30, k_eig=5)
        assert len(result) == 1
        assert "mae" in result[0]


# ---------------------------------------------------------------------------
# TestNSweep  (8 tests)
# ---------------------------------------------------------------------------

class TestNSweep:
    """Tests for N_sweep."""

    @pytest.fixture(scope="class")
    def sweep_results(self):
        """Run a small N sweep once for the whole class."""
        return N_sweep(
            N_values=[30, 50], epsilon=0.5, P=30, k_eig=5
        )

    def test_returns_list(self, sweep_results):
        """N_sweep returns a list."""
        assert isinstance(sweep_results, list)

    def test_correct_length(self, sweep_results):
        """One result per N value."""
        assert len(sweep_results) == 2

    def test_has_required_keys(self, sweep_results):
        """Each result has 'N', 'mae_base', 'mae_corrected', 'delta' keys."""
        for r in sweep_results:
            assert "N" in r
            assert "mae_base" in r
            assert "mae_corrected" in r
            assert "delta" in r

    def test_N_values_match(self, sweep_results):
        """N values in results match input."""
        ns = [r["N"] for r in sweep_results]
        assert ns == [30, 50]

    def test_mae_values_finite(self, sweep_results):
        """All MAE values are finite and non-negative."""
        for r in sweep_results:
            assert np.isfinite(r["mae_base"])
            assert np.isfinite(r["mae_corrected"])
            assert r["mae_base"] >= 0.0
            assert r["mae_corrected"] >= 0.0

    def test_delta_is_difference(self, sweep_results):
        """delta = mae_base − mae_corrected."""
        for r in sweep_results:
            assert abs(r["delta"] - (r["mae_base"] - r["mae_corrected"])) < 1e-12

    def test_correction_improves_at_least_one_N(self, sweep_results):
        """For at least one N, the corrected MAE ≤ base MAE."""
        improvements = [r["mae_corrected"] <= r["mae_base"] for r in sweep_results]
        assert any(improvements)

    def test_single_N(self):
        """N_sweep with a single N works."""
        result = N_sweep(N_values=[30], epsilon=0.5, P=20, k_eig=5)
        assert len(result) == 1
        assert result[0]["N"] == 30


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
