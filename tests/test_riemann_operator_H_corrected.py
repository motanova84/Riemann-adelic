"""
test_riemann_operator_H_corrected.py
=====================================
Tests para el módulo riemann_operator_H_corrected.py

Autor: JMMB Ψ (Trinity QCAL ∞³)
"""
import math

import numpy as np
import pytest

from riemann_operator_H import ZEROS_ZETA_REFERENCIA, N_smooth, WuSprungOperator
from riemann_operator_H_corrected import (
    CorrectedWuSprungOperator,
    SpacingAnalysis,
    V_osc_array,
    V_osc_prime_sum,
    _check_monotone_decreasing,
    epsilon_sweep,
    primes_up_to,
    N_sweep,
)

# ---------------------------------------------------------------------------
# Fixtures compartidos
# ---------------------------------------------------------------------------

@pytest.fixture(scope="module")
def small_primes():
    return primes_up_to(30)


@pytest.fixture(scope="module")
def corrected_op():
    """Operador corregido con parámetros pequeños para tests rápidos."""
    return CorrectedWuSprungOperator(N=100, x_max=13.0, epsilon=0.3, primes_upto=30)


@pytest.fixture(scope="module")
def base_op():
    return CorrectedWuSprungOperator(N=100, x_max=13.0, epsilon=0.0, primes_upto=30)


@pytest.fixture(scope="module")
def spacing_analysis(corrected_op):
    return SpacingAnalysis(corrected_op.eigenvalues())


@pytest.fixture(scope="module")
def spacing_analysis_zeros():
    return SpacingAnalysis(np.array(ZEROS_ZETA_REFERENCIA))


# ===========================================================================
# Tests: primes_up_to
# ===========================================================================

class TestPrimesUpTo:

    def test_primes_up_to_30(self):
        p = primes_up_to(30)
        assert p == [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]

    def test_primes_up_to_2(self):
        assert primes_up_to(2) == [2]

    def test_primes_up_to_1_returns_empty(self):
        assert primes_up_to(1) == []

    def test_primes_up_to_0_returns_empty(self):
        assert primes_up_to(0) == []

    def test_primes_count_up_to_100(self):
        # Hay 25 primos ≤ 100
        assert len(primes_up_to(100)) == 25

    def test_all_entries_prime(self, small_primes):
        for p in small_primes:
            assert all(p % i != 0 for i in range(2, p)), f"{p} no es primo"

    def test_sorted_ascending(self, small_primes):
        assert small_primes == sorted(small_primes)

    def test_no_duplicates(self, small_primes):
        assert len(small_primes) == len(set(small_primes))


# ===========================================================================
# Tests: V_osc_prime_sum
# ===========================================================================

class TestVOscPrimeSum:

    def test_zero_primes_returns_zero(self):
        assert V_osc_prime_sum(1.0, []) == 0.0

    def test_single_prime_2(self):
        x = 1.0
        expected = (math.log(2) / math.sqrt(2)) * math.cos(x * math.log(2))
        assert abs(V_osc_prime_sum(x, [2]) - expected) < 1e-12

    def test_x_zero(self, small_primes):
        # cos(0) = 1 para todos, resultado = Σ log(p)/√p
        result = V_osc_prime_sum(0.0, small_primes)
        expected = sum(math.log(p) / math.sqrt(p) for p in small_primes)
        assert abs(result - expected) < 1e-10

    def test_returns_float(self, small_primes):
        result = V_osc_prime_sum(5.0, small_primes)
        assert isinstance(result, float)

    def test_oscillatory_sign_change(self, small_primes):
        # Debe haber al menos un par de x con signos distintos
        values = [V_osc_prime_sum(x, small_primes) for x in np.linspace(0.1, 50.0, 200)]
        assert min(values) < 0 and max(values) > 0

    def test_consistency_with_array(self, small_primes):
        xs = np.array([1.0, 2.0, 3.0])
        arr = V_osc_array(xs, small_primes)
        for i, x in enumerate(xs):
            assert abs(V_osc_prime_sum(x, small_primes) - arr[i]) < 1e-12


# ===========================================================================
# Tests: V_osc_array
# ===========================================================================

class TestVOscArray:

    def test_empty_primes_returns_zeros(self):
        x = np.array([1.0, 2.0, 3.0])
        result = V_osc_array(x, [])
        np.testing.assert_array_equal(result, np.zeros(3))

    def test_shape_matches_input(self, small_primes):
        x = np.linspace(0.1, 10.0, 50)
        result = V_osc_array(x, small_primes)
        assert result.shape == (50,)

    def test_values_finite(self, small_primes):
        x = np.linspace(0.1, 20.0, 100)
        result = V_osc_array(x, small_primes)
        assert np.all(np.isfinite(result))

    def test_single_element(self, small_primes):
        x = np.array([2.5])
        result = V_osc_array(x, small_primes)
        expected = V_osc_prime_sum(2.5, small_primes)
        assert abs(result[0] - expected) < 1e-12


# ===========================================================================
# Tests: CorrectedWuSprungOperator
# ===========================================================================

class TestCorrectedWuSprungOperator:

    def test_constructor_defaults(self):
        op = CorrectedWuSprungOperator()
        assert op.N == 300
        assert op.x_max == 13.0
        assert op.epsilon == 0.0

    def test_constructor_raises_invalid_N(self):
        with pytest.raises(ValueError):
            CorrectedWuSprungOperator(N=1)

    def test_constructor_raises_negative_x_max(self):
        with pytest.raises(ValueError):
            CorrectedWuSprungOperator(x_max=-1.0)

    def test_constructor_raises_negative_epsilon(self):
        with pytest.raises(ValueError):
            CorrectedWuSprungOperator(epsilon=-0.1)

    def test_x_grid_shape(self, corrected_op):
        assert corrected_op.x_grid.shape == (corrected_op.N,)

    def test_potential_shape(self, corrected_op):
        assert corrected_op.potential.shape == (corrected_op.N,)

    def test_potential_base_shape(self, corrected_op):
        assert corrected_op.potential_base.shape == (corrected_op.N,)

    def test_potential_osc_shape(self, corrected_op):
        assert corrected_op.potential_osc.shape == (corrected_op.N,)

    def test_potential_total_is_base_plus_eps_osc(self, corrected_op):
        expected = corrected_op.potential_base + corrected_op.epsilon * corrected_op.potential_osc
        np.testing.assert_allclose(corrected_op.potential, expected, rtol=1e-12)

    def test_eigenvalues_sorted(self, corrected_op):
        evals = corrected_op.eigenvalues()
        assert np.all(np.diff(evals) >= 0)

    def test_eigenvalues_count_N(self, corrected_op):
        evals = corrected_op.eigenvalues()
        assert len(evals) == corrected_op.N

    def test_eigenvalues_n_vals_truncation(self, corrected_op):
        evals = corrected_op.eigenvalues(n_vals=5)
        assert len(evals) == 5

    def test_eigenvalues_positive(self, corrected_op):
        evals = corrected_op.eigenvalues(5)
        assert np.all(evals > 0)

    def test_eigenvalues_caching(self, corrected_op):
        e1 = corrected_op.eigenvalues()
        e2 = corrected_op.eigenvalues()
        np.testing.assert_array_equal(e1, e2)

    def test_compare_to_zeros_returns_tuple_of_3(self, corrected_op):
        result = corrected_op.compare_to_zeros()
        assert len(result) == 3

    def test_compare_to_zeros_mae_positive(self, corrected_op):
        _, _, mae = corrected_op.compare_to_zeros()
        assert mae > 0

    def test_compare_to_zeros_custom_refs(self, corrected_op):
        refs = [14.0, 21.0]
        evals, refs_arr, mae = corrected_op.compare_to_zeros(refs)
        assert len(refs_arr) == 2

    def test_fraction_small_spacings_in_range(self, corrected_op):
        f = corrected_op.fraction_small_spacings()
        assert 0.0 <= f <= 1.0

    def test_fraction_small_spacings_custom_threshold(self, corrected_op):
        f = corrected_op.fraction_small_spacings(threshold=0.5)
        assert 0.0 <= f <= 1.0

    def test_epsilon_zero_matches_base(self, base_op, corrected_op):
        """Con ε=0 el potencial total coincide con el potencial base."""
        np.testing.assert_allclose(
            base_op.potential, base_op.potential_base, rtol=1e-12
        )


# ===========================================================================
# Tests: SpacingAnalysis
# ===========================================================================

class TestSpacingAnalysis:

    def test_unfolded_shape(self, spacing_analysis, corrected_op):
        assert len(spacing_analysis.unfolded) == corrected_op.N

    def test_unfolded_monotone(self, spacing_analysis):
        xi = spacing_analysis.unfolded
        # N_smooth es monótona creciente para E>0
        assert np.all(np.diff(xi) >= 0)

    def test_spacings_shape(self, spacing_analysis, corrected_op):
        assert len(spacing_analysis.spacings) == corrected_op.N - 1

    def test_spacings_positive(self, spacing_analysis):
        assert np.all(spacing_analysis.spacings >= 0)

    def test_mean_spacing_approx_one(self, spacing_analysis):
        # La normalización garantiza media ≈ 1
        ms = spacing_analysis.mean_spacing()
        assert abs(ms - 1.0) < 0.1

    def test_ks_statistic_in_range(self, spacing_analysis):
        ks = spacing_analysis.ks_statistic()
        assert 0.0 <= ks <= 1.0

    def test_ks_zeros_less_than_ws(self, spacing_analysis, spacing_analysis_zeros):
        """Los ceros de ζ deben tener KS menor que Wu-Sprung (más compatible con GUE)."""
        ks_zeros = spacing_analysis_zeros.ks_statistic()
        ks_ws = spacing_analysis.ks_statistic()
        assert ks_zeros < ks_ws, (
            f"KS zeros ({ks_zeros:.4f}) should be < KS Wu-Sprung ({ks_ws:.4f})"
        )

    def test_fraction_small_nonnegative(self, spacing_analysis):
        assert spacing_analysis.fraction_small_spacings(0.2) >= 0.0

    def test_wigner_dyson_pdf_at_zero(self):
        result = SpacingAnalysis.wigner_dyson_pdf(np.array([0.0]))
        assert result[0] == pytest.approx(0.0, abs=1e-12)

    def test_wigner_dyson_pdf_positive(self):
        s = np.linspace(0.1, 3.0, 50)
        pdf = SpacingAnalysis.wigner_dyson_pdf(s)
        assert np.all(pdf > 0)

    def test_wigner_dyson_pdf_peak_location(self):
        # Máximo en s* = √(2/π) ≈ 0.798
        s = np.linspace(0.01, 3.0, 1000)
        pdf = SpacingAnalysis.wigner_dyson_pdf(s)
        peak_s = s[np.argmax(pdf)]
        assert abs(peak_s - math.sqrt(2.0 / math.pi)) < 0.01

    def test_spacing_analysis_from_zeros(self, spacing_analysis_zeros):
        ks = spacing_analysis_zeros.ks_statistic()
        assert 0.0 <= ks <= 1.0


# ===========================================================================
# Tests: epsilon_sweep
# ===========================================================================

class TestEpsilonSweep:

    @pytest.fixture(scope="class")
    def sweep_results(self):
        return epsilon_sweep(
            epsilons=[0.0, 0.1, 0.3],
            primes_upto=30,
            N=80,
            x_max=13.0,
        )

    def test_result_count(self, sweep_results):
        assert len(sweep_results) == 3

    def test_result_keys(self, sweep_results):
        required = {"epsilon", "mean_abs_error", "n_within_1", "n_within_5pct",
                    "improvement_vs_base"}
        for r in sweep_results:
            assert required.issubset(r.keys())

    def test_epsilon_zero_has_zero_improvement(self, sweep_results):
        r0 = next(r for r in sweep_results if r["epsilon"] == 0.0)
        assert abs(r0["improvement_vs_base"]) < 1e-10

    def test_mae_positive(self, sweep_results):
        for r in sweep_results:
            assert r["mean_abs_error"] > 0.0

    def test_n_within_1_nonnegative(self, sweep_results):
        for r in sweep_results:
            assert r["n_within_1"] >= 0

    def test_n_within_5pct_nonnegative(self, sweep_results):
        for r in sweep_results:
            assert r["n_within_5pct"] >= 0

    def test_epsilon_values_preserved(self, sweep_results):
        epsilons = [r["epsilon"] for r in sweep_results]
        assert 0.0 in epsilons
        assert 0.1 in epsilons
        assert 0.3 in epsilons


# ===========================================================================
# Tests: N_sweep
# ===========================================================================

class TestNSweep:

    @pytest.fixture(scope="class")
    def results(self):
        return N_sweep(
            N_values=[80, 120, 160],
            epsilon=0.3,
            primes_upto=30,
            x_max=13.0,
        )

    def test_result_count(self, results):
        assert len(results) == 3

    def test_result_keys(self, results):
        required = {"N", "mae_base", "mae_corrected", "improvement"}
        for r in results:
            assert required.issubset(r.keys())

    def test_mae_base_positive(self, results):
        for r in results:
            assert r["mae_base"] > 0.0

    def test_correction_positive_improvement(self, results):
        """La corrección debe mejorar respecto a la base en todos los N."""
        improvements = [r["improvement"] for r in results]
        assert all(i > 0 for i in improvements), (
            f"Expected improvement > 0 at all N, got: {improvements}"
        )

    def test_base_converges(self):
        """Error base decrece con N (convergencia de diferencias finitas)."""
        results = N_sweep(
            N_values=[80, 160, 240],
            epsilon=0.0,
            primes_upto=30,
            x_max=13.0,
        )
        maes = [r["mae_base"] for r in results]
        # Error base debería decrecer (o al menos no crecer) al aumentar N
        assert maes[0] >= maes[1] and maes[1] >= maes[2], (
            "El error base debería decrecer al aumentar N"
        )

    def test_N_values_preserved(self, results):
        ns = [r["N"] for r in results]
        assert ns == [80, 120, 160]


# ===========================================================================
# Tests: _check_monotone_decreasing
# ===========================================================================

class TestCheckMonotoneDecreasing:

    def test_strictly_decreasing(self):
        assert _check_monotone_decreasing([3.0, 2.0, 1.0]) is True

    def test_equal_values(self):
        assert _check_monotone_decreasing([2.0, 2.0, 2.0]) is True

    def test_increasing_returns_false(self):
        assert _check_monotone_decreasing([1.0, 2.0, 3.0]) is False

    def test_single_element(self):
        assert _check_monotone_decreasing([5.0]) is True

    def test_empty_list(self):
        assert _check_monotone_decreasing([]) is True


# ===========================================================================
# Tests: N_smooth (from riemann_operator_H)
# ===========================================================================

class TestNSmooth:

    def test_zero_returns_zero(self):
        assert N_smooth(0.0) == 0.0

    def test_negative_returns_zero(self):
        assert N_smooth(-1.0) == 0.0

    def test_positive_and_increasing(self):
        vals = [N_smooth(E) for E in [10.0, 20.0, 30.0, 40.0]]
        assert all(vals[i] < vals[i + 1] for i in range(len(vals) - 1))

    def test_first_zero_approximate(self):
        # N_smooth(14.13) ≈ 0.73 (el primer cero es el nº 1 por convención)
        assert N_smooth(14.13) > 0

    def test_large_E(self):
        val = N_smooth(100.0)
        assert val > 0


# ===========================================================================
# Tests: WuSprungOperator (from riemann_operator_H)
# ===========================================================================

class TestWuSprungOperator:

    @pytest.fixture(scope="class")
    def op(self):
        return WuSprungOperator(N=80, x_max=13.0)

    def test_eigenvalues_sorted(self, op):
        evals = op.eigenvalues()
        assert np.all(np.diff(evals) >= 0)

    def test_eigenvalues_positive(self, op):
        assert np.all(op.eigenvalues(5) > 0)

    def test_compare_to_zeros_returns_mae(self, op):
        _, _, mae = op.compare_to_zeros()
        assert mae > 0

    def test_constructor_raises_N_lt_2(self):
        with pytest.raises(ValueError):
            WuSprungOperator(N=1)

    def test_constructor_raises_x_max_le_0(self):
        with pytest.raises(ValueError):
            WuSprungOperator(x_max=0.0)
