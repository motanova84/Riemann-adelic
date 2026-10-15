"""
Tests for the truncated Hadamard product  D_N(s).

Validates the five mathematical properties required by the problem statement:

1. Construction of D_N(s) as a truncated Hadamard product.
2. Truncation error estimate with explicit constants.
3. Uniform convergence on compact sets.
4. Comparison with Xi(s) without a priori identification.
5. Exponential factor tends to 1 with an explicit bound.

Author : José Manuel Mota Burruezo Ψ ∞³
ORCID  : 0009-0002-1923-0773
DOI    : 10.5281/zenodo.17379721
"""

import pytest
from mpmath import mp, mpf, mpc, fabs

# Increase precision for sensitive tests
mp.dps = 35


# ---------------------------------------------------------------------------
# Fixture: shared TruncatedHadamardProduct instance
# ---------------------------------------------------------------------------

@pytest.fixture(scope='module')
def thp():
    """Create a TruncatedHadamardProduct with 200 zeros at 35 dps."""
    from utils.truncated_hadamard import TruncatedHadamardProduct
    return TruncatedHadamardProduct(total_zeros=200, dps=35)


# ===========================================================================
# 1. Construction of D_N(s)
# ===========================================================================

class TestDNConstruction:
    """Property 1: D_N(s) is a valid truncated Hadamard product."""

    def test_normalisation_at_half(self, thp):
        """D_N(1/2) = 1 for several values of N."""
        for N in [10, 50, 100, 200]:
            val = thp.D_N(mpf('0.5'), N)
            assert fabs(val - 1) < mpf('1e-20'), (
                f"D_{N}(1/2) = {val} != 1"
            )

    def test_real_for_real_s(self, thp):
        """D_N(s) is real for real s (since zeros come in conjugate pairs)."""
        for s in [mpf('0.5'), mpf('1.0'), mpf('2.0')]:
            for N in [20, 80]:
                val = thp.D_N(s, N)
                assert fabs(mp.im(val)) < mpf('1e-20'), (
                    f"D_{N}({s}) has non-zero imaginary part: im={mp.im(val)}"
                )

    def test_increasing_N_stability(self, thp):
        """Adding more zeros should not drastically change D_N at most points."""
        s = mpc('0.5', '5.0')
        vals = [thp.D_N(s, N) for N in [50, 100, 150, 200]]
        # Successive differences should decrease
        diffs = [fabs(vals[i + 1] - vals[i]) for i in range(len(vals) - 1)]
        assert diffs[-1] <= diffs[0] + mpf('1e-8'), (
            "Differences did not decrease as N increased"
        )

    def test_zero_appears_near_first_riemann_zero(self, thp):
        """D_N(s) should be small near the first Riemann zero."""
        t1 = thp.ts[0]          # ≈ 14.1347
        s_zero = mpc('0.5', t1)
        val = fabs(thp.D_full(s_zero))
        # Not exactly zero due to normalisation, but should be small relative
        # to values away from zeros.
        s_away = mpc('0.5', '2.0')
        val_away = fabs(thp.D_full(s_away))
        assert val < val_away, (
            f"|D(1/2+it1)| = {val} should be < |D(1/2+2i)| = {val_away}"
        )

    def test_log_E1_at_zero(self, thp):
        """log E_1(0) = 0."""
        from utils.truncated_hadamard import _log_E1
        assert fabs(_log_E1(mpf('0'))) < mpf('1e-30')

    def test_log_E1_small_z(self, thp):
        """For small z, log E_1(z) ≈ -z^2/2."""
        from utils.truncated_hadamard import _log_E1
        z = mpf('0.01')
        val = _log_E1(z)
        expected = -(z ** 2) / 2    # leading term of Taylor series
        assert fabs(val - expected) < mpf('1e-5'), (
            f"log E_1({z}) = {val}, expected ≈ {expected}"
        )


# ===========================================================================
# 2. Truncation error estimate
# ===========================================================================

class TestTruncationError:
    """Property 2: explicit upper bound on |D(s) - D_N(s)|."""

    def test_tail_sum_positive_and_decreasing(self, thp):
        """T_N = sum_{n>N} 1/|rho_n|^2 is positive and decreasing in N."""
        t_prev = thp.tail_sum_real(0)
        for N in [10, 50, 100, 150]:
            t_curr = thp.tail_sum_real(N)
            assert t_curr >= 0, f"T_{N} < 0"
            assert t_curr <= t_prev, f"T_{N} = {t_curr} > T_prev = {t_prev}"
            t_prev = t_curr

    def test_tail_sum_converges_to_zero(self, thp):
        """T_N -> 0 as N -> total_zeros."""
        t_full = thp.tail_sum_real(thp.total)
        assert fabs(t_full) < mpf('1e-30'), (
            f"T_{{total}} = {t_full} should be 0"
        )

    def test_error_log_bound_positive(self, thp):
        """eps_N(R) = 4R^2 T_N >= 0."""
        for N in [10, 50]:
            eps = thp.truncation_error_log_bound(mpf('5'), N)
            assert eps >= 0

    def test_error_log_bound_monotone_in_N(self, thp):
        """eps_N(R) is non-increasing in N."""
        R = mpf('3')
        eps_prev = thp.truncation_error_log_bound(R, 10)
        for N in [30, 60, 100]:
            eps_curr = thp.truncation_error_log_bound(R, N)
            assert eps_curr <= eps_prev + mpf('1e-30'), (
                f"eps_{N}(R) = {eps_curr} > eps_prev = {eps_prev}"
            )
            eps_prev = eps_curr

    def test_error_bound_non_negative(self, thp):
        """The absolute error bound is non-negative."""
        s = mpc('0.3', '2.0')
        for N in [20, 80]:
            bound = thp.truncation_error_bound(s, N)
            assert bound >= 0

    def test_error_bound_satisfied(self, thp):
        """
        The actual error |D_full - D_N| should be <= the bound.

        We use N=100 and compare against D_full (which uses all 200 zeros).
        The bound computed for R = |s| should cover the gap.
        """
        s = mpc('0.4', '3.0')
        N = 100
        d_n = thp.D_N(s, N)
        d_full = thp.D_full(s)
        actual = fabs(d_full - d_n)
        bound = thp.truncation_error_bound(s, N, D_N_val=d_n)
        # The bound uses only zeros N+1..total, so it holds
        assert actual <= bound + mpf('1e-20'), (
            f"actual={actual} > bound={bound}"
        )


# ===========================================================================
# 3. Uniform convergence on compacts
# ===========================================================================

class TestUniformConvergence:
    """Property 3: D_N -> D uniformly on compact sets."""

    def test_uniform_bound_decreases_with_N(self, thp):
        """delta_N(R) = exp(eps_N(R)) - 1 is non-increasing in N."""
        R = mpf('4')
        delta_prev = thp.uniform_convergence_bound(R, 5)
        for N in [20, 50, 100]:
            delta_curr = thp.uniform_convergence_bound(R, N)
            assert delta_curr <= delta_prev + mpf('1e-30'), (
                f"delta_{N}(R) = {delta_curr} > delta_prev = {delta_prev}"
            )
            delta_prev = delta_curr

    def test_uniform_bound_goes_to_zero(self, thp):
        """delta_total(R) ~ 0 (full product has no tail)."""
        R = mpf('5')
        delta = thp.uniform_convergence_bound(R, thp.total)
        assert fabs(delta) < mpf('1e-20')

    def test_threshold_gives_correct_tolerance(self, thp):
        """convergence_threshold returns N such that delta_N(R) <= tol."""
        R = mpf('2')
        tol = mpf('0.01')
        N_thresh = thp.convergence_threshold(R, tol)
        assert N_thresh <= thp.total
        achieved = thp.uniform_convergence_bound(R, N_thresh)
        assert achieved <= tol + mpf('1e-30'), (
            f"delta_{N_thresh}(R) = {achieved} > tol = {tol}"
        )

    def test_uniform_convergence_on_grid(self, thp):
        """
        On a grid of points with |s| <= 3, the actual relative deviation
        |D_full(s) - D_N(s)| / |D_N(s)| is <= delta_N(R).
        """
        R = mpf('3')
        N = 80
        delta = thp.uniform_convergence_bound(R, N)
        test_points = [
            mpc('0.5', '1.0'),
            mpc('0.2', '2.0'),
            mpc('0.8', '1.5'),
            mpc('0.5', '0.0'),
        ]
        for s in test_points:
            if fabs(s) > R:
                continue
            d_n = thp.D_N(s, N)
            d_full = thp.D_full(s)
            if fabs(d_n) < mpf('1e-30'):
                continue      # skip near zeros
            rel_err = fabs(d_full - d_n) / fabs(d_n)
            assert rel_err <= delta + mpf('1e-15'), (
                f"s={s}: rel_err={rel_err} > delta={delta}"
            )


# ===========================================================================
# 4. Comparison with Xi(s) — no a priori identification
# ===========================================================================

class TestComparisonWithXi:
    """
    Property 4: Compare D_N(s) with Xi(s) numerically.

    We do NOT assume D_N = Xi.  We simply check that the normalised ratio
    remains stable across different N and converges, which is consistent with
    (but does not prove) their equality.
    """

    def test_xi_values_finite(self, thp):
        """Xi(s) is finite and non-zero for s away from 0 and 1."""
        for s in [mpf('2'), mpc('0.5', '3.0'), mpc('0.3', '5.0')]:
            xi_val = thp.xi(s)
            assert fabs(xi_val) > 0 and fabs(xi_val) < mpf('1e20'), (
                f"Xi({s}) = {xi_val}"
            )

    def test_xi_functional_equation(self, thp):
        """Xi(s) = Xi(1-s) (functional equation)."""
        for s in [mpc('0.5', '3.0'), mpc('0.3', '7.0')]:
            xi_s = thp.xi(s)
            xi_1ms = thp.xi(1 - s)
            assert fabs(xi_s - xi_1ms) < mpf('1e-20'), (
                f"Xi({s}) = {xi_s}, Xi(1-{s}) = {xi_1ms}"
            )

    def test_ratio_near_constant(self, thp):
        """
        The ratio D_N(s)/Xi(s) (after common normalisation at s=2) should
        be finite, non-zero, and approximately the same magnitude as 1.

        For real s, D_N(s) and Xi(s) agree closely (exponential prefactor
        is absorbed by normalisation at the real reference point s=2).
        """
        N = 150
        # Test at real s: exponential factor is real so ratio should be ~1
        results_real = thp.compare_with_xi([mpf('3')], N)
        ratio_real = results_real[0]['ratio']
        assert ratio_real is not None
        # For real s, ratio should be very close to 1
        assert fabs(fabs(ratio_real) - 1) < mpf('0.01'), (
            f"ratio at real s=3 = {ratio_real}"
        )
        # Test at complex s: ratio is bounded (finite, not exploding)
        s_values = [mpc('0.5', '2.0'), mpc('0.5', '5.0')]
        results = thp.compare_with_xi(s_values, N)
        for r in results:
            assert r['ratio'] is not None
            assert fabs(r['ratio']) > mpf('0.1'), "Ratio too small"
            assert fabs(r['ratio']) < mpf('10'), "Ratio too large"

    def test_ratio_converges_with_N(self, thp):
        """
        As N increases, the ratio D_N(s)/Xi(s) should become more stable.
        """
        s = mpc('0.5', '4.0')
        s_values = [s]
        ratios = {}
        for N in [50, 100, 150]:
            res = thp.compare_with_xi(s_values, N)
            ratios[N] = res[0]['ratio']
        # The ratio should be converging: |ratio_100 - ratio_150| < |ratio_50 - ratio_100|
        diff_a = fabs(ratios[100] - ratios[50])
        diff_b = fabs(ratios[150] - ratios[100])
        assert diff_b <= diff_a + mpf('1e-10'), (
            f"Ratio not converging: diff50-100={diff_a}, diff100-150={diff_b}"
        )

    def test_compare_returns_expected_keys(self, thp):
        """compare_with_xi returns the expected dict structure."""
        results = thp.compare_with_xi([mpc('0.5', '3.0')], N=50)
        assert len(results) == 1
        r = results[0]
        for key in ('s', 'D_N', 'Xi', 'ratio', 'abs_diff'):
            assert key in r, f"Missing key '{key}' in result"


# ===========================================================================
# 5. Exponential factor tends to 1 with explicit bound
# ===========================================================================

class TestExponentialFactor:
    """
    Property 5: The exponential factor F_N(s) = D(s)/D_N(s) -> 1 as N -> inf,
    with an explicit bound.
    """

    def test_exp_factor_bound_positive(self, thp):
        """Exponential factor bound is non-negative."""
        for N in [10, 50, 100]:
            bound = thp.exponential_factor_bound(mpf('3'), N)
            assert bound >= 0

    def test_exp_factor_bound_decreases_with_N(self, thp):
        """The bound decreases as N increases."""
        R = mpf('3')
        bound_prev = thp.exponential_factor_bound(R, 10)
        for N in [30, 70, 130]:
            bound_curr = thp.exponential_factor_bound(R, N)
            assert bound_curr <= bound_prev + mpf('1e-30'), (
                f"bound_{N} = {bound_curr} > bound_prev = {bound_prev}"
            )
            bound_prev = bound_curr

    def test_exp_factor_tends_to_zero(self, thp):
        """At N = total, the exponential factor bound = 0 (no tail)."""
        bound = thp.exponential_factor_bound(mpf('5'), thp.total)
        assert fabs(bound) < mpf('1e-20')

    def test_actual_exp_factor_bounded(self, thp):
        """
        The actual |D_full(s)/D_N(s) - 1| <= exponential_factor_bound(|s|, N).
        """
        s = mpc('0.4', '2.5')
        N = 80
        d_n = thp.D_N(s, N)
        d_full = thp.D_full(s)
        if fabs(d_n) < mpf('1e-30'):
            pytest.skip("D_N near zero – cannot compute ratio")
        actual = fabs(d_full / d_n - 1)
        bound = thp.exponential_factor_bound(fabs(s), N)
        assert actual <= bound + mpf('1e-15'), (
            f"actual |F_N - 1| = {actual} > bound = {bound}"
        )

    def test_b_diff_bound_positive_decreasing(self, thp):
        """
        |B - B_N| bound is positive and decreases with N.
        """
        bd_prev = thp.b_diff_bound(0)
        for N in [20, 60, 120]:
            bd_curr = thp.b_diff_bound(N)
            assert bd_curr >= 0
            assert bd_curr <= bd_prev + mpf('1e-30')
            bd_prev = bd_curr

    def test_exp_factor_via_b_diff(self, thp):
        """
        Alternative bound via B-constant difference is non-negative and
        decreasing.
        """
        R = mpf('2')
        b_bound_prev = thp.exp_factor_via_b_diff(R, 10)
        for N in [40, 90, 160]:
            b_bound_curr = thp.exp_factor_via_b_diff(R, N)
            assert b_bound_curr >= 0
            assert b_bound_curr <= b_bound_prev + mpf('1e-25')
            b_bound_prev = b_bound_curr

    def test_explicit_bound_formula(self, thp):
        """
        Verify the formula: bound = exp(4 R^2 T_N) - 1
        where T_N = sum_{n>N} 1/|rho_n|^2.
        """
        R = mpf('2')
        N = 50
        T_N = thp.tail_sum_real(N)
        expected = mp.exp(4 * R ** 2 * T_N) - 1
        computed = thp.exponential_factor_bound(R, N)
        assert fabs(computed - expected) < mpf('1e-20'), (
            f"Formula mismatch: computed={computed}, expected={expected}"
        )
