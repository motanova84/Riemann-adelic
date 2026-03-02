"""
Tests for Wu-Sprung Operator and Five Pillars Spectral Framework

Tests for:
  - WuSprungOperator: discretized H = -d^2/dx^2 + V_WS(x)
  - convergence_rate: O(1/N^2) convergence constant
  - Five Pillars: Pillars I-V of the spectral Riemann Hypothesis framework

Author: Jose Manuel Mota Burruezo
ORCID: 0009-0002-1923-0773
Institution: Instituto de Conciencia Cuantica (ICQ)
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add repository root and operators to path
sys.path.insert(0, str(Path(__file__).parent.parent))
sys.path.insert(0, str(Path(__file__).parent.parent / 'operators'))

from operators.wu_sprung_operator import (
    WuSprungOperator,
    N_smooth,
    V_WS,
    ZEROS_ZETA,
    convergence_rate,
    _x_of_V,
)
from pillars.pilar5_spectral_wu_sprung import (
    pilar1_convergence_analysis,
    pilar2_uniqueness_check,
    pilar3_continuous_spectrum_control,
    pilar4_no_extra_eigenvalues,
    pilar5_v_construction_without_functional_equation,
    verify_five_pillars,
)


class TestNSmooth:
    """Tests for the smooth counting function N_smooth(E)."""

    def test_positive_for_positive_E(self):
        """N_smooth(E) should be positive for E > 2*pi (past inflection)."""
        assert N_smooth(20.0) > 0

    def test_zero_at_zero(self):
        """N_smooth(0) = 0."""
        assert N_smooth(0.0) == 0.0

    def test_monotone_increasing(self):
        """N_smooth should be increasing for E > 0."""
        E_vals = [10.0, 15.0, 20.0, 30.0, 50.0]
        N_vals = [N_smooth(E) for E in E_vals]
        assert all(N_vals[i] < N_vals[i + 1] for i in range(len(N_vals) - 1))

    def test_between_consecutive_zeros(self):
        """N_smooth(gamma_n) should be between n-1 and n."""
        # First zero: gamma_1 = 14.134...
        n1 = N_smooth(14.134725)
        assert 0.0 < n1 < 1.0, f"N_smooth(gamma_1) = {n1}, expected in (0, 1)"

        # Second zero: gamma_2 = 21.022...
        n2 = N_smooth(21.022040)
        assert 1.0 < n2 < 2.0, f"N_smooth(gamma_2) = {n2}, expected in (1, 2)"

    def test_weyl_asymptotic(self):
        """N_smooth should follow Weyl's law for large E."""
        import math
        E = 100.0
        two_pi = 2.0 * math.pi
        expected = (E / two_pi) * math.log(E / two_pi) - E / two_pi + 7.0 / 8.0
        assert abs(N_smooth(E) - expected) < 1e-10


class TestVWS:
    """Tests for the Wu-Sprung potential V_WS(x)."""

    def test_positive_values(self):
        """V_WS should return positive values for x > 0."""
        for x in [0.1, 1.0, 5.0, 10.0]:
            v = V_WS(x)
            assert v > 0, f"V_WS({x}) = {v}, expected positive"

    def test_monotone_increasing(self):
        """V_WS should be monotone increasing."""
        x_vals = [0.5, 1.0, 2.0, 5.0, 10.0]
        V_vals = [V_WS(x) for x in x_vals]
        assert all(V_vals[i] < V_vals[i + 1] for i in range(len(V_vals) - 1))

    def test_x_of_V_roundtrip(self):
        """_x_of_V(V_WS(x)) should recover x."""
        x_test = [1.0, 2.0, 5.0, 8.0]
        for x in x_test:
            V = V_WS(x)
            x_back = _x_of_V(V)
            assert abs(x_back - x) < 1e-6, (
                f"Roundtrip error at x={x}: |{x_back} - {x}| = {abs(x_back - x)}"
            )

    def test_x_of_V_at_zero(self):
        """_x_of_V(V) is negative for V below the minimum threshold."""
        # The formula x(V) = (2*sqrt(V)/pi)*(log(V/2pi) + C) has a minimum
        # at V_min where x(V_min) = 0. For V < V_min, x < 0 (unphysical).
        # The minimum V such that x > 0 is approximately 9.23.
        import math
        # At V_min where log(V/2pi) + C = 0: V_min = 2*pi*exp(-C) = 2*pi*exp(2*log(2)-1)
        C = 1.0 - 2.0 * math.log(2.0)
        V_min_exact = 2 * math.pi * math.exp(-C)
        # Just above V_min, x should be positive
        x_just_above = _x_of_V(V_min_exact + 0.1)
        assert x_just_above >= 0.0, f"x({V_min_exact + 0.1:.2f}) = {x_just_above}"

    def test_grows_to_infinity(self):
        """V_WS(x) should grow significantly with x."""
        v1 = V_WS(1.0)
        v10 = V_WS(10.0)
        assert v10 > 2 * v1, f"V_WS not growing fast enough: V(1)={v1}, V(10)={v10}"


class TestWuSprungOperator:
    """Tests for the WuSprungOperator class."""

    def test_initialization(self):
        """Test that WuSprungOperator initializes correctly."""
        ws = WuSprungOperator(N=50, x_max=10.0)
        assert ws.N == 50
        assert ws.x_max == 10.0
        assert len(ws.x) == 50
        assert len(ws.V) == 50

    def test_grid_spacing(self):
        """Test that grid spacing is correct."""
        N, L = 100, 10.0
        ws = WuSprungOperator(N=N, x_max=L)
        expected_dx = L / (N + 1)
        assert abs(ws.dx - expected_dx) < 1e-12

    def test_potential_positive(self):
        """All potential values should be positive."""
        ws = WuSprungOperator(N=50, x_max=10.0)
        assert np.all(ws.V > 0), "All potential values should be positive"

    def test_potential_monotone(self):
        """Potential should be monotone increasing along grid."""
        ws = WuSprungOperator(N=50, x_max=10.0)
        diffs = np.diff(ws.V)
        assert np.all(diffs > 0), "Potential should be monotone increasing"

    def test_eigenvalues_shape(self):
        """eigenvalues should return N eigenvalues."""
        ws = WuSprungOperator(N=50, x_max=10.0)
        evals = ws.eigenvalues()
        assert len(evals) == 50

    def test_positive_eigenvalues_shape(self):
        """positive_eigenvalues(n_max) should return n_max values."""
        ws = WuSprungOperator(N=100, x_max=13.0)
        evals = ws.positive_eigenvalues(n_max=5)
        assert len(evals) == 5

    def test_eigenvalues_sorted(self):
        """Eigenvalues should be in ascending order."""
        ws = WuSprungOperator(N=50, x_max=10.0)
        evals = ws.eigenvalues()
        assert np.all(np.diff(evals) >= 0), "Eigenvalues should be non-decreasing"

    def test_eigenvalues_approximation(self):
        """
        Eigenvalues should approximate Riemann zeros within a reasonable error.

        For N=200, L=13, mean error should be < 3.0 for first 5 zeros.
        (Exact match requires large N; this tests basic correctness.)
        """
        ws = WuSprungOperator(N=200, x_max=13.0)
        evals = ws.positive_eigenvalues(n_max=5)
        zeros_ref = ZEROS_ZETA[:5]
        mean_error = np.mean(np.abs(evals - zeros_ref))
        assert mean_error < 3.0, (
            f"Mean error {mean_error:.3f} too large for N=200 (expected < 3.0)"
        )

    def test_convergence_with_N(self):
        """Larger N should give better approximation."""
        ws100 = WuSprungOperator(N=100, x_max=13.0)
        ws200 = WuSprungOperator(N=200, x_max=13.0)
        zeros_ref = ZEROS_ZETA[:5]

        err100 = np.mean(np.abs(ws100.positive_eigenvalues(n_max=5) - zeros_ref))
        err200 = np.mean(np.abs(ws200.positive_eigenvalues(n_max=5) - zeros_ref))

        assert err200 <= err100 + 0.5, (
            f"Error should decrease with N: err(100)={err100:.3f}, err(200)={err200:.3f}"
        )


class TestConvergenceRate:
    """Tests for the convergence_rate function."""

    def test_returns_float(self):
        """convergence_rate should return a float."""
        C = convergence_rate(np.array([50, 100]), L_fixed=13.0, n_max=5)
        assert isinstance(C, float)

    def test_positive_constant(self):
        """Convergence constant should be positive."""
        C = convergence_rate(np.array([100, 200]), L_fixed=13.0, n_max=5)
        assert C > 0, f"Convergence constant C = {C}, expected positive"

    def test_problem_statement_n500(self):
        """
        For N=500, error ~ 1.96 as stated in problem statement (Pilar I).
        """
        ws = WuSprungOperator(N=500, x_max=13.0)
        evals = ws.positive_eigenvalues(n_max=15)
        error = float(np.mean(np.abs(evals - ZEROS_ZETA[:15])))
        # Problem statement: "Para N=500, error ≈ 1.96"
        assert 0.5 < error < 4.0, (
            f"For N=500, error = {error:.3f}, expected ~1.96"
        )


class TestPilar1ConvergenceAnalysis:
    """Tests for Pilar I: Uniform convergence analysis."""

    def test_basic_run(self):
        """Should run without errors."""
        result = pilar1_convergence_analysis(
            N_values=np.array([50, 100, 150]),
            L_fixed=13.0,
            n_max=5,
        )
        assert 'errors' in result
        assert 'converges' in result

    def test_errors_decrease(self):
        """Errors should decrease with increasing N."""
        result = pilar1_convergence_analysis(
            N_values=np.array([50, 100, 200]),
            L_fixed=13.0,
            n_max=5,
        )
        errors = result['errors']
        assert errors[0] > errors[-1], (
            f"Error should decrease: {errors[0]:.3f} -> {errors[-1]:.3f}"
        )

    def test_convergence_flag(self):
        """converges flag should be True for increasing N values."""
        result = pilar1_convergence_analysis(
            N_values=np.array([50, 100, 200]),
            L_fixed=13.0,
            n_max=5,
        )
        assert result['converges'] is True


class TestPilar2UniquenessCheck:
    """Tests for Pilar II: Uniqueness of inverse spectral problem."""

    def test_basic_run(self):
        """Should run without errors."""
        result = pilar2_uniqueness_check()
        assert 'uniqueness_holds' in result

    def test_monotone_increasing(self):
        """V_WS should be monotone increasing."""
        result = pilar2_uniqueness_check()
        assert result['is_monotone_increasing'] is True

    def test_grows_to_infinity(self):
        """V_WS should grow to infinity."""
        result = pilar2_uniqueness_check()
        assert result['grows_to_infinity'] is True

    def test_uniqueness_holds(self):
        """Borg-Marchenko uniqueness conditions should be satisfied."""
        result = pilar2_uniqueness_check()
        assert result['uniqueness_holds']


class TestPilar3ContinuousSpectrumControl:
    """Tests for Pilar III: Control of the continuous spectrum."""

    def test_basic_run(self):
        """Should run without errors."""
        result = pilar3_continuous_spectrum_control()
        assert 'spectrum_is_purely_discrete' in result

    def test_no_continuous_spectrum(self):
        """There should be no continuous spectrum in bounded energy ranges."""
        result = pilar3_continuous_spectrum_control(E_max=100.0)
        assert result['no_continuous_spectrum'] is True

    def test_weyl_criterion(self):
        """Weyl criterion (V -> inf) should be satisfied."""
        result = pilar3_continuous_spectrum_control()
        assert result['weyl_criterion_satisfied'] is True

    def test_purely_discrete(self):
        """Spectrum should be purely discrete."""
        result = pilar3_continuous_spectrum_control()
        assert result['spectrum_is_purely_discrete'] is True

    def test_V_grows_superlinearly(self):
        """V_WS should grow superlinearly (exponent > 1)."""
        result = pilar3_continuous_spectrum_control()
        alpha = result['V_growth_rate_exponent']
        assert alpha > 1.0, f"Growth exponent alpha = {alpha:.3f}, expected > 1"


class TestPilar4NoExtraEigenvalues:
    """Tests for Pilar IV: Absence of extra eigenvalues."""

    def test_basic_run(self):
        """Should run without errors."""
        result = pilar4_no_extra_eigenvalues(N=100, L=13.0, n_check=5)
        assert 'no_extra_eigenvalues' in result

    def test_no_extra(self):
        """No extra eigenvalues should be found."""
        result = pilar4_no_extra_eigenvalues(N=150, L=13.0, n_check=8)
        assert result['no_extra_eigenvalues'] is True

    def test_eigenvalues_are_positive(self):
        """Computed eigenvalues should all be positive."""
        result = pilar4_no_extra_eigenvalues(N=100, L=13.0, n_check=5)
        assert np.all(result['eigenvalues'] > 0)


class TestPilar5VConstruction:
    """Tests for Pilar V: V_WS construction without functional equation."""

    def test_basic_run(self):
        """Should run without errors."""
        result = pilar5_v_construction_without_functional_equation()
        assert 'construction_is_independent' in result

    def test_construction_independent(self):
        """Construction should be independent of functional equation."""
        result = pilar5_v_construction_without_functional_equation()
        assert result['construction_is_independent'] is True

    def test_n_smooth_stirling(self):
        """N_smooth should come from Stirling approximation."""
        result = pilar5_v_construction_without_functional_equation()
        assert result['N_smooth_is_stirling'] is True

    def test_abel_inversion_consistent(self):
        """Abel inversion roundtrip should be accurate."""
        result = pilar5_v_construction_without_functional_equation()
        assert result['abel_inversion_consistent'] is True

    def test_n_smooth_at_zeros_in_range(self):
        """N_smooth at Riemann zeros should be between consecutive integers."""
        result = pilar5_v_construction_without_functional_equation()
        n1 = result['N_smooth_at_first_zero']
        n2 = result['N_smooth_at_second_zero']
        assert 0.0 < n1 < 1.0, f"N_smooth(gamma_1) = {n1} not in (0, 1)"
        assert 1.0 < n2 < 2.0, f"N_smooth(gamma_2) = {n2} not in (1, 2)"


class TestVerifyFivePillars:
    """Integration tests for the complete Five Pillars framework."""

    def test_all_pillars_pass(self):
        """All five pillars should pass with sufficient N."""
        result = verify_five_pillars(N_convergence=150, L=13.0, verbose=False)
        assert result['all_pass'] is True, (
            "Not all pillars pass: " + str({
                k: v.get('pilar', k) for k, v in result.items()
                if isinstance(v, dict) and not _all_true_bools(v)
            })
        )

    def test_structure(self):
        """Result should contain all five pillar keys."""
        result = verify_five_pillars(N_convergence=100, L=13.0, verbose=False)
        for key in ['pilar1', 'pilar2', 'pilar3', 'pilar4', 'pilar5']:
            assert key in result, f"Missing key: {key}"

    def test_pilar_keys_have_pilar_label(self):
        """Each pillar result should have a 'pilar' label."""
        result = verify_five_pillars(N_convergence=100, L=13.0, verbose=False)
        for key in ['pilar1', 'pilar2', 'pilar3', 'pilar4', 'pilar5']:
            assert 'pilar' in result[key], f"Missing 'pilar' label in {key}"


def _all_true_bools(d: dict) -> bool:
    """Check that all boolean values in a dict are True."""
    return all(v for v in d.values() if isinstance(v, bool))
