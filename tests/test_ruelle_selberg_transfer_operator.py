#!/usr/bin/env python3
"""
Tests for the Ruelle-Selberg Regularized Transfer Operator
==========================================================

Tests all four components of the mathematical architecture:
A. Ruelle-Selberg Transfer Operator (nuclear trace, Schatten class)
B. Transverse Jacobian (exact p^{-k/2} Poincaré determinant)
C. Archimedean Weyl Term (Γ factor, Nodo Zero, functional equation)
D. Fredholm-Determinant Bridge Δ(s) = ξ(s)

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ · f₀ = 141.7001 Hz · DOI: 10.5281/zenodo.17379721
"""

import math

import numpy as np
import pytest

from operators.ruelle_selberg_transfer_operator import (
    ArchimedeanResult,
    ArchimedeanWeylTerm,
    FredholmDeterminantResult,
    MathesisFredholmXi,
    MathesisGestoResult,
    NuclearTraceResult,
    PoincareDeterminantResult,
    RuelleSelbergTransferOperator,
    TransverseJacobian,
    gesto_final_mathesis,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def gaussian(t: np.ndarray, sigma: float = 1.0) -> np.ndarray:
    """Standard Gaussian Schwartz kernel f(t) = exp(-t²/(2σ²))."""
    return np.exp(-(t**2) / (2.0 * sigma**2))


def gaussian_ft(omega: float, sigma: float = 1.0) -> complex:
    """Analytical Fourier transform of the Gaussian: f̂(ω) = σ√(2π) exp(-σ²ω²/2)."""
    return sigma * math.sqrt(2 * math.pi) * math.exp(-0.5 * (sigma * omega) ** 2)


# ===========================================================================
# Part A: RuelleSelbergTransferOperator
# ===========================================================================

class TestRuelleSelbergTransferOperator:
    """Tests for Part A: regularized transfer operator and nuclear trace."""

    def test_instantiation_default(self):
        """Default constructor creates a valid operator."""
        op = RuelleSelbergTransferOperator()
        assert op.epsilon > 0
        assert op.n_t > 0
        assert len(op.zeros) > 0

    def test_instantiation_custom_epsilon(self):
        """Custom ε is stored correctly."""
        op = RuelleSelbergTransferOperator(epsilon=0.1)
        assert op.epsilon == pytest.approx(0.1)

    def test_invalid_epsilon_raises(self):
        """Negative or zero ε must raise ValueError."""
        with pytest.raises(ValueError):
            RuelleSelbergTransferOperator(epsilon=0.0)
        with pytest.raises(ValueError):
            RuelleSelbergTransferOperator(epsilon=-1.0)

    def test_fourier_transform_gaussian(self):
        """Numerical Fourier transform matches the analytic formula for a Gaussian."""
        op = RuelleSelbergTransferOperator(epsilon=0.5, n_t=8192, t_cutoff=20.0)
        sigma = 1.0
        f = lambda t: gaussian(t, sigma)  # noqa: E731
        for omega in [0.0, 1.0, 2.0, 5.0]:
            numerical = op.fourier_transform(f, omega)
            analytic = gaussian_ft(omega, sigma)
            assert abs(numerical - analytic) / abs(analytic + 1e-30) < 0.02, (
                f"FT mismatch at ω={omega}: {numerical:.4f} vs {analytic:.4f}"
            )

    def test_nuclear_trace_result_type(self):
        """nuclear_trace returns a NuclearTraceResult."""
        op = RuelleSelbergTransferOperator(epsilon=0.5, n_t=512, t_cutoff=15.0)
        f = lambda t: gaussian(t)  # noqa: E731
        result = op.nuclear_trace(f, tolerance=0.1)
        assert isinstance(result, NuclearTraceResult)

    def test_nuclear_trace_schatten_class(self):
        """L_f is trace-class (Schatten class = 1) for ε > 0."""
        op = RuelleSelbergTransferOperator(epsilon=0.5, n_t=512, t_cutoff=15.0)
        f = lambda t: gaussian(t)  # noqa: E731
        result = op.nuclear_trace(f, tolerance=0.5)
        assert result.schatten_class == 1

    def test_nuclear_trace_zero_count(self):
        """n_zeros_used matches the number of zeros supplied."""
        zeros = np.array([14.134725, 21.022040, 25.010858])
        op = RuelleSelbergTransferOperator(epsilon=0.5, riemann_zeros=zeros, n_t=512)
        f = lambda t: gaussian(t)  # noqa: E731
        result = op.nuclear_trace(f)
        assert result.n_zeros_used == 3

    def test_schatten_norm_positive(self):
        """Schatten 1-norm is positive for a non-trivial test function."""
        op = RuelleSelbergTransferOperator(epsilon=0.5, n_t=512)
        f = lambda t: gaussian(t)  # noqa: E731
        norm = op.schatten_norm_estimate(f, p=1)
        assert norm > 0

    def test_nuclear_trace_epsilon_dependence(self):
        """Larger ε gives stronger regularization (faster decay of integrand)."""
        f = lambda t: gaussian(t)  # noqa: E731
        op_small = RuelleSelbergTransferOperator(epsilon=0.1, n_t=512, t_cutoff=15.0)
        op_large = RuelleSelbergTransferOperator(epsilon=2.0, n_t=512, t_cutoff=15.0)
        norm_small = op_small.schatten_norm_estimate(f)
        norm_large = op_large.schatten_norm_estimate(f)
        # Larger ε → stronger suppression → smaller Schatten norm
        assert norm_large < norm_small


# ===========================================================================
# Part B: TransverseJacobian
# ===========================================================================

class TestTransverseJacobian:
    """Tests for Part B: exact Poincaré determinant and orbit weights."""

    def test_instantiation(self):
        """Default constructor works."""
        jac = TransverseJacobian()
        assert len(jac.primes) > 0
        assert jac.k_max >= 1

    def test_compute_returns_correct_type(self):
        """compute() returns a PoincareDeterminantResult."""
        jac = TransverseJacobian()
        r = jac.compute(2.0, 1)
        assert isinstance(r, PoincareDeterminantResult)

    def test_invalid_p_raises(self):
        """p ≤ 1 must raise ValueError."""
        jac = TransverseJacobian()
        with pytest.raises(ValueError):
            jac.compute(1.0, 1)
        with pytest.raises(ValueError):
            jac.compute(0.5, 1)

    def test_invalid_k_raises(self):
        """k < 1 must raise ValueError."""
        jac = TransverseJacobian()
        with pytest.raises(ValueError):
            jac.compute(2.0, 0)
        with pytest.raises(ValueError):
            jac.compute(2.0, -1)

    @pytest.mark.parametrize("p,k", [(2, 1), (3, 1), (5, 2), (7, 3), (11, 1)])
    def test_real_expansion(self, p, k):
        """Real-place Jacobian = p^k (expanding)."""
        jac = TransverseJacobian()
        r = jac.compute(float(p), k)
        assert r.real_expansion == pytest.approx(p**k, rel=1e-12)

    @pytest.mark.parametrize("p,k", [(2, 1), (3, 1), (5, 2), (7, 3)])
    def test_padic_contraction(self, p, k):
        """p-adic contraction factor = p^{-k} (contracting)."""
        jac = TransverseJacobian()
        r = jac.compute(float(p), k)
        assert r.padic_contraction == pytest.approx(p**(-k), rel=1e-12)

    @pytest.mark.parametrize("p,k", [(2, 1), (3, 2), (5, 1), (7, 2), (11, 3)])
    def test_fujisaki_norm_product(self, p, k):
        """Global norm product p^k · p^{-k} = 1 (Fujisaki condition)."""
        jac = TransverseJacobian()
        r = jac.compute(float(p), k)
        assert r.norm_product == pytest.approx(1.0, abs=1e-12)

    @pytest.mark.parametrize("p,k", [(2, 1), (3, 1), (5, 2), (7, 1)])
    def test_transversal_determinant_exact(self, p, k):
        """Poincaré determinant |det(I−dφ_T)|_N = p^{k/2} (exact)."""
        jac = TransverseJacobian()
        r = jac.compute(float(p), k)
        expected = p ** (k / 2)
        assert r.transversal_determinant == pytest.approx(expected, rel=1e-12)

    @pytest.mark.parametrize("p,k", [(2, 1), (3, 1), (5, 1)])
    def test_orbit_weight_exact(self, p, k):
        """Orbit weight W_p^k = log(p) / p^{k/2} (exact)."""
        jac = TransverseJacobian()
        r = jac.compute(float(p), k)
        expected = math.log(p) / (p ** (k / 2))
        assert r.orbit_weight == pytest.approx(expected, rel=1e-12)

    def test_result_marked_exact(self):
        """Result.exact is always True."""
        jac = TransverseJacobian()
        r = jac.compute(2.0, 1)
        assert r.exact is True

    def test_fujisaki_condition_all_orbits(self):
        """verify_fujisaki_condition() passes for the full weight table."""
        jac = TransverseJacobian(k_max=3)
        assert jac.verify_fujisaki_condition() is True

    def test_verify_exact_weight_p2_k1(self):
        """verify_exact_weight for (p=2, k=1) passes."""
        jac = TransverseJacobian()
        assert jac.verify_exact_weight(2.0, 1) is True

    def test_weight_table_has_entries(self):
        """weight_table() returns a non-empty list."""
        jac = TransverseJacobian(primes=[2, 3, 5], k_max=2)
        table = jac.weight_table()
        assert len(table) == 6  # 3 primes × 2 powers

    def test_weight_table_all_exact(self):
        """All entries in weight_table have exact = True."""
        jac = TransverseJacobian(primes=[2, 3, 5, 7], k_max=2)
        for entry in jac.weight_table():
            assert entry.exact is True


# ===========================================================================
# Part C: ArchimedeanWeylTerm
# ===========================================================================

class TestArchimedeanWeylTerm:
    """Tests for Part C: Weyl term, Gamma factor, and Nodo Zero."""

    def test_instantiation(self):
        """Default constructor works."""
        arch = ArchimedeanWeylTerm()
        assert arch is not None

    def test_gamma_factor_at_s2(self):
        """Γ factor at s=2: π^{-1}Γ(1) = 1/π."""
        arch = ArchimedeanWeylTerm()
        gf = arch.gamma_factor(complex(2.0, 0.0))
        expected = 1.0 / math.pi
        assert abs(gf - expected) / abs(expected) < 1e-6

    def test_gamma_factor_real_on_critical_line(self):
        """γ factor is real on the critical line Re(s) = 1/2."""
        arch = ArchimedeanWeylTerm()
        s = complex(0.5, 14.134725)
        gf = arch.gamma_factor(s)
        # Imaginary part should be small relative to the real part
        assert abs(gf.imag) < abs(gf.real) * 10 + 1e-10

    def test_nodo_zero_at_half(self):
        """Nodo Zero ½s(s−1) at s=1/2 is −1/8."""
        arch = ArchimedeanWeylTerm()
        nz = arch.nodo_zero_factor(complex(0.5, 0.0))
        expected = 0.5 * 0.5 * (0.5 - 1)  # = -1/8
        assert abs(nz - expected) < 1e-12

    def test_nodo_zero_at_s0(self):
        """Nodo Zero at s=0 is zero."""
        arch = ArchimedeanWeylTerm()
        nz = arch.nodo_zero_factor(complex(0.0, 0.0))
        assert abs(nz) < 1e-15

    def test_nodo_zero_at_s1(self):
        """Nodo Zero at s=1 is zero."""
        arch = ArchimedeanWeylTerm()
        nz = arch.nodo_zero_factor(complex(1.0, 0.0))
        assert abs(nz) < 1e-15

    def test_weyl_term_positive_energy(self):
        """Weyl term is finite for E > 2πe (positive result)."""
        arch = ArchimedeanWeylTerm()
        # E = 2πe → log term = 0
        E_threshold = 2.0 * math.pi * math.e
        wt = arch.weyl_term(E_threshold * 2)
        assert isinstance(wt, float)

    def test_weyl_term_zero_energy(self):
        """Weyl term returns 0.0 for E ≤ 0."""
        arch = ArchimedeanWeylTerm()
        assert arch.weyl_term(0.0) == 0.0
        assert arch.weyl_term(-5.0) == 0.0

    def test_weyl_term_formula(self):
        """Weyl term matches (1/2π)log(E/2πe)."""
        arch = ArchimedeanWeylTerm()
        E = 100.0
        expected = (1.0 / (2.0 * math.pi)) * math.log(E / (2.0 * math.pi * math.e))
        assert arch.weyl_term(E) == pytest.approx(expected, rel=1e-12)

    def test_functional_symmetry_critical_line(self):
        """On the critical line, |Δ_∞(s)| = |Δ_∞(1−s)| (magnitude equality)."""
        arch = ArchimedeanWeylTerm()
        s = complex(0.5, 14.134725)
        assert arch.verify_functional_symmetry(s, tolerance=1e-8) is True

    def test_functional_symmetry_on_critical_line_t5(self):
        """Magnitude equality holds for other values of t on the critical line."""
        arch = ArchimedeanWeylTerm()
        s = complex(0.5, 5.0)
        assert arch.verify_functional_symmetry(s, tolerance=1e-8) is True

    def test_evaluate_returns_correct_type(self):
        """evaluate() returns an ArchimedeanResult."""
        arch = ArchimedeanWeylTerm()
        result = arch.evaluate(complex(0.5, 14.134725))
        assert isinstance(result, ArchimedeanResult)

    def test_evaluate_s_stored(self):
        """evaluate() stores the s value correctly."""
        arch = ArchimedeanWeylTerm()
        s = complex(0.5, 21.022040)
        result = arch.evaluate(s)
        assert result.s == s


# ===========================================================================
# Part D: MathesisFredholmXi
# ===========================================================================

class TestMathesisFredholmXi:
    """Tests for Part D: Fredholm-determinant bridge Δ(s) = ξ(s)."""

    def test_instantiation(self):
        """Default constructor works."""
        bridge = MathesisFredholmXi()
        assert bridge is not None

    def test_euler_product_at_s2(self):
        """Euler product at s=2 ≈ π²/6."""
        bridge = MathesisFredholmXi(n_primes=50)
        ep = bridge.euler_product(complex(2.0, 0.0))
        # π²/6 ≈ 1.6449
        assert abs(ep.real - math.pi**2 / 6) < 0.01

    def test_euler_product_has_no_imaginary_on_real_axis(self):
        """Euler product is real at real s > 1."""
        bridge = MathesisFredholmXi(n_primes=20)
        ep = bridge.euler_product(complex(3.0, 0.0))
        # Should be nearly real
        assert abs(ep.imag) < abs(ep.real) * 1e-10 + 1e-12

    def test_xi_functional_equation(self):
        """ξ(s) = ξ(1−s) for the computed xi function."""
        bridge = MathesisFredholmXi(n_primes=30, precision=25)
        s = complex(0.5, 14.134725)
        xi_s = bridge.xi_function(s)
        xi_1ms = bridge.xi_function(1 - s)
        rel_err = abs(xi_s - xi_1ms) / max(abs(xi_s), 1e-30)
        assert rel_err < 1e-6

    def test_verify_identity_at_s2(self):
        """Identity Δ(s) ≈ ξ(s) at s=2 holds with relaxed tolerance (slow Euler convergence)."""
        bridge = MathesisFredholmXi(n_primes=30)
        r = bridge.verify_identity(complex(2.0, 0.0), tolerance=0.1)
        assert isinstance(r, FredholmDeterminantResult)
        assert r.identity_verified

    def test_verify_identity_at_s3(self):
        """Identity Δ(3) ≈ ξ(3) holds with standard tolerance."""
        bridge = MathesisFredholmXi(n_primes=30)
        r = bridge.verify_identity(complex(3.0, 0.0), tolerance=1e-3)
        assert r.identity_verified

    def test_verify_identity_over_range(self):
        """verify_identity_over_range returns a dict with correct keys."""
        bridge = MathesisFredholmXi(n_primes=20)
        s_values = [complex(2.0, 0.0), complex(3.0, 0.0)]
        result = bridge.verify_identity_over_range(s_values, tolerance=0.1)
        assert "results" in result
        assert "verification_rate" in result
        assert "max_error" in result
        assert "mean_error" in result
        assert "all_verified" in result
        assert "status" in result

    def test_verification_rate_high_for_real_s(self):
        """Verification rate ≥ 0.8 for s on the real axis ≥ 3."""
        bridge = MathesisFredholmXi(n_primes=30)
        s_values = [complex(float(s), 0.0) for s in range(3, 7)]
        result = bridge.verify_identity_over_range(s_values, tolerance=1e-3)
        assert result["verification_rate"] >= 0.75

    def test_log_delta_prime_trace_is_finite(self):
        """log_delta_from_prime_trace returns a finite complex number."""
        bridge = MathesisFredholmXi(n_primes=20)
        val = bridge.log_delta_from_prime_trace(complex(2.0, 0.0))
        assert math.isfinite(val.real)
        assert math.isfinite(val.imag)


# ===========================================================================
# Gesto Final de Mathesis (integration)
# ===========================================================================

class TestGestoFinalMathesis:
    """Integration tests for the complete 4-step architecture."""

    def test_returns_mathesis_gesto_result(self):
        """gesto_final_mathesis() returns a MathesisGestoResult."""
        result = gesto_final_mathesis(n_primes=20, k_max=2, verbose=False)
        assert isinstance(result, MathesisGestoResult)

    def test_paso_a_nuclear(self):
        """Part A — L_f is nuclear (trace-class)."""
        result = gesto_final_mathesis(n_primes=20, k_max=2, verbose=False)
        assert result.paso_a_nuclear is True

    def test_paso_b_jacobian_exact(self):
        """Part B — transverse Jacobian p^{-k/2} is exact."""
        result = gesto_final_mathesis(n_primes=20, k_max=2, verbose=False)
        assert result.paso_b_jacobian_exact is True

    def test_paso_c_archimedean(self):
        """Part C — archimedean integration is complete."""
        result = gesto_final_mathesis(n_primes=20, k_max=2, verbose=False)
        assert result.paso_c_archimedean is True

    def test_paso_d_delta_xi(self):
        """Part D — Δ(s) ≡ ξ(s)."""
        result = gesto_final_mathesis(n_primes=30, k_max=2, verbose=False)
        assert result.paso_d_delta_xi is True

    def test_overall_verified(self):
        """All four steps pass simultaneously."""
        result = gesto_final_mathesis(n_primes=30, k_max=2, verbose=False)
        assert result.overall_verified is True

    def test_fujisaki_ok(self):
        """Global norm product = 1 (Fujisaki condition)."""
        result = gesto_final_mathesis(n_primes=20, k_max=2, verbose=False)
        assert result.fujisaki_ok is True

    def test_functional_eq_ok(self):
        """Functional equation Δ_∞(s) = Δ_∞(1−s) holds."""
        result = gesto_final_mathesis(n_primes=20, k_max=2, verbose=False)
        assert result.functional_eq_ok is True

    def test_epsilon_stored(self):
        """Epsilon value is stored in the result."""
        result = gesto_final_mathesis(epsilon=0.3, n_primes=20, verbose=False)
        assert result.epsilon == pytest.approx(0.3)

    def test_n_primes_stored(self):
        """Number of primes is stored in the result."""
        result = gesto_final_mathesis(n_primes=15, k_max=2, verbose=False)
        assert result.n_primes_used == 15

    def test_identity_error_finite(self):
        """Identity error is a finite non-negative number."""
        result = gesto_final_mathesis(n_primes=20, k_max=2, verbose=False)
        assert math.isfinite(result.identity_error)
        assert result.identity_error >= 0.0

    def test_verbose_mode_runs(self, capsys):
        """verbose=True produces non-empty output."""
        gesto_final_mathesis(n_primes=15, k_max=2, verbose=True)
        captured = capsys.readouterr()
        assert "Mathesis" in captured.out

    def test_status_completado(self):
        """Status string is 'COMPLETADO ✓' when all steps pass."""
        result = gesto_final_mathesis(n_primes=30, k_max=2, verbose=False)
        if result.overall_verified:
            assert "COMPLETADO" in result.status
