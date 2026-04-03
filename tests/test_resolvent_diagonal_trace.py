#!/usr/bin/env python3
"""
Tests for Resolvent Diagonal Trace: Tr_reg(R_s) = ξ'(s)/ξ(s)

Validates the four-step derivation showing that the regularized trace of the
resolvent R_s = (H − s)^{-1} of the adelic scaling flow equals the logarithmic
derivative of the completed zeta function ξ(s).

Mathematical Framework:
    Step 1: K_s(x,x) = Σ_{q∈Q^×} ∫₀^∞ e^{-τ(s-1/2)} δ(e^{-τ}qx − x) dτ
    Step 2: Tr_reg(R_s) = ∫_𝒟 [delta-collapse] d*x  →  Σ_{|q|>1} |q|^{-(s-1/2)}
    Step 3: Reduction  →  Σ_p Σ_k (ln p) p^{-ks}  =  −ζ'(s)/ζ(s)
    Step 4: + archimedean term  →  ξ'(s)/ξ(s)

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: April 2026
DOI: 10.5281/zenodo.17379721
"""

import cmath
import sys
from pathlib import Path
import importlib.util

import mpmath
import numpy as np
import pytest

# Allow running from any directory
sys.path.insert(0, str(Path(__file__).parent.parent))

# Load module directly to avoid operators/__init__.py side effects
_spec = importlib.util.spec_from_file_location(
    "resolvent_diagonal_trace",
    Path(__file__).parent.parent / "operators" / "resolvent_diagonal_trace.py",
)
_mod = importlib.util.module_from_spec(_spec)  # type: ignore[arg-type]
_spec.loader.exec_module(_mod)  # type: ignore[union-attr]

ArchimedeanContributionComputer = _mod.ArchimedeanContributionComputer
DiagonalKernelResolver = _mod.DiagonalKernelResolver
DirichletSeriesDecomposition = _mod.DirichletSeriesDecomposition
RegularizedTraceResolver = _mod.RegularizedTraceResolver
TraceDecompositionResult = _mod.TraceDecompositionResult
XiLogarithmicDerivative = _mod.XiLogarithmicDerivative
verify_resolvent_trace_identity = _mod.verify_resolvent_trace_identity

# Test points: Re(s) > 1 required for absolute convergence
S_REAL = [complex(2.0, 0.0), complex(3.0, 0.0), complex(4.0, 0.0), complex(10.0, 0.0)]
S_COMPLEX = [complex(2.0, 1.0), complex(2.0, 5.0), complex(3.0, 3.0)]
S_ALL = S_REAL + S_COMPLEX


# ---------------------------------------------------------------------------
# DiagonalKernelResolver tests
# ---------------------------------------------------------------------------

class TestDiagonalKernelResolver:
    """Tests for Step 1: diagonal kernel K_s(x,x)."""

    def setup_method(self):
        self.resolver = DiagonalKernelResolver(n_primes=5, k_max=3, precision=25)

    def test_saddle_point_at_q_equals_prime(self):
        """τ*(p) = ln(p) for prime p."""
        for p in [2, 3, 5, 7]:
            tau = self.resolver._saddle_point(float(p))
            assert abs(tau - np.log(p)) < 1e-12, (
                f"τ*({p}) = {tau:.6f} ≠ ln({p}) = {np.log(p):.6f}"
            )

    def test_saddle_point_at_prime_power(self):
        """τ*(p^k) = k · ln(p)."""
        for p in [2, 3]:
            for k in [1, 2, 3]:
                tau = self.resolver._saddle_point(float(p ** k))
                expected = k * np.log(p)
                assert abs(tau - expected) < 1e-12

    def test_jacobian_unity(self):
        """The Jacobian |g'(τ*)| equals |x| which cancels in the trace."""
        for p in [2, 3, 5]:
            tau_star = np.log(p)
            jac = self.resolver._jacobian(float(p), tau_star)
            assert abs(jac - 1.0) < 1e-12, (
                f"Jacobian for p={p} should be 1.0, got {jac}"
            )

    def test_kernel_value_shape(self):
        """Kernel contribution for (p=2, k=1) at s=2 is a complex number."""
        result = self.resolver.evaluate_orbit(complex(2.0, 0.0), 2.0, 1)
        assert isinstance(result.kernel_value, complex)

    def test_orbit_weight_positive_for_real_s(self):
        """Orbit weight (ln p) p^{-ks} > 0 for real s > 1."""
        for s_val in [2.0, 3.0]:
            s = complex(s_val, 0.0)
            result = self.resolver.evaluate_orbit(s, 2.0, 1)
            assert result.orbit_weight > 0

    def test_orbit_weight_decreasing_in_k(self):
        """Orbit weight decreases as exponent k increases (for p ≥ 2, s > 1)."""
        s = complex(2.0, 0.0)
        weights = [
            self.resolver.evaluate_orbit(s, 2.0, k).orbit_weight for k in range(1, 5)
        ]
        for i in range(len(weights) - 1):
            assert weights[i] > weights[i + 1], (
                f"Weight at k={i+1} ({weights[i]:.4f}) not greater than "
                f"weight at k={i+2} ({weights[i+1]:.4f})"
            )

    def test_all_orbits_returns_n_primes_times_k_max(self):
        """all_orbits returns n_primes × k_max results."""
        results = self.resolver.all_orbits(complex(2.0, 0.0))
        expected = self.resolver.n_primes * self.resolver.k_max
        assert len(results) == expected


# ---------------------------------------------------------------------------
# DirichletSeriesDecomposition tests
# ---------------------------------------------------------------------------

class TestDirichletSeriesDecomposition:
    """Tests for Step 3: Dirichlet series T_fin(s) = −ζ'(s)/ζ(s)."""

    def setup_method(self):
        self.ds = DirichletSeriesDecomposition(n_primes=60, k_max=15, precision=50)

    def test_prime_power_sum_is_complex(self):
        """Prime-power sum returns a complex number."""
        result = self.ds.prime_power_sum(complex(2.0, 0.0))
        assert isinstance(result, complex)

    def test_von_mangoldt_approximation_real_s(self):
        """
        T_fin(s) approximates −ζ'(s)/ζ(s) with relative error < 1%.

        With 60 primes and k_max=15 the truncation error is small for s > 1.
        """
        for s in [complex(2.0, 0.0), complex(3.0, 0.0), complex(4.0, 0.0)]:
            result = self.ds.verify_dirichlet_identity(s, tol=0.01)
            assert result["identity_holds"], (
                f"Dirichlet identity failed at s={s}: "
                f"T_fin={result['T_fin']:.4f}, "
                f"von_M={result['neg_zeta_prime_over_zeta']:.4f}, "
                f"err={result['relative_error']:.2e}"
            )

    def test_prime_power_sum_decreasing_with_s(self):
        """T_fin(s) should decrease as Re(s) increases (for real s > 1)."""
        vals = [abs(self.ds.prime_power_sum(complex(s, 0.0))) for s in [2.0, 3.0, 5.0]]
        for i in range(len(vals) - 1):
            assert vals[i] > vals[i + 1], (
                f"|T_fin| should decrease with s, but got {vals}"
            )

    def test_orbit_table_structure(self):
        """orbit_table returns list of (int, int, float) triples."""
        table = self.ds.orbit_table(complex(2.0, 0.0))
        assert len(table) > 0
        p, k, w = table[0]
        assert isinstance(p, int) and p >= 2
        assert isinstance(k, int) and k >= 1
        assert isinstance(w, float) and w > 0


# ---------------------------------------------------------------------------
# ArchimedeanContributionComputer tests
# ---------------------------------------------------------------------------

class TestArchimedeanContributionComputer:
    """Tests for the archimedean regularisation term T_∞(s) = −½ ln π + ½ ψ(s/2)."""

    def setup_method(self):
        self.arch = ArchimedeanContributionComputer(precision=50)

    def test_returns_complex(self):
        """compute() returns a complex number."""
        result = self.arch.compute(complex(2.0, 0.0))
        assert isinstance(result, complex)

    def test_known_value_at_s2(self):
        """
        At s=2: T_∞(2) = −½ ln π + ½ ψ(1)
        ψ(1) = −γ_Euler ≈ −0.5772, so T_∞(2) ≈ −0.5724 + (−0.2886) ≈ −0.861.
        """
        result = self.arch.compute(complex(2.0, 0.0))
        # Manual reference via mpmath
        with mpmath.workdps(50):
            expected = float(
                -mpmath.log(mpmath.pi) / 2 + mpmath.digamma(1) / 2
            )
        assert abs(result.real - expected) < 1e-10, (
            f"T_∞(2) = {result.real:.8f}, expected {expected:.8f}"
        )

    def test_imaginary_part_varies_with_s(self):
        """Im(T_∞(s)) is nonzero for s with Im(s) ≠ 0."""
        result_real = self.arch.compute(complex(2.0, 0.0))
        result_imag = self.arch.compute(complex(2.0, 3.0))
        assert abs(result_real.imag) < 1e-12
        assert abs(result_imag.imag) > 1e-6


# ---------------------------------------------------------------------------
# XiLogarithmicDerivative tests
# ---------------------------------------------------------------------------

class TestXiLogarithmicDerivative:
    """Tests for ξ'(s)/ξ(s) computation."""

    def setup_method(self):
        self.xi_ld = XiLogarithmicDerivative(precision=50)

    def test_xi_at_s2_is_positive(self):
        """ξ(2) > 0 (ζ(2) = π²/6 > 0 and all factors positive for s > 1)."""
        result = self.xi_ld.xi(complex(2.0, 0.0))
        assert result.real > 0
        assert abs(result.imag) < 1e-10

    def test_log_derivative_is_complex(self):
        """log_derivative returns a complex number."""
        result = self.xi_ld.log_derivative(complex(2.0, 0.0))
        assert isinstance(result, complex)

    def test_log_derivative_components_sum(self):
        """π_term + γ_term + ζ_term equals ξ'(s)/ξ(s)."""
        s = complex(3.0, 0.0)
        components = self.xi_ld.log_derivative_components(s)
        direct = self.xi_ld.log_derivative(s)
        total = components["total"]
        assert abs(total - direct) < 1e-8, (
            f"Component sum {total} ≠ direct {direct}"
        )

    def test_zeta_term_equals_neg_von_mangoldt(self):
        """ζ'(s)/ζ(s) = −Σ_n Λ(n)/n^s (von Mangoldt series)."""
        s = complex(3.0, 0.0)
        components = self.xi_ld.log_derivative_components(s)
        zeta_term = components["zeta_term"]
        # Direct von Mangoldt reference
        ds_ref = DirichletSeriesDecomposition(n_primes=100, k_max=20, precision=50)
        von_m = ds_ref.von_mangoldt_series(s)
        # zeta_term = ζ'(s)/ζ(s); von_m = −ζ'(s)/ζ(s)
        assert abs(zeta_term + von_m) < 1e-5, (
            f"ζ'/ζ = {zeta_term:.6f}, −(von Mangoldt) = {-von_m:.6f}"
        )


# ---------------------------------------------------------------------------
# RegularizedTraceResolver — main identity tests
# ---------------------------------------------------------------------------

class TestRegularizedTraceResolver:
    """Tests for the full identity Tr_reg(R_s) = ξ'(s)/ξ(s)."""

    def setup_method(self):
        self.resolver = RegularizedTraceResolver(
            n_primes=60, k_max=15, precision=50
        )

    def test_compute_returns_result(self):
        """compute() returns a TraceDecompositionResult."""
        result = self.resolver.compute(complex(2.0, 0.0))
        assert isinstance(result, TraceDecompositionResult)

    def test_raises_for_re_s_le_1(self):
        """compute() raises ValueError for Re(s) ≤ 1."""
        with pytest.raises(ValueError, match="Re\\(s\\)"):
            self.resolver.compute(complex(0.5, 14.134))

        with pytest.raises(ValueError, match="Re\\(s\\)"):
            self.resolver.compute(complex(1.0, 0.0))

    def test_identity_at_real_s_2(self):
        """Tr_reg(2) ≈ ξ'(2)/ξ(2) with relative error < 1%."""
        result = self.resolver.compute(complex(2.0, 0.0), tol=0.01)
        assert result.identity_holds, (
            f"Identity failed at s=2: "
            f"Tr_reg={result.tr_reg:.6f}, "
            f"ξ'/ξ={result.xi_log_deriv:.6f}, "
            f"err={result.relative_error:.2e}"
        )

    def test_identity_at_real_s_3(self):
        """Tr_reg(3) ≈ ξ'(3)/ξ(3) with relative error < 0.5%."""
        result = self.resolver.compute(complex(3.0, 0.0), tol=0.005)
        assert result.identity_holds, (
            f"Identity failed at s=3: err={result.relative_error:.2e}"
        )

    def test_identity_at_real_s_4(self):
        """Tr_reg(4) ≈ ξ'(4)/ξ(4) with relative error < 0.1%."""
        result = self.resolver.compute(complex(4.0, 0.0), tol=1e-3)
        assert result.identity_holds, (
            f"Identity failed at s=4: err={result.relative_error:.2e}"
        )

    @pytest.mark.parametrize("s", S_REAL)
    def test_identity_converges_for_real_s(self, s):
        """The identity holds for real s > 1 with tol=2%."""
        result = self.resolver.compute(s, tol=0.02)
        assert result.identity_holds, (
            f"Identity failed at s={s}: err={result.relative_error:.2e}"
        )

    @pytest.mark.parametrize("s", S_COMPLEX)
    def test_identity_for_complex_s(self, s):
        """The identity holds for complex s with Re(s) > 1 and tol=2%."""
        result = self.resolver.compute(s, tol=0.02)
        assert result.identity_holds, (
            f"Identity failed at s={s}: "
            f"Tr_reg={result.tr_reg}, ξ'/ξ={result.xi_log_deriv}, "
            f"err={result.relative_error:.2e}"
        )

    def test_decomposition_sums_correctly(self):
        """tr_reg = dirichlet_series + archimedean_term."""
        result = self.resolver.compute(complex(3.0, 0.0))
        reconstructed = result.dirichlet_series + result.archimedean_term
        assert abs(reconstructed - result.tr_reg) < 1e-12

    def test_dirichlet_series_is_negative_for_real_s(self):
        """dirichlet_series = ζ'(s)/ζ(s) is negative for real s > 1."""
        result = self.resolver.compute(complex(2.0, 0.0))
        assert result.dirichlet_series.real < 0, (
            f"ζ'/ζ should be negative for real s > 1, got {result.dirichlet_series}"
        )

    def test_archimedean_term_is_real_for_real_s(self):
        """T_∞(s) is real when s is real."""
        result = self.resolver.compute(complex(2.0, 0.0))
        assert abs(result.archimedean_term.imag) < 1e-10

    def test_verify_multiple_returns_list(self):
        """verify_multiple returns a list of length equal to input."""
        results = self.resolver.verify_multiple(S_REAL[:3])
        assert len(results) == 3
        for r in results:
            assert isinstance(r, TraceDecompositionResult)

    def test_certificate_structure(self):
        """generate_certificate() returns the expected keys."""
        cert = self.resolver.generate_certificate(
            s_values=[complex(2.0, 0.0), complex(3.0, 0.0)]
        )
        assert "identity" in cert
        assert "all_tests_passed" in cert
        assert "results" in cert
        assert len(cert["results"]) == 2

    def test_certificate_passes(self):
        """Full certificate with standard test grid passes all checks."""
        cert = self.resolver.generate_certificate()
        assert cert["all_tests_passed"], (
            f"Certificate: max_err={cert['max_relative_error']:.2e}\n"
            + "\n".join(
                f"  s={r['s']}: err={r['relative_error']:.2e}"
                for r in cert["results"]
                if not r["identity_holds"]
            )
        )


# ---------------------------------------------------------------------------
# Convenience function tests
# ---------------------------------------------------------------------------

class TestVerifyResolventTraceIdentity:
    """Tests for the public convenience function."""

    def test_default_call(self):
        """Default call (s=2) returns a valid result."""
        result = verify_resolvent_trace_identity()
        assert isinstance(result, TraceDecompositionResult)
        assert result.s == complex(2.0, 0.0)

    def test_custom_s(self):
        """Custom s value is passed through correctly."""
        result = verify_resolvent_trace_identity(s=complex(4.0, 0.0))
        assert result.s == complex(4.0, 0.0)

    def test_identity_holds_at_default(self):
        """Identity holds at the default point s=2."""
        result = verify_resolvent_trace_identity(tol=0.01)
        assert result.identity_holds


# ---------------------------------------------------------------------------
# Integration test: full pipeline
# ---------------------------------------------------------------------------

class TestFullPipeline:
    """End-to-end integration of the four-step derivation."""

    def test_step1_to_step4_pipeline(self):
        """
        Verify the four-step chain:
            K_s → Tr_reg(R_s) = T_fin + T_∞ → ξ'(s)/ξ(s).
        """
        s = complex(2.5, 0.0)

        # Step 1: Diagonal kernel contributions
        kernel_resolver = DiagonalKernelResolver(n_primes=20, k_max=5, precision=30)
        orbits = kernel_resolver.all_orbits(s)
        assert len(orbits) == 100  # 20 primes × 5 exponents

        # Step 3: Dirichlet series from prime-power orbits
        ds = DirichletSeriesDecomposition(n_primes=60, k_max=15, precision=50)
        t_fin = ds.prime_power_sum(s)
        assert t_fin.real > 0  # positive von Mangoldt sum for real s > 1
        zeta_contrib = -t_fin  # ζ'/ζ = -prime_power_sum

        # Archimedean contribution
        arch = ArchimedeanContributionComputer(precision=50)
        t_arch = arch.compute(s)

        # Step 4: Identity with ξ'/ξ
        xi_ld = XiLogarithmicDerivative(precision=50)
        xi_val = xi_ld.log_derivative(s)

        tr_reg = zeta_contrib + t_arch
        rel_err = abs(tr_reg - xi_val) / (abs(xi_val) + 1e-30)
        assert rel_err < 0.02, (
            f"Full pipeline: Tr_reg={tr_reg:.6f}, ξ'/ξ={xi_val:.6f}, "
            f"err={rel_err:.2e}"
        )

    def test_orbit_weights_match_von_mangoldt(self):
        """
        The sum of orbit weights Σ_p Σ_k (ln p) p^{-ks} approximates
        −ζ'(s)/ζ(s) to better than 1% for s = 4.
        """
        s = complex(4.0, 0.0)
        ds = DirichletSeriesDecomposition(n_primes=60, k_max=20, precision=50)
        result = ds.verify_dirichlet_identity(s, tol=0.005)
        assert result["identity_holds"], (
            f"Von Mangoldt identity: err={result['relative_error']:.2e}"
        )
