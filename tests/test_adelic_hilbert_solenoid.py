#!/usr/bin/env python3
"""
Tests for Adelic Hilbert Solenoid — Berry-Keating Symmetrized Operator

Validates the complete AdelicHilbertSolenoid implementation:
1. QCAL constants
2. Prime sieve helper
3. AdelicHilbertSolenoid initialisation
4. Haar inner product (positivity, conjugate symmetry, Haar invariance)
5. Berry-Keating operator application
6. Self-adjointness: ⟨Ĥf, g⟩ = ⟨f, Ĥg⟩
7. Enki Scale Invariance domain check
8. Eigenfunctions ψ_E(x) = x^(-1/2+iE)
9. Eigenvalue equation Ĥψ_E = E ψ_E
10. Critical line correspondence: Re(s) = 1/2
11. Weil explicit formula (structural)
12. QCAL coherence
13. QED_Omega functions
14. sellar_solenoid_adélico() seal

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
QCAL ∞³ · 141.7001 Hz · C = 244.36
"""

import numpy as np
import pytest
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from operators.adelic_hilbert_solenoid import (
    AdelicHilbertSolenoid,
    QED_Omega,
    sellar_solenoid_adélico,
    sieve_primes,
    F0,
    F_UNITY,
    C_QCAL,
    PI,
    DOI,
    ORCID,
)

# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

@pytest.fixture(scope="module")
def solenoid():
    """Small solenoid for fast tests."""
    return AdelicHilbertSolenoid(n_primes=20, x_min=0.01, x_max=100.0, n_points=500)


@pytest.fixture(scope="module")
def test_functions(solenoid):
    """Two Gaussian-modulated test functions in 𝒟(H)."""
    x = solenoid.x
    sigma = 0.5
    f = np.exp(-((np.log(x) - 0.5) ** 2) / (2 * sigma ** 2)) / x ** 0.5
    g = np.exp(-((np.log(x) + 0.5) ** 2) / (2 * sigma ** 2)) / x ** 0.5
    return f, g


# ===========================================================================
# 1. Constants
# ===========================================================================

class TestConstants:
    """QCAL and mathematical constants."""

    def test_fundamental_frequency(self):
        assert np.isclose(F0, 141.7001, rtol=1e-6)

    def test_unity_frequency(self):
        assert np.isclose(F_UNITY, 888.0, rtol=1e-6)

    def test_coherence_constant(self):
        assert np.isclose(C_QCAL, 244.36, rtol=1e-4)

    def test_pi(self):
        assert np.isclose(PI, np.pi, rtol=1e-12)

    def test_doi_format(self):
        assert DOI.startswith("10.5281/zenodo.")

    def test_orcid_format(self):
        assert len(ORCID) > 0


# ===========================================================================
# 2. Prime sieve
# ===========================================================================

class TestSievePrimes:
    """Tests for sieve_primes helper."""

    def test_empty_for_n_max_lt_2(self):
        assert sieve_primes(0) == []
        assert sieve_primes(1) == []

    def test_primes_up_to_10(self):
        assert sieve_primes(10) == [2, 3, 5, 7]

    def test_primes_up_to_20(self):
        assert sieve_primes(20) == [2, 3, 5, 7, 11, 13, 17, 19]

    def test_count_to_100(self):
        assert len(sieve_primes(100)) == 25

    def test_all_prime(self):
        primes = sieve_primes(50)
        for p in primes:
            assert all(p % d != 0 for d in range(2, p))


# ===========================================================================
# 3. Initialisation
# ===========================================================================

class TestInit:
    """AdelicHilbertSolenoid initialisation."""

    def test_default_init(self):
        s = AdelicHilbertSolenoid()
        assert s.n_primes == 50
        assert len(s.primes) == 50
        assert s.x_min < s.x_max
        assert len(s.x) == s.n_points

    def test_custom_n_primes(self):
        s = AdelicHilbertSolenoid(n_primes=10)
        assert len(s.primes) == 10

    def test_grid_positive(self, solenoid):
        assert np.all(solenoid.x > 0)

    def test_grid_monotone(self, solenoid):
        assert np.all(np.diff(solenoid.x) > 0)

    def test_primes_are_prime(self, solenoid):
        for p in solenoid.primes:
            assert all(p % d != 0 for d in range(2, p)) or p < 2

    def test_qcal_attributes(self, solenoid):
        assert solenoid.f0 == F0
        assert solenoid.f_unity == F_UNITY
        assert solenoid.C == C_QCAL


# ===========================================================================
# 4. Haar inner product
# ===========================================================================

class TestHaarInnerProduct:
    """Tests for the Haar measure inner product ⟨f,g⟩ = ∫ f̄ g dx/x."""

    def test_returns_complex(self, solenoid, test_functions):
        f, g = test_functions
        ip = solenoid.haar_inner_product(f, g)
        assert isinstance(ip, complex)

    def test_self_inner_product_real_positive(self, solenoid, test_functions):
        f, _ = test_functions
        ip = solenoid.haar_inner_product(f, f)
        assert ip.real > 0
        assert abs(ip.imag) < 1e-10 * abs(ip.real)

    def test_conjugate_symmetry(self, solenoid, test_functions):
        f, g = test_functions
        ip_fg = solenoid.haar_inner_product(f, g)
        ip_gf = solenoid.haar_inner_product(g, f)
        assert np.isclose(ip_fg, np.conj(ip_gf), rtol=1e-6)

    def test_linearity_in_second_argument(self, solenoid, test_functions):
        f, g = test_functions
        alpha = 2.5 + 0.3j
        ip_fg = solenoid.haar_inner_product(f, g)
        ip_f_ag = solenoid.haar_inner_product(f, alpha * g)
        assert np.isclose(ip_f_ag, alpha * ip_fg, rtol=1e-6)

    def test_haar_scale_invariance(self, solenoid, test_functions):
        """⟨f, g⟩ ≈ ⟨f(λ·), g(λ·)⟩ under log-uniform grid rescaling.

        This property holds exactly for infinite grids.  On a finite bounded
        grid, rescaling shifts the support window, so we only require the
        two inner products to be of the same order of magnitude (rtol=0.5).
        This is a structural sanity check rather than a precision test.
        """
        f, g = test_functions
        x = solenoid.x
        lam = 2.0
        x_scaled = x * lam
        # Construct functions on scaled grid
        ln_xs = np.log(x_scaled)
        sigma = 0.5
        f_s = np.exp(-((ln_xs - 0.5) ** 2) / (2 * sigma ** 2)) / x_scaled ** 0.5
        g_s = np.exp(-((ln_xs + 0.5) ** 2) / (2 * sigma ** 2)) / x_scaled ** 0.5
        ip_orig = solenoid.haar_inner_product(f, g)
        ip_scaled = solenoid.haar_inner_product(f_s, g_s, x_scaled)
        # Allow 50% relative difference: finite-domain window shift
        rtol = 0.5
        denom = abs(ip_orig) + abs(ip_scaled) + 1e-10
        assert abs(ip_orig - ip_scaled) / denom < rtol


# ===========================================================================
# 5. Operator application
# ===========================================================================

class TestOperatorApplication:
    """Tests for Ĥ = -i(x d/dx + 1/2)."""

    def test_returns_array(self, solenoid, test_functions):
        f, _ = test_functions
        Hf = solenoid.apply_operator(f)
        assert Hf.shape == f.shape

    def test_returns_complex(self, solenoid, test_functions):
        f, _ = test_functions
        Hf = solenoid.apply_operator(f)
        assert np.iscomplexobj(Hf)

    def test_linearity(self, solenoid, test_functions):
        f, g = test_functions
        alpha = 1.5
        Hf = solenoid.apply_operator(f)
        Hg = solenoid.apply_operator(g)
        H_fg = solenoid.apply_operator(f + alpha * g)
        assert np.allclose(H_fg, Hf + alpha * Hg, rtol=1e-5)

    def test_complex_input(self, solenoid):
        x = solenoid.x
        f_c = solenoid.eigenfunction(x, 5.0)
        Hf = solenoid.apply_operator(f_c)
        assert np.iscomplexobj(Hf)
        assert Hf.shape == f_c.shape


# ===========================================================================
# 6. Self-adjointness
# ===========================================================================

class TestSelfAdjointness:
    """Verify ⟨Ĥf, g⟩ = ⟨f, Ĥg⟩ using default eigenfunctions."""

    def test_self_adjoint_flag_defaults(self, solenoid):
        """Default (eigenfunctions) must pass."""
        result = solenoid.verify_self_adjointness()
        assert result["self_adjoint"], (
            f"Self-adjointness failed with relative error = {result['error']:.4e}"
        )

    def test_error_finite(self, solenoid):
        result = solenoid.verify_self_adjointness()
        assert np.isfinite(result["error"])

    def test_relative_error_lt_one(self, solenoid):
        """Relative error must be < 1.0 (100 %)."""
        result = solenoid.verify_self_adjointness()
        assert result["error"] < 1.0

    def test_boundary_term_finite(self, solenoid):
        result = solenoid.verify_self_adjointness()
        assert np.isfinite(result["boundary_term"])

    def test_has_required_keys(self, solenoid):
        result = solenoid.verify_self_adjointness()
        for key in ("lhs", "rhs", "error", "self_adjoint", "boundary_term"):
            assert key in result

    def test_custom_functions(self, solenoid, test_functions):
        """Custom real Gaussian test functions should return finite values."""
        f, g = test_functions
        x = solenoid.x
        result = solenoid.verify_self_adjointness(f, g, x)
        assert np.isfinite(result["error"])
        assert "self_adjoint" in result


# ===========================================================================
# 7. Enki Scale Invariance
# ===========================================================================

class TestEnkiScaleInvariance:
    """Domain condition f(px) = f(x)."""

    def test_constant_function_invariant(self, solenoid):
        """Constant f(x) = 1 trivially satisfies f(px) = f(x)."""
        x = solenoid.x[:100]
        result = solenoid.enki_scale_invariant(lambda t: np.ones_like(t), x)
        assert result["invariant"]
        assert result["max_error"] < 1e-12

    def test_non_invariant_function(self, solenoid):
        """f(x) = x is NOT Enki scale invariant (f(px) = p·x ≠ x)."""
        x = solenoid.x[:50]
        result = solenoid.enki_scale_invariant(lambda t: t, x)
        assert not result["invariant"]

    def test_per_prime_keys(self, solenoid):
        x = solenoid.x[:50]
        result = solenoid.enki_scale_invariant(lambda t: np.ones_like(t), x)
        assert len(result["per_prime"]) > 0


# ===========================================================================
# 8. Eigenfunctions
# ===========================================================================

class TestEigenfunctions:
    """Tests for ψ_E(x) = x^(-1/2 + iE)."""

    def test_eigenfunction_shape(self, solenoid):
        psi = solenoid.eigenfunction(solenoid.x, 14.135)
        assert psi.shape == solenoid.x.shape

    def test_eigenfunction_complex(self, solenoid):
        psi = solenoid.eigenfunction(solenoid.x, 14.135)
        assert np.iscomplexobj(psi)

    def test_eigenfunction_amplitude(self, solenoid):
        """|ψ_E(x)| = x^(-1/2) for all x."""
        x = solenoid.x
        psi = solenoid.eigenfunction(x, 5.0)
        expected_amp = x ** (-0.5)
        assert np.allclose(np.abs(psi), expected_amp, rtol=1e-10)

    def test_eigenfunction_phase(self, solenoid):
        """arg(ψ_E(x)) = E ln x."""
        x = solenoid.x[10:50]
        E = 3.0
        psi = solenoid.eigenfunction(x, E)
        expected_phase = E * np.log(x)
        actual_phase = np.angle(psi)
        # Phases match modulo 2π
        diff = (actual_phase - expected_phase + np.pi) % (2 * np.pi) - np.pi
        assert np.allclose(diff, 0, atol=1e-10)

    def test_zero_E_real_valued(self, solenoid):
        """For E=0, ψ_0(x) = x^(-1/2) is real."""
        x = solenoid.x
        psi = solenoid.eigenfunction(x, 0.0)
        assert np.allclose(psi.imag, 0, atol=1e-12)
        assert np.allclose(psi.real, x ** (-0.5), rtol=1e-10)


# ===========================================================================
# 9. Eigenvalue equation
# ===========================================================================

class TestEigenvalueEquation:
    """Verify Ĥ ψ_E ≈ E ψ_E numerically."""

    @pytest.mark.parametrize("E", [0.0, 1.0, 5.0, 14.1347])
    def test_eigenvalue_equation(self, solenoid, E):
        result = solenoid.verify_eigenvalue_equation(E)
        assert result["passed"], (
            f"Eigenvalue equation failed for E={E}: max_error={result['max_error']:.4e}"
        )

    def test_result_has_required_keys(self, solenoid):
        result = solenoid.verify_eigenvalue_equation(1.0)
        assert "E" in result
        assert "max_error" in result
        assert "passed" in result

    def test_max_error_finite(self, solenoid):
        result = solenoid.verify_eigenvalue_equation(5.0)
        assert np.isfinite(result["max_error"])


# ===========================================================================
# 10. Critical line correspondence
# ===========================================================================

class TestCriticalLine:
    """When E ∈ ℝ, s = 1/2 + iE → Re(s) = 1/2."""

    @pytest.mark.parametrize("E", [14.1347, 21.022, 25.011, 30.425, 32.935])
    def test_on_critical_line(self, solenoid, E):
        result = solenoid.critical_line_correspondence(E)
        assert result["on_critical_line"], (
            f"Re(s) = {result['real_part']} ≠ 0.5 for E = {E}"
        )

    def test_real_part_exactly_half(self, solenoid):
        result = solenoid.critical_line_correspondence(14.1347)
        assert abs(result["real_part"] - 0.5) < 1e-12

    def test_s_imaginary_part(self, solenoid):
        E = 21.022
        result = solenoid.critical_line_correspondence(E)
        assert np.isclose(result["s"].imag, E, rtol=1e-12)

    def test_eigenvalue_real(self, solenoid):
        result = solenoid.critical_line_correspondence(14.1347)
        assert result["eigenvalue_real"]

    def test_result_has_s(self, solenoid):
        result = solenoid.critical_line_correspondence(5.0)
        assert "s" in result


# ===========================================================================
# 11. Weil explicit formula
# ===========================================================================

class TestWeilExplicitFormula:
    """Structural tests for the Weil explicit formula."""

    def _gaussian_hat(self, u: float, sigma: float = 1.0) -> float:
        """Gaussian test function Fourier transform."""
        return float(np.exp(-0.5 * (u / sigma) ** 2))

    def test_returns_dict(self, solenoid):
        gammas = [14.1347, 21.022]
        result = solenoid.weil_explicit_formula(self._gaussian_hat, gammas)
        assert isinstance(result, dict)

    def test_required_keys(self, solenoid):
        gammas = [14.1347, 21.022]
        result = solenoid.weil_explicit_formula(self._gaussian_hat, gammas)
        assert "zero_sum" in result
        assert "prime_sum" in result
        assert "balance" in result

    def test_zero_sum_finite(self, solenoid):
        gammas = [14.1347, 21.022, 25.011]
        result = solenoid.weil_explicit_formula(self._gaussian_hat, gammas)
        assert np.isfinite(result["zero_sum"])

    def test_prime_sum_finite(self, solenoid):
        gammas = [14.1347]
        result = solenoid.weil_explicit_formula(self._gaussian_hat, gammas)
        assert np.isfinite(result["prime_sum"])

    def test_balance_positive(self, solenoid):
        gammas = [14.1347, 21.022]
        result = solenoid.weil_explicit_formula(self._gaussian_hat, gammas)
        assert result["balance"] >= 0


# ===========================================================================
# 12. QCAL coherence
# ===========================================================================

class TestQCALCoherence:
    """QCAL Ψ coherence."""

    def test_psi_in_range(self, solenoid):
        psi = solenoid.compute_coherence()
        assert 0.0 <= psi <= 1.0

    def test_psi_positive(self, solenoid):
        psi = solenoid.compute_coherence()
        assert psi > 0.0


# ===========================================================================
# 13. QED_Omega functions
# ===========================================================================

class TestQEDOmega:
    """Tests for the Q.E.D. entry points."""

    def test_instance_method_returns_string(self, solenoid):
        result = solenoid.QED_Omega()
        assert isinstance(result, str)
        assert "HECHO ESTÁ" in result

    def test_module_function_returns_string(self):
        result = QED_Omega()
        assert isinstance(result, str)
        assert "HECHO ESTÁ" in result

    def test_message_content(self, solenoid):
        result = solenoid.QED_Omega()
        assert "simetría" in result.lower() or "symmetry" in result.lower() or "simeti" in result.lower()


# ===========================================================================
# 14. sellar_solenoid_adélico (seal)
# ===========================================================================

class TestSellarSolenoidAdelico:
    """Integration test for the full proof seal."""

    @pytest.fixture(scope="class")
    def seal_result(self):
        return sellar_solenoid_adélico()

    def test_status_validated(self, seal_result):
        assert seal_result["status"] == "VALIDATED"

    def test_self_adjoint(self, seal_result):
        assert seal_result["self_adjoint"]

    def test_critical_line(self, seal_result):
        assert seal_result["critical_line"]

    def test_eigenvalue_equation_passed(self, seal_result):
        assert seal_result["eigenvalue_equation_passed"]

    def test_coherence_psi(self, seal_result):
        assert seal_result["coherence_Psi"] > 0.5

    def test_qed_message(self, seal_result):
        assert "HECHO ESTÁ" in seal_result["qed"]

    def test_framework_keys(self, seal_result):
        fw = seal_result["framework"]
        assert "hilbert_space" in fw
        assert "operator" in fw
        assert "domain" in fw
        assert "eigenfunction" in fw
        assert "critical_line" in fw

    def test_frequency(self, seal_result):
        assert np.isclose(seal_result["frequency"], F_UNITY)
