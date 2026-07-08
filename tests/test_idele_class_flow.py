#!/usr/bin/env python3
"""
Tests for Idele Class Flow Implementation
==========================================

Validates the natural dynamical system on X = A_Q^× / Q^×:
  - Dilation flow φ_t with orbit lengths ℓ_γ = ln p (Artin product formula)
  - Self-adjoint operator H = -i(x∂/∂x + 1/2) on L²(X, d*x)
  - Fredholm-Ruelle determinant Δ(s) = det(I - L_s) ≡ ξ(s)

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: March 2026
QCAL ∞³ Active · 141.7001 Hz
DOI: 10.5281/zenodo.17379721
"""

import sys
from pathlib import Path

import numpy as np
import pytest

# Add operators directory to path
repo_root = Path(__file__).parent.parent
sys.path.insert(0, str(repo_root / "operators"))

from idele_class_flow import (
    ClosedOrbit,
    FredholmRuelleDeterminant,
    FredholmRuelleResult,
    IdeleClassFlow,
    OrbitRigidity,
    OrbitRigidityResult,
    SelfAdjointDilationH,
    SelfAdjointVerification,
    _sieve_primes,
    validate_idele_class_flow,
)


# ---------------------------------------------------------------------------
# Helper
# ---------------------------------------------------------------------------

SMALL_PRIMES = [2, 3, 5, 7, 11, 13]


# ===========================================================================
# Tests for _sieve_primes
# ===========================================================================

class TestSievePrimes:
    """Tests for prime sieve utility."""

    def test_first_few_primes(self):
        """Sieve should return [2, 3, 5, 7] for n_max=10."""
        primes = _sieve_primes(10)
        assert primes == [2, 3, 5, 7]

    def test_sieve_empty_below_two(self):
        """No primes below 2."""
        assert _sieve_primes(1) == []
        assert _sieve_primes(0) == []

    def test_sieve_includes_boundary(self):
        """n_max itself is included when prime."""
        primes = _sieve_primes(7)
        assert 7 in primes

    def test_sieve_count_100(self):
        """There are 25 primes ≤ 100."""
        assert len(_sieve_primes(100)) == 25

    def test_all_prime(self):
        """Every number returned is prime."""
        primes = _sieve_primes(50)
        for p in primes:
            assert all(p % d != 0 for d in range(2, p)), f"{p} is not prime"

    def test_no_composites(self):
        """No composite numbers are returned."""
        primes = _sieve_primes(30)
        composites = [4, 6, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 22, 25, 26, 27, 28]
        for c in composites:
            assert c not in primes


# ===========================================================================
# Tests for IdeleClassFlow
# ===========================================================================

class TestIdeleClassFlow:
    """Tests for the dilation flow on X = A_Q^× / Q^×."""

    def setup_method(self):
        self.flow = IdeleClassFlow(primes=SMALL_PRIMES, t_max=8.0, max_k=4)

    # ------------------------------------------------------------------
    # Initialization
    # ------------------------------------------------------------------

    def test_initialization(self):
        """Flow initializes with correct primes and parameters."""
        assert self.flow.primes == SMALL_PRIMES
        assert self.flow.t_max == 8.0
        assert self.flow.max_k == 4

    def test_default_primes(self):
        """Default constructor uses primes ≤ 50."""
        flow = IdeleClassFlow()
        assert all(_sieve_primes(50).__contains__(p) for p in flow.primes)
        assert len(flow.primes) >= 10

    # ------------------------------------------------------------------
    # Archimedean dilation
    # ------------------------------------------------------------------

    def test_archimedean_dilation(self):
        """φ_t(x)_∞ = e^t · x_∞."""
        x, t = 3.7, 1.5
        result = self.flow.flow_archimedean(x, t)
        assert abs(result - np.exp(t) * x) < 1e-12

    def test_archimedean_identity_at_zero_time(self):
        """φ_0 is the identity: x → x."""
        x = 4.2
        assert abs(self.flow.flow_archimedean(x, 0.0) - x) < 1e-12

    def test_archimedean_semigroup(self):
        """φ_{t+s}(x) = φ_t(φ_s(x)) (semigroup property)."""
        x, t, s = 2.0, 0.5, 1.0
        result1 = self.flow.flow_archimedean(x, t + s)
        result2 = self.flow.flow_archimedean(self.flow.flow_archimedean(x, s), t)
        assert abs(result1 - result2) < 1e-12

    # ------------------------------------------------------------------
    # p-adic identity
    # ------------------------------------------------------------------

    def test_p_adic_identity(self):
        """p-adic components are unchanged by the flow."""
        for val in [1.0, 0.5, 2.3, 0.0]:
            assert self.flow.flow_p_adic(val) == val

    # ------------------------------------------------------------------
    # Closed orbit detection
    # ------------------------------------------------------------------

    def test_closed_orbit_at_ln_p(self):
        """t = ln p is a closed orbit for each prime p."""
        for p in SMALL_PRIMES:
            t = np.log(p)
            assert self.flow.is_closed_orbit(t), f"t=ln({p}) should be closed"

    def test_closed_orbit_at_k_ln_p(self):
        """t = k ln p is closed for k = 2, 3."""
        for p in [2, 3]:
            for k in [2, 3]:
                t = k * np.log(p)
                if t <= self.flow.t_max:
                    assert self.flow.is_closed_orbit(t), (
                        f"t={k}ln({p}) should be closed"
                    )

    def test_non_closed_orbit(self):
        """t = π is NOT a closed orbit (π ≠ k ln p for any prime/integer)."""
        # π ≈ 3.14159... — check it's not a prime-power ln
        assert not self.flow.is_closed_orbit(np.pi, tolerance=1e-6)

    def test_sqrt2_not_closed(self):
        """t = √2 is not a closed orbit."""
        assert not self.flow.is_closed_orbit(np.sqrt(2), tolerance=1e-6)

    # ------------------------------------------------------------------
    # Orbit enumeration
    # ------------------------------------------------------------------

    def test_enumerate_returns_closed_orbits(self):
        """Enumeration returns ClosedOrbit instances."""
        orbits = self.flow.enumerate_closed_orbits()
        assert len(orbits) > 0
        for o in orbits:
            assert isinstance(o, ClosedOrbit)

    def test_orbit_lengths_equal_k_ln_p(self):
        """Each orbit has ℓ = k ln p exactly."""
        orbits = self.flow.enumerate_closed_orbits()
        for o in orbits:
            expected = o.k * np.log(o.prime)
            assert abs(o.length - expected) < 1e-12, (
                f"Orbit length {o.length} ≠ {o.k}·ln({o.prime})"
            )

    def test_orbit_weights_positive(self):
        """All orbit weights must be positive."""
        orbits = self.flow.enumerate_closed_orbits()
        for o in orbits:
            assert o.weight > 0, f"Orbit weight should be positive: {o.weight}"

    def test_orbits_sorted_by_length(self):
        """Orbits are sorted by increasing length."""
        orbits = self.flow.enumerate_closed_orbits()
        lengths = [o.length for o in orbits]
        assert lengths == sorted(lengths)

    def test_first_orbit_is_ln_2(self):
        """The smallest orbit has length ln 2."""
        orbits = self.flow.enumerate_closed_orbits()
        assert len(orbits) > 0
        assert abs(orbits[0].length - np.log(2)) < 1e-12

    def test_primitive_orbit_length(self):
        """primitive_orbit_length(p) = ln p."""
        for p in SMALL_PRIMES:
            assert abs(self.flow.primitive_orbit_length(p) - np.log(p)) < 1e-12

    def test_orbit_jacobian_determinant(self):
        """Jacobian |det(I - dφ_{ln p})| = p^(1/2) - p^(-1/2)."""
        orbits = self.flow.enumerate_closed_orbits()
        for o in orbits:
            p, k = o.prime, o.k
            expected_jac = abs(p ** (k / 2.0) - p ** (-k / 2.0))
            assert abs(o.jacobian_det - expected_jac) < 1e-10, (
                f"Jacobian mismatch for p={p}, k={k}"
            )

    def test_orbits_within_t_max(self):
        """All orbits have length ≤ t_max."""
        orbits = self.flow.enumerate_closed_orbits()
        for o in orbits:
            assert o.length <= self.flow.t_max + 1e-10


# ===========================================================================
# Tests for OrbitRigidity (Artin product formula)
# ===========================================================================

class TestOrbitRigidity:
    """Tests for the Artin product formula orbit-rigidity verification."""

    def setup_method(self):
        self.rigidity = OrbitRigidity(
            primes=_sieve_primes(20), t_max=8.0
        )

    # ------------------------------------------------------------------
    # p-adic valuation
    # ------------------------------------------------------------------

    def test_p_adic_valuation_basic(self):
        """v_2(8) = 3, v_3(9) = 2."""
        assert self.rigidity.p_adic_valuation(8, 2) == 3
        assert self.rigidity.p_adic_valuation(9, 3) == 2

    def test_p_adic_valuation_zero_exponent(self):
        """v_p(n) = 0 when p ∤ n."""
        assert self.rigidity.p_adic_valuation(7, 3) == 0
        assert self.rigidity.p_adic_valuation(10, 3) == 0

    def test_p_adic_valuation_negative(self):
        """v_p works for negative integers via |n|."""
        assert self.rigidity.p_adic_valuation(-8, 2) == 3

    def test_p_adic_valuation_zero_raises(self):
        """v_p(0) is undefined — should raise ValueError."""
        with pytest.raises(ValueError):
            self.rigidity.p_adic_valuation(0, 2)

    # ------------------------------------------------------------------
    # p-adic norm
    # ------------------------------------------------------------------

    def test_p_adic_norm_basic(self):
        """|8|_2 = 2^{-3} = 1/8."""
        result = self.rigidity.p_adic_norm(8, 2)
        assert abs(result - 1.0 / 8) < 1e-12

    def test_p_adic_norm_one_for_coprime(self):
        """|7|_3 = 1 (7 is coprime to 3)."""
        assert abs(self.rigidity.p_adic_norm(7, 3) - 1.0) < 1e-12

    def test_p_adic_norm_zero_for_zero(self):
        """|0|_p = 0 by convention."""
        assert self.rigidity.p_adic_norm(0, 2) == 0.0

    # ------------------------------------------------------------------
    # Artin product formula
    # ------------------------------------------------------------------

    def test_artin_product_prime(self):
        """Artin product Π_v |p|_v = 1 for any prime p (within known primes)."""
        # For a prime p ≤ max(primes), the only non-trivial p-adic factor is p itself.
        # |p|_∞ · |p|_p · Π_{q≠p} |p|_q = p · (1/p) · 1 = 1
        for p in [2, 3, 5, 7]:
            val = self.rigidity.artin_product(p)
            assert abs(val - 1.0) < 1e-10, (
                f"Artin product for {p} = {val} ≠ 1"
            )

    def test_artin_product_prime_square(self):
        """Artin product = 1 for p² (all prime contributions)."""
        # |p²|_∞ = p², |p²|_p = p^{-2}, Π_{q≠p} |p²|_q = 1
        for p in [2, 3]:
            val = self.rigidity.artin_product(p * p)
            assert abs(val - 1.0) < 1e-10

    # ------------------------------------------------------------------
    # Full orbit rigidity verification
    # ------------------------------------------------------------------

    def test_rigidity_result_type(self):
        """verify_orbit_rigidity returns OrbitRigidityResult."""
        result = self.rigidity.verify_orbit_rigidity()
        assert isinstance(result, OrbitRigidityResult)

    def test_is_rigid(self):
        """Orbit rigidity flag is True."""
        result = self.rigidity.verify_orbit_rigidity()
        assert result.is_rigid, "Orbit rigidity should hold"

    def test_artin_product_satisfied(self):
        """Artin product formula holds for all orbit representatives."""
        result = self.rigidity.verify_orbit_rigidity()
        assert result.artin_product_satisfied, (
            "Artin product formula should be satisfied"
        )

    def test_primes_found(self):
        """Primes found in orbit lengths cover first few primes."""
        result = self.rigidity.verify_orbit_rigidity()
        for p in [2, 3, 5]:
            assert p in result.primes_found, f"Prime {p} should appear in orbits"

    def test_orbit_lengths_are_ln_primes(self):
        """Orbit lengths from rigidity test are k ln p values."""
        result = self.rigidity.verify_orbit_rigidity()
        for length in result.orbit_lengths:
            # Check that e^length is a prime power
            et = np.exp(length)
            found = False
            for p in result.primes_found:
                if p > 1:
                    k_float = np.log(et) / np.log(p)
                    k_int = round(k_float)
                    if k_int >= 1 and abs(k_float - k_int) < 1e-6:
                        found = True
                        break
            assert found, f"Length {length} is not k ln p for any prime"


# ===========================================================================
# Tests for SelfAdjointDilationH
# ===========================================================================

class TestSelfAdjointDilationH:
    """Tests for H = -i(x∂_x + 1/2) on L²(ℝ_{>0}, dx/x)."""

    def setup_method(self):
        self.H = SelfAdjointDilationH(n_points=256, x_min=1e-3, x_max=1e3)

    # ------------------------------------------------------------------
    # Initialization
    # ------------------------------------------------------------------

    def test_initialization(self):
        """H initializes with correct grid parameters."""
        assert self.H.n_points == 256
        assert self.H.x_min == 1e-3
        assert self.H.x_max == 1e3
        assert len(self.H.x_grid) == 256
        assert len(self.H.y_grid) == 256

    def test_x_grid_positive(self):
        """All x values are positive."""
        assert np.all(self.H.x_grid > 0)

    def test_y_grid_is_log_x(self):
        """y_grid = ln(x_grid)."""
        assert np.allclose(self.H.y_grid, np.log(self.H.x_grid))

    # ------------------------------------------------------------------
    # Operator application
    # ------------------------------------------------------------------

    def test_apply_returns_array_same_shape(self):
        """H.apply returns array of same shape as input."""
        psi = np.exp(-self.H.x_grid)
        result = self.H.apply(psi)
        assert result.shape == psi.shape

    def test_apply_returns_complex(self):
        """H.apply returns complex-valued array (H has factor -i)."""
        psi = np.exp(-self.H.x_grid)
        result = self.H.apply(psi)
        assert np.iscomplexobj(result)

    def test_apply_real_input_imaginary_output(self):
        """T = -i∂_y of a smooth real function gives purely imaginary output."""
        psi = np.exp(-self.H.x_grid).astype(float)
        result = self.H.apply(psi)
        # T = -i∂_y → result is purely imaginary for real input
        assert np.max(np.abs(result.real)) < np.max(np.abs(result.imag)) * 1e-8

    # ------------------------------------------------------------------
    # Inner product
    # ------------------------------------------------------------------

    def test_inner_product_positive_definite(self):
        """⟨ψ, ψ⟩ > 0 for non-zero ψ."""
        psi = np.exp(-self.H.x_grid)
        ip = self.H.inner_product(psi, psi)
        assert ip.real > 0

    def test_inner_product_conjugate_symmetry(self):
        """⟨φ, ψ⟩ = conj(⟨ψ, φ⟩)."""
        phi = np.exp(-self.H.x_grid)
        psi = np.sqrt(self.H.x_grid) * np.exp(-self.H.x_grid)
        ip_phipsi = self.H.inner_product(phi, psi)
        ip_psiphi = self.H.inner_product(psi, phi)
        assert abs(ip_phipsi - np.conj(ip_psiphi)) < 1e-10

    def test_inner_product_linearity(self):
        """⟨φ, αψ⟩ = α ⟨φ, ψ⟩."""
        phi = np.exp(-self.H.x_grid)
        psi = np.sqrt(self.H.x_grid) * np.exp(-self.H.x_grid)
        alpha = 2.5 + 1.3j
        lhs = self.H.inner_product(phi, alpha * psi)
        rhs = alpha * self.H.inner_product(phi, psi)
        assert abs(lhs - rhs) < 1e-10

    # ------------------------------------------------------------------
    # Self-adjointness
    # ------------------------------------------------------------------

    def test_self_adjoint_verification_type(self):
        """verify_self_adjoint returns SelfAdjointVerification."""
        result = self.H.verify_self_adjoint(n_test=5)
        assert isinstance(result, SelfAdjointVerification)

    def test_is_self_adjoint(self):
        """T = -i∂_y is self-adjoint (Hermitian matrix check)."""
        result = self.H.verify_self_adjoint(n_test=10, tolerance=1e-4)
        assert result.is_self_adjoint, (
            f"T should be self-adjoint; symmetry_error={result.symmetry_error:.2e}"
        )

    def test_symmetry_error_small(self):
        """Hermitian error for periodic FD matrix is negligible."""
        result = self.H.verify_self_adjoint(n_test=10, tolerance=1e-4)
        assert result.is_self_adjoint

    def test_eigenvalue_reality(self):
        """Eigenvalues of T = -i∂_y are purely real (self-adjoint operator)."""
        result = self.H.verify_self_adjoint(n_test=5)
        assert result.eigenvalue_reality, (
            f"Eigenvalues should be real; "
            f"max_imag={result.max_imaginary_part:.2e}"
        )

    # ------------------------------------------------------------------
    # Mellin diagonalization
    # ------------------------------------------------------------------

    def test_mellin_diagonalization_verified(self):
        """T = -i∂_y is Hermitian with real Fourier eigenvalues."""
        result = self.H.verify_mellin_diagonalization()
        assert result["verified"], (
            f"Mellin diagonalization failed: "
            f"herm_err={result.get('herm_error', '?'):.2e}, "
            f"max_imag_eig={result.get('max_imaginary_eig', '?'):.2e}"
        )

    def test_mellin_transform_critical_line(self):
        """Standard Mellin transform converges at Re(s) = 1."""
        psi = np.sqrt(self.H.x_grid) * np.exp(-self.H.x_grid)
        s = 1.0 + 2.0j
        mt = self.H.mellin_transform(psi, s)
        assert np.isfinite(mt.real) and np.isfinite(mt.imag)

    def test_mellin_transform_nonzero(self):
        """Mellin transform of a non-zero function is non-zero."""
        psi = np.sqrt(self.H.x_grid) * np.exp(-self.H.x_grid)
        s = 1.0 + 0j
        mt = self.H.mellin_transform(psi, s)
        assert abs(mt) > 1e-10


# ===========================================================================
# Tests for FredholmRuelleDeterminant
# ===========================================================================

class TestFredholmRuelleDeterminant:
    """Tests for Δ(s) = det(I - L_s) and its identification with ξ(s)."""

    def setup_method(self):
        self.frd = FredholmRuelleDeterminant(
            primes=_sieve_primes(50),
            max_k=20,
            n_primes_euler=80,
        )

    # ------------------------------------------------------------------
    # Archimedean factor
    # ------------------------------------------------------------------

    def test_archimedean_factor_real_at_real_s(self):
        """γ_∞(s) = π^{-s/2} Γ(s/2) is real for real s > 0."""
        for s_val in [1.0, 2.0, 3.0]:
            arch = self.frd.archimedean_factor(complex(s_val))
            assert abs(arch.imag) < 1e-12, (
                f"Archimedean factor should be real at s={s_val}"
            )

    def test_archimedean_factor_nonzero(self):
        """γ_∞(s) ≠ 0 for Re(s) > 0."""
        for s in [2.0 + 0j, 2.0 + 3j, 1.5 + 0.5j]:
            assert abs(self.frd.archimedean_factor(s)) > 1e-10

    # ------------------------------------------------------------------
    # Euler product
    # ------------------------------------------------------------------

    def test_euler_product_converges(self):
        """Euler product converges for Re(s) > 1."""
        ep = self.frd.euler_product(2.0 + 0j)
        assert np.isfinite(ep.real) and np.isfinite(ep.imag)

    def test_euler_product_bounded_above_one(self):
        """Euler product ≤ 1 for Re(s) > 1 (each factor |1-p^{-s}| < 1)."""
        ep = abs(self.frd.euler_product(2.0 + 0j))
        assert ep <= 1.0 + 1e-10

    def test_euler_product_positive_real_s(self):
        """Euler product is real and positive for real s > 1."""
        ep = self.frd.euler_product(2.0 + 0j)
        assert ep.imag < 1e-10
        assert ep.real > 0

    # ------------------------------------------------------------------
    # Prime orbit sum
    # ------------------------------------------------------------------

    def test_prime_orbit_sum_convergent(self):
        """Prime orbit sum converges for Re(s) = 2."""
        ln_delta = self.frd.prime_orbit_sum(2.0 + 0j)
        assert np.isfinite(ln_delta.real)

    def test_prime_orbit_sum_negative(self):
        """ln Δ(s) < 0 for Re(s) > 1 (Δ = 1/ζ < 1 there)."""
        ln_delta = self.frd.prime_orbit_sum(2.0 + 0j)
        assert ln_delta.real < 0

    def test_orbit_sum_equals_log_euler(self):
        """
        Prime orbit sum agrees with log of Euler product.

        ln Δ(s) = -Σ_{p,k} p^{-ks}/k = Σ_p ln(1 - p^{-s}) = ln Π_p (1-p^{-s})
        """
        s = 2.0 + 0j
        ln_delta_orbit = self.frd.prime_orbit_sum(s)
        ep = self.frd.euler_product(s)
        ln_ep = np.log(ep)
        rel_err = abs(ln_delta_orbit - ln_ep) / max(abs(ln_ep), 1e-15)
        assert rel_err < 0.05, (
            f"Orbit sum ln Δ={ln_delta_orbit:.6f} ≠ ln Euler={ln_ep:.6f}"
        )

    # ------------------------------------------------------------------
    # Euler ↔ orbit consistency
    # ------------------------------------------------------------------

    def test_verify_euler_orbit_consistency_passes(self):
        """Euler product and orbit sum agree at multiple s values."""
        check = self.frd.verify_euler_orbit_consistency(
            s_values=[2.0 + 0j, 3.0 + 0j, 2.0 + 1j],
            tolerance=0.05,
        )
        assert check["all_passed"], (
            f"Euler/orbit consistency failed: {check['details']}"
        )

    # ------------------------------------------------------------------
    # Full compute
    # ------------------------------------------------------------------

    def test_compute_returns_result_type(self):
        """compute() returns FredholmRuelleResult."""
        result = self.frd.compute(2.0 + 0j)
        assert isinstance(result, FredholmRuelleResult)

    def test_compute_stores_s(self):
        """Result stores the correct s parameter."""
        s = 2.5 + 1j
        result = self.frd.compute(s)
        assert result.s == s

    def test_delta_s_nonzero(self):
        """Δ(s) ≠ 0 for Re(s) > 1 (not a zero of 1/ζ)."""
        result = self.frd.compute(2.0 + 0j)
        assert abs(result.delta_s) > 1e-10

    def test_xi_identification_small_error(self):
        """Δ(s) combined with arch factor approximates ξ(s) within 20%."""
        for s in [2.0 + 0j, 3.0 + 0j]:
            result = self.frd.compute(s)
            assert result.relative_error < 0.2, (
                f"Δ(s) ≠ ξ(s) at s={s}: relative_error={result.relative_error:.4f}"
            )

    def test_archimedean_factor_in_result(self):
        """Result contains non-zero Archimedean factor."""
        result = self.frd.compute(2.0 + 0j)
        assert abs(result.archimedean_factor) > 0

    def test_guillemin_pollack_residues_positive(self):
        """Guillemin-Pollack residues are positive for Re(s) > 1."""
        result = self.frd.compute(2.0 + 0j)
        for p, res in result.guillemin_pollack_residues.items():
            assert res > 0, f"GP residue for p={p} should be positive"


# ===========================================================================
# Integration test: validate_idele_class_flow
# ===========================================================================

class TestValidateIdeleClassFlow:
    """Integration tests using the top-level validation function."""

    def test_validation_runs(self):
        """validate_idele_class_flow() completes without error."""
        result = validate_idele_class_flow(verbose=False)
        assert isinstance(result, dict)

    def test_validation_has_expected_keys(self):
        """Validation result contains expected keys."""
        result = validate_idele_class_flow(verbose=False)
        expected_keys = [
            "orbit_rigidity",
            "orbit_lengths",
            "self_adjoint",
            "mellin_diag",
            "euler_orbit",
            "xi_identification",
            "passed",
            "psi",
            "certificate",
            "qcal",
        ]
        for key in expected_keys:
            assert key in result, f"Missing key: {key}"

    def test_validation_passes(self):
        """Full validation passes."""
        result = validate_idele_class_flow(verbose=False)
        assert result["passed"], (
            f"Validation failed; details: {result}"
        )

    def test_psi_equals_one(self):
        """Ψ = 1.0 when all checks pass."""
        result = validate_idele_class_flow(verbose=False)
        assert result["psi"] == 1.0

    def test_certificate_format(self):
        """Certificate has expected QCAL format prefix."""
        result = validate_idele_class_flow(verbose=False)
        assert result["certificate"].startswith("0xQCAL_IDELE_")

    def test_qcal_constants(self):
        """QCAL constants are present and correct."""
        result = validate_idele_class_flow(verbose=False)
        qcal = result["qcal"]
        assert abs(qcal["f0_hz"] - 141.7001) < 1e-4
        assert abs(qcal["C"] - 244.36) < 1e-4

    def test_orbit_rigidity_passes(self):
        """Orbit rigidity sub-check passes."""
        result = validate_idele_class_flow(verbose=False)
        assert result["orbit_rigidity"]["is_rigid"]
        assert result["orbit_rigidity"]["artin_product_ok"]

    def test_self_adjoint_passes(self):
        """Self-adjointness sub-check passes."""
        result = validate_idele_class_flow(verbose=False)
        assert result["self_adjoint"]["is_self_adjoint"]
