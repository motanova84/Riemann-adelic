#!/usr/bin/env python3
"""
Tests for the Adelic Scaling Flow Implementation
=================================================

Validates the five components of the adelic scaling flow:
  I.   Phase space 𝒳 = 𝔸_ℚ^× / ℚ^×
  II.  Dynamic flow φ_t and Haar-measure preservation
  III. Orbit rigidity: period T = log p
  IV.  Hamiltonian Ĥ = -i(x∂_x + 1/2) self-adjointness
  V.   Fredholm determinant = ξ(s)

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: March 2026
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Ensure operators directory is importable
repo_root = Path(__file__).parent.parent
sys.path.insert(0, str(repo_root / "operators"))

from adelic_scaling_flow import (
    IdelicPhaseSpace,
    AdelicScalingFlow,
    DilationHamiltonian,
    PeriodicOrbit,
    SelfAdjointnessResult,
    FredholmXiResult,
    xi_function,
    fredholm_determinant_approx,
    verify_fredholm_xi_identity,
    validate_adelic_scaling_flow,
    _sieve,
)


# ---------------------------------------------------------------------------
# Helper
# ---------------------------------------------------------------------------

def small_primes() -> list:
    return [2, 3, 5, 7, 11, 13]


# ===========================================================================
# I. Phase space 𝒳 = 𝔸_ℚ^× / ℚ^×
# ===========================================================================

class TestIdelicPhaseSpace:
    """Tests for the idele class group phase space."""

    def setup_method(self):
        self.ps = IdelicPhaseSpace(primes=small_primes(), n_points=200)

    def test_initialization(self):
        """Phase space initialises with correct primes and grid."""
        assert self.ps.primes == small_primes()
        assert len(self.ps.x_grid) == 200
        assert self.ps.x_grid[0] > 0
        assert self.ps.x_grid[-1] > self.ps.x_grid[0]

    def test_log_uniform_grid(self):
        """x_grid is log-uniformly spaced."""
        log_x = np.log(self.ps.x_grid)
        diffs = np.diff(log_x)
        assert np.allclose(diffs, diffs[0], rtol=1e-10)

    def test_haar_measure_element(self):
        """d*x = 1/x is positive and correctly computed."""
        for x in [0.5, 1.0, 3.14, 100.0]:
            assert abs(self.ps.haar_measure_element(x) - 1.0 / x) < 1e-14

    def test_haar_measure_element_zero_raises(self):
        """Haar measure at x=0 should raise ValueError."""
        with pytest.raises(ValueError):
            self.ps.haar_measure_element(0.0)

    def test_p_adic_norm_prime(self):
        """|p|_p = 1/p."""
        for p in small_primes():
            assert abs(self.ps.p_adic_norm(p, p) - 1.0 / p) < 1e-14

    def test_p_adic_norm_prime_square(self):
        """|p²|_p = 1/p²."""
        for p in small_primes():
            assert abs(self.ps.p_adic_norm(p * p, p) - 1.0 / p**2) < 1e-14

    def test_p_adic_norm_coprime(self):
        """|q|_p = 1 when gcd(q,p)=1."""
        assert abs(self.ps.p_adic_norm(3, 2) - 1.0) < 1e-14
        assert abs(self.ps.p_adic_norm(4, 3) - 1.0) < 1e-14

    def test_artin_product_formula_primes(self):
        """Artin product ∏_v |p|_v = 1 for each prime p."""
        for p in small_primes():
            product = self.ps.artin_product(p)
            assert abs(product - 1.0) < 1e-9, (
                f"Artin product for p={p}: expected 1, got {product}"
            )

    def test_artin_product_formula_integers(self):
        """Artin product ∏_v |n|_v = 1 for positive integers (using limited primes)."""
        # For n = p1*p2, with both p1,p2 in our prime list the product is 1
        for n in [6, 10, 15]:  # products of primes in our list
            product = self.ps.artin_product(n)
            assert abs(product - 1.0) < 1e-9, (
                f"Artin product for n={n}: expected 1, got {product}"
            )

    def test_idele_class_representative(self):
        """Primes satisfy the idele class condition."""
        for p in small_primes():
            assert self.ps.is_idele_class_representative(p)


# ===========================================================================
# II. Dynamic flow φ_t
# ===========================================================================

class TestAdelicScalingFlow:
    """Tests for the dilation flow φ_t([a]) = [(e^t, 1, 1, …)·a]."""

    def setup_method(self):
        self.ps = IdelicPhaseSpace(primes=small_primes(), n_points=200)
        self.flow = AdelicScalingFlow(phase_space=self.ps)

    def test_flow_action(self):
        """φ_t(x) = e^t x."""
        x = 2.5
        for t in [-1.0, 0.0, 0.5, 1.0, 2.0]:
            assert abs(self.flow.apply_flow(x, t) - np.exp(t) * x) < 1e-14

    def test_flow_at_zero_time(self):
        """φ_0 is the identity."""
        for x in [0.1, 1.0, 10.0]:
            assert abs(self.flow.apply_flow(x, 0.0) - x) < 1e-14

    def test_flow_composition(self):
        """φ_{t+s} = φ_t ∘ φ_s (group property)."""
        x, t, s = 3.0, 0.7, -0.3
        composed = self.flow.apply_flow(self.flow.apply_flow(x, s), t)
        direct = self.flow.apply_flow(x, t + s)
        assert abs(composed - direct) < 1e-12

    def test_flow_on_grid_shape(self):
        """flow_on_grid returns array of same length as x_grid."""
        shifted = self.flow.flow_on_grid(0.5)
        assert shifted.shape == self.ps.x_grid.shape

    def test_flow_on_grid_values(self):
        """flow_on_grid(t) = e^t * x_grid."""
        t = 1.3
        shifted = self.flow.flow_on_grid(t)
        assert np.allclose(shifted, np.exp(t) * self.ps.x_grid)

    def test_haar_measure_preserved(self):
        """φ_t preserves the Haar measure d*x = dx/x for all t."""
        for t in [-2.0, -0.5, 0.0, 0.5, 2.0]:
            assert self.flow.haar_measure_preserved(t)


# ===========================================================================
# III. Orbit rigidity
# ===========================================================================

class TestOrbitRigidity:
    """Tests for T = log p rigidity of periodic orbits."""

    def setup_method(self):
        ps = IdelicPhaseSpace(primes=small_primes(), n_points=100)
        self.flow = AdelicScalingFlow(phase_space=ps, max_prime_power=3)

    def test_primitive_orbit_periods(self):
        """Primitive orbits have period exactly log p."""
        orbits = self.flow.find_periodic_orbits(max_period=5.0)
        primitive = [o for o in orbits if o.is_primitive]
        for o in primitive:
            expected = np.log(float(o.prime))
            assert abs(o.period - expected) < 1e-12, (
                f"p={o.prime}: period={o.period}, expected log(p)={expected}"
            )

    def test_non_primitive_orbit_periods(self):
        """k-th orbit of prime p has period k·log p."""
        orbits = self.flow.find_periodic_orbits(max_period=10.0)
        for o in orbits:
            expected = o.power * np.log(float(o.prime))
            assert abs(o.period - expected) < 1e-12

    def test_orbits_sorted_by_period(self):
        """find_periodic_orbits returns orbits in ascending period order."""
        orbits = self.flow.find_periodic_orbits(max_period=5.0)
        periods = [o.period for o in orbits]
        assert periods == sorted(periods)

    def test_artin_product_on_orbits(self):
        """All periodic orbits satisfy the Artin product formula."""
        orbits = self.flow.find_periodic_orbits(max_period=4.0)
        for o in orbits:
            assert abs(o.artin_product - 1.0) < 1e-9, (
                f"p={o.prime}: Artin product = {o.artin_product}"
            )

    def test_rigidity_verification(self):
        """verify_orbit_rigidity returns all_ok=True for all orbits."""
        orbits = self.flow.find_periodic_orbits(max_period=4.0)
        for o in orbits:
            check = self.flow.verify_orbit_rigidity(o)
            assert check["all_ok"], (
                f"Rigidity check failed for p={o.prime}, k={o.power}: {check}"
            )

    def test_archimedean_closure_condition(self):
        """Closure condition e^T = p^k holds for every orbit."""
        orbits = self.flow.find_periodic_orbits(max_period=4.0)
        for o in orbits:
            assert abs(np.exp(o.period) - float(o.prime) ** o.power) < 1e-7

    def test_only_primes_generate_primitive_orbits(self):
        """Primitive orbits correspond bijectively to primes."""
        orbits = self.flow.find_periodic_orbits(max_period=4.0)
        primitive_primes = sorted({o.prime for o in orbits if o.is_primitive})
        expected_primes = [p for p in small_primes() if np.log(p) <= 4.0]
        assert primitive_primes == expected_primes


# ===========================================================================
# IV. Hamiltonian Ĥ = -i(x ∂_x + 1/2)
# ===========================================================================

class TestDilationHamiltonian:
    """Tests for self-adjointness and spectral properties of Ĥ."""

    def setup_method(self):
        self.ham = DilationHamiltonian(x_min=1e-3, x_max=1e3, n_points=500)

    # --- Operator application ---

    def test_apply_shape(self):
        """Ĥψ has the same shape as ψ."""
        psi = np.ones(500, dtype=complex)
        hpsi = self.ham.apply(psi)
        assert hpsi.shape == psi.shape

    def test_apply_eigenfunction_check(self):
        """For φ_γ(x) = x^{-1/2 + iγ}, Ĥφ_γ ≈ γ φ_γ in the interior."""
        gamma = 14.135  # First Riemann zero imaginary part (approximately)
        x = self.ham.x_grid
        phi = np.array([self.ham.eigenfunction(xi, gamma) for xi in x])
        Hphi = self.ham.apply(phi)
        # Compare in interior (avoid boundary derivative artefacts)
        interior = slice(50, 450)
        ratio = Hphi[interior] / (phi[interior] + 1e-30j)
        # Eigenvalue should be ≈ gamma (real); use generous tolerance for finite grid
        assert np.abs(ratio.real - gamma).mean() < 0.5  # numerical grid tolerance
        assert np.abs(ratio.imag).mean() < 0.5

    def test_eigenfunction_real_eigenvalue(self):
        """The eigenvalue ratio Ĥφ_γ/φ_γ has negligible imaginary part."""
        gamma = 14.135
        x = self.ham.x_grid
        phi = np.array([self.ham.eigenfunction(xi, gamma) for xi in x])
        Hphi = self.ham.apply(phi)
        interior = slice(100, 400)
        ratio = Hphi[interior] / (phi[interior] + 1e-30j)
        # Imaginary part of eigenvalue should be small
        assert np.abs(ratio.imag).mean() < 0.5

    # --- Unitary group ---

    def test_unitary_group_identity(self):
        """U(0)ψ = ψ."""
        psi = np.exp(-((np.log(self.ham.x_grid)) ** 2)).astype(complex)
        Ut_psi = self.ham.unitary_group(psi, 0.0)
        assert np.allclose(Ut_psi, psi, atol=1e-10)

    def test_unitary_group_norm_preservation(self):
        """‖U(t)ψ‖_{L²(dx)} ≈ ‖ψ‖_{L²(dx)} for all t."""
        psi = np.exp(-((np.log(self.ham.x_grid) - 1.0) ** 2) / 0.5).astype(complex)
        x = self.ham.x_grid
        dx_log = self.ham.dx_log

        def lebesgue_norm(f):
            # L²(dx) norm: ∫|f|² dx = ∫|f|² x d(log x)
            return np.sqrt(abs(np.trapezoid(np.conj(f) * f * x, dx=dx_log)))

        norm0 = lebesgue_norm(psi)
        for t in [0.1, 0.3, -0.2]:
            norm_t = lebesgue_norm(self.ham.unitary_group(psi, t))
            # Allow 1 % tolerance due to boundary interpolation effects
            assert abs(norm_t / norm0 - 1.0) < 0.01, (
                f"Norm ratio at t={t}: {norm_t/norm0:.6f}"
            )

    # --- Self-adjointness ---

    def test_self_adjointness_verification(self):
        """verify_self_adjointness returns is_self_adjoint=True."""
        result = self.ham.verify_self_adjointness()
        assert isinstance(result, SelfAdjointnessResult)
        assert result.is_self_adjoint, (
            f"Self-adjointness check failed:\n"
            f"  symmetry_error={result.inner_product_symmetry:.2e}\n"
            f"  unitarity_error={result.unitary_group_property:.2e}\n"
            f"  stone_ok={result.stone_theorem_satisfied}"
        )

    def test_inner_product_symmetry(self):
        """⟨Ĥφ, ψ⟩_{L²(dx)} ≈ ⟨φ, Ĥψ⟩_{L²(dx)} for smooth test functions."""
        result = self.ham.verify_self_adjointness()
        assert result.inner_product_symmetry < 1e-2

    def test_stone_theorem_satisfied(self):
        """U(t) → Id as t → 0 (Stone's theorem continuity condition)."""
        result = self.ham.verify_self_adjointness()
        assert result.stone_theorem_satisfied


# ===========================================================================
# V. Fredholm determinant = ξ(s)
# ===========================================================================

class TestFredholmXiIdentity:
    """Tests for det(I − K_s) = ξ(s)."""

    def test_xi_function_symmetry(self):
        """ξ(s) = ξ(1-s) for all s."""
        for s in [0.3 + 2j, 0.5 + 14.135j, 0.7 + 5j]:
            xi_s = xi_function(s)
            xi_1ms = xi_function(1 - s)
            assert abs(xi_s - xi_1ms) / (abs(xi_s) + 1e-30) < 1e-6, (
                f"ξ symmetry at s={s}: xi(s)={xi_s}, xi(1-s)={xi_1ms}"
            )

    def test_xi_function_real_on_critical_line(self):
        """ξ(1/2 + iγ) is real for real γ (up to numerical precision)."""
        for gamma in [14.135, 21.022, 25.011]:
            s = 0.5 + 1j * gamma
            xi_val = xi_function(s)
            # On the critical line ξ is real (up to floating-point errors)
            assert abs(xi_val.imag) < abs(xi_val.real) * 0.01 + 1e-8

    def test_fredholm_approx_matches_xi(self):
        """Fredholm approximation ≈ ξ(s) with a small Euler-product truncation."""
        primes = list(_sieve(300).tolist())
        for s in [2.0 + 0j, 3.0 + 1j, 1.5 + 3j]:
            xi_val = xi_function(s)
            fred_val = fredholm_determinant_approx(s, primes=primes)
            if abs(xi_val) > 1e-10:
                rel_err = abs(xi_val - fred_val) / abs(xi_val)
                assert rel_err < 0.05, (
                    f"Fredholm vs ξ at s={s}: xi={xi_val:.4f}, "
                    f"fred={fred_val:.4f}, rel_err={rel_err:.4f}"
                )

    def test_verify_fredholm_xi_identity(self):
        """verify_fredholm_xi_identity returns verified=True at non-zero points."""
        primes = list(_sieve(200).tolist())
        # Use points away from zeros of ξ for well-defined relative error
        s_values = [2.0 + 0j, 1.5 + 3j, 2.0 + 5j, 3.0 + 1j]
        results = verify_fredholm_xi_identity(s_values=s_values, primes=primes)
        assert len(results) > 0
        # At least 3 out of 4 test points should verify
        n_verified = sum(1 for r in results if r.identity_verified)
        assert n_verified >= 3, (
            f"Only {n_verified}/{len(results)} Fredholm-ξ checks passed:\n"
            + "\n".join(
                f"  s={r.s}, rel_err={r.relative_error:.4f}"
                for r in results
            )
        )

    def test_fredholm_xi_result_structure(self):
        """FredholmXiResult has correct fields."""
        results = verify_fredholm_xi_identity(
            s_values=[0.5 + 14.135j], primes=list(_sieve(100).tolist())
        )
        r = results[0]
        assert isinstance(r, FredholmXiResult)
        assert isinstance(r.s, complex)
        assert isinstance(r.relative_error, float)
        assert r.relative_error >= 0


# ===========================================================================
# Integration: full validation
# ===========================================================================

class TestFullValidation:
    """Integration test for validate_adelic_scaling_flow."""

    def test_full_validation_passes(self):
        """validate_adelic_scaling_flow returns all_ok=True."""
        result = validate_adelic_scaling_flow(
            primes=small_primes(),
            n_orbits_max_period=4.0,
            verbose=False,
        )
        assert result["all_ok"], (
            "Full validation failed:\n" + str(result)
        )

    def test_validation_contains_expected_keys(self):
        """Validation result contains all expected keys."""
        result = validate_adelic_scaling_flow(
            primes=small_primes(),
            n_orbits_max_period=3.0,
            verbose=False,
        )
        expected_keys = [
            "phase_space_ok",
            "haar_measure_ok",
            "orbit_rigidity_ok",
            "n_primitive_orbits",
            "primitive_orbits",
            "self_adjoint_ok",
            "fredholm_xi_ok",
            "qcal_psi",
            "all_ok",
        ]
        for key in expected_keys:
            assert key in result, f"Missing key: {key}"

    def test_qcal_psi_is_one(self):
        """Coherence Ψ = 1.0 when all checks pass."""
        result = validate_adelic_scaling_flow(
            primes=small_primes(),
            n_orbits_max_period=3.0,
            verbose=False,
        )
        assert result["qcal_psi"] == 1.0

    def test_primitive_orbits_are_primes(self):
        """Primitive orbit primes match the input prime list."""
        primes = [2, 3, 5]
        result = validate_adelic_scaling_flow(
            primes=primes,
            n_orbits_max_period=np.log(5) + 0.01,
            verbose=False,
        )
        primitive_primes = sorted([p for p, _ in result["primitive_orbits"]])
        assert primitive_primes == primes


# ===========================================================================
# Utility: prime sieve
# ===========================================================================

class TestSieve:
    """Tests for the internal prime sieve."""

    def test_sieve_small(self):
        """_sieve(10) returns [2, 3, 5, 7]."""
        assert list(_sieve(10)) == [2, 3, 5, 7]

    def test_sieve_empty(self):
        """_sieve(1) returns empty array."""
        assert len(_sieve(1)) == 0

    def test_sieve_primes_only(self):
        """All numbers returned by _sieve are prime."""
        primes = _sieve(100)
        for p in primes:
            assert all(p % d != 0 for d in range(2, int(p**0.5) + 1))
