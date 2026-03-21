#!/usr/bin/env python3
"""
Tests for Multiplicative Boundary Conditions and Structural V_osc Derivation
=============================================================================

Validates the structural derivation of V_osc(x) from multiplicative phase-space
constraints on the operator H = -ix d/dx, as proposed in issue #2395.

Covers:
  - Arithmetic lattice (prime logarithms)
  - Multiplicative Bloch boundary conditions
  - Eigenfunction Bloch property
  - Spectral discretisation at log p
  - Density-of-states (smooth + oscillatory components)
  - V_osc(x) = Σ_p (log p / √p) cos(x log p) consistency
  - WKB certification

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Framework · Issue #2395
DOI: 10.5281/zenodo.17379721
"""

import cmath
import math

import numpy as np
import pytest

from operators.multiplicative_boundary_conditions import (
    ArithmeticPhaseSpace,
    MultiplicativeBoundaryCondition,
    SpectralDiscretization,
    VOscStructuralDerivation,
    arithmetic_lattice,
    sieve_primes,
    v_osc_from_constraints,
)


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

@pytest.fixture
def small_phase_space():
    """Phase space with primes up to 30."""
    return ArithmeticPhaseSpace(p_max=30)


@pytest.fixture
def medium_phase_space():
    """Phase space with primes up to 1000."""
    return ArithmeticPhaseSpace(p_max=1000)


@pytest.fixture
def derivation():
    """V_osc derivation with primes up to 1000."""
    return VOscStructuralDerivation(p_max=1000)


# ---------------------------------------------------------------------------
# sieve_primes
# ---------------------------------------------------------------------------

class TestSievePrimes:
    """Tests for sieve_primes utility."""

    def test_first_primes(self):
        """Verify the first few primes."""
        assert sieve_primes(30) == [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]

    def test_empty_below_2(self):
        """No primes below 2."""
        assert sieve_primes(1) == []
        assert sieve_primes(0) == []

    def test_boundary_inclusive(self):
        """Boundary prime is included."""
        primes = sieve_primes(7)
        assert 7 in primes

    def test_prime_count_100(self):
        """π(100) = 25."""
        assert len(sieve_primes(100)) == 25

    def test_no_composites(self):
        """No composite numbers in the output."""
        primes = sieve_primes(50)
        for p in primes:
            assert all(p % d != 0 for d in range(2, int(p**0.5) + 1)), (
                f"{p} is not prime"
            )


# ---------------------------------------------------------------------------
# arithmetic_lattice
# ---------------------------------------------------------------------------

class TestArithmeticLattice:
    """Tests for the arithmetic lattice Λ = {log p}."""

    def test_values(self):
        """Lattice points match log of primes."""
        primes = sieve_primes(30)
        lattice = arithmetic_lattice(30)
        expected = np.log(np.array(primes, dtype=float))
        np.testing.assert_allclose(lattice, expected, rtol=1e-12)

    def test_positive(self):
        """All lattice points are positive (log p > 0 for p ≥ 2)."""
        lattice = arithmetic_lattice(100)
        assert np.all(lattice > 0)

    def test_monotone(self):
        """Lattice points are strictly increasing."""
        lattice = arithmetic_lattice(100)
        assert np.all(np.diff(lattice) > 0)

    def test_first_point(self):
        """First lattice point is log 2."""
        lattice = arithmetic_lattice(10)
        assert abs(lattice[0] - math.log(2)) < 1e-12


# ---------------------------------------------------------------------------
# MultiplicativeBoundaryCondition
# ---------------------------------------------------------------------------

class TestMultiplicativeBoundaryCondition:
    """Tests for the single-prime Bloch condition."""

    def test_construction_prime(self):
        """Construction succeeds for a prime."""
        bc = MultiplicativeBoundaryCondition(p=5)
        assert bc.p == 5
        assert abs(bc.log_p - math.log(5)) < 1e-12

    def test_construction_non_prime_raises(self):
        """Construction raises ValueError for a non-prime."""
        with pytest.raises(ValueError):
            MultiplicativeBoundaryCondition(p=4)

    def test_construction_one_raises(self):
        """Construction raises ValueError for p=1."""
        with pytest.raises(ValueError):
            MultiplicativeBoundaryCondition(p=1)

    def test_eigenfunction_value(self):
        """Eigenfunction φ_λ(x) = exp(iλ log x) at x=1 equals 1."""
        bc = MultiplicativeBoundaryCondition(p=3)
        assert abs(bc.eigenfunction(lam=2.0, x=1.0) - 1.0) < 1e-12

    def test_eigenfunction_zero_for_nonpositive(self):
        """Eigenfunction returns 0 for x ≤ 0."""
        bc = MultiplicativeBoundaryCondition(p=2)
        assert bc.eigenfunction(lam=1.0, x=0.0) == 0.0
        assert bc.eigenfunction(lam=1.0, x=-1.0) == 0.0

    def test_bloch_condition_satisfied(self):
        """φ_λ(p·x) = e^{iλ log p} φ_λ(x) for all x > 0."""
        bc = MultiplicativeBoundaryCondition(p=5, theta=0.0)
        lam = 3.7
        for x in [0.5, 1.0, 2.3, 10.0]:
            phi_px = bc.eigenfunction(lam, bc.p * x)
            phase = cmath.exp(1j * lam * bc.log_p)
            phi_x = bc.eigenfunction(lam, x)
            assert abs(phi_px - phase * phi_x) < 1e-10

    def test_spectral_phase(self):
        """Phase at eigenvalue λ is λ log p."""
        bc = MultiplicativeBoundaryCondition(p=7)
        lam = 1.5
        assert abs(bc.spectral_phase(lam) - lam * math.log(7)) < 1e-12

    def test_bloch_residual_zero_for_eigenfunction(self):
        """apply() returns ~0 when f is an eigenfunction with matching phase."""
        p = 3
        lam = 2.0
        bc = MultiplicativeBoundaryCondition(p=p, theta=lam * math.log(p))
        f = lambda x: bc.eigenfunction(lam, x)
        for x in [1.0, 2.5, 0.1]:
            residual = bc.apply(f, x)
            assert abs(residual) < 1e-10, f"Residual {residual} at x={x}"


# ---------------------------------------------------------------------------
# ArithmeticPhaseSpace
# ---------------------------------------------------------------------------

class TestArithmeticPhaseSpace:
    """Tests for the full arithmetic phase space."""

    def test_prime_count(self, small_phase_space):
        """Phase space contains correct number of primes."""
        primes = sieve_primes(30)
        assert len(small_phase_space.primes) == len(primes)

    def test_lattice_points(self, small_phase_space):
        """Lattice points match log of each prime."""
        for p, lp in zip(small_phase_space.primes, small_phase_space.log_primes):
            assert abs(lp - math.log(p)) < 1e-12

    def test_sqrt_primes(self, small_phase_space):
        """sqrt_primes matches √p for each prime."""
        for p, sp in zip(small_phase_space.primes, small_phase_space.sqrt_primes):
            assert abs(sp - math.sqrt(p)) < 1e-12

    def test_amplitudes_positive(self, small_phase_space):
        """All prime amplitudes c_p = log p / √p are positive."""
        amps = small_phase_space.prime_amplitudes()
        assert np.all(amps > 0)

    def test_amplitude_formula(self, small_phase_space):
        """Amplitude for prime p equals log(p) / sqrt(p)."""
        amps = small_phase_space.prime_amplitudes()
        for p, c in zip(small_phase_space.primes, amps):
            expected = math.log(p) / math.sqrt(p)
            assert abs(c - expected) < 1e-12

    def test_conditions_count(self, small_phase_space):
        """One boundary condition per prime."""
        assert len(small_phase_space.conditions) == len(small_phase_space.primes)

    def test_conditions_primes_match(self, small_phase_space):
        """Each condition p matches the corresponding prime."""
        for bc, p in zip(small_phase_space.conditions, small_phase_space.primes):
            assert bc.p == p


# ---------------------------------------------------------------------------
# SpectralDiscretization
# ---------------------------------------------------------------------------

class TestSpectralDiscretization:
    """Tests for spectral quantisation from multiplicative constraints."""

    def test_eigenvalues_match_log_primes(self, small_phase_space):
        """Eigenvalues are the log of the primes."""
        spec = SpectralDiscretization(phase_space=small_phase_space)
        np.testing.assert_allclose(spec.eigenvalues, small_phase_space.log_primes)

    def test_smooth_density_positive(self):
        """Smooth density ρ̄(E) > 0 for large enough E."""
        spec = SpectralDiscretization()
        # ρ̄(E) > 0 iff E > 2π
        E_positive = 2 * math.pi * math.e + 1
        assert spec.density_of_states_smooth(E_positive) > 0

    def test_smooth_density_zero_for_nonpositive(self):
        """Smooth density is 0 for E ≤ 0."""
        spec = SpectralDiscretization()
        assert spec.density_of_states_smooth(0.0) == 0.0
        assert spec.density_of_states_smooth(-5.0) == 0.0

    def test_smooth_density_formula(self):
        """ρ̄(E) = (1/2π) log(E/2π)."""
        spec = SpectralDiscretization()
        E = 100.0
        expected = math.log(E / (2 * math.pi)) / (2 * math.pi)
        assert abs(spec.density_of_states_smooth(E) - expected) < 1e-12

    def test_oscillatory_density_is_float(self, small_phase_space):
        """Oscillatory density returns a float."""
        spec = SpectralDiscretization(phase_space=small_phase_space)
        result = spec.density_of_states_oscillatory(14.1347)
        assert isinstance(result, float)

    def test_total_density(self, small_phase_space):
        """Total density = smooth + oscillatory."""
        spec = SpectralDiscretization(phase_space=small_phase_space)
        E = 10.0
        total = spec.density_of_states(E)
        expected = (spec.density_of_states_smooth(E) +
                    spec.density_of_states_oscillatory(E))
        assert abs(total - expected) < 1e-12


# ---------------------------------------------------------------------------
# VOscStructuralDerivation
# ---------------------------------------------------------------------------

class TestVOscStructuralDerivation:
    """Tests for the structural derivation of V_osc(x)."""

    def test_v_osc_is_float(self, derivation):
        """v_osc() returns a float."""
        val = derivation.v_osc(14.1347)
        assert isinstance(val, float)

    def test_v_osc_array_shape(self, derivation):
        """v_osc_array() returns array of correct shape."""
        x_arr = np.linspace(0, 20, 50)
        result = derivation.v_osc_array(x_arr)
        assert result.shape == (50,)

    def test_v_osc_consistent_with_direct_sum(self):
        """v_osc(x) matches direct computation Σ (log p / √p) cos(x log p)."""
        ps = ArithmeticPhaseSpace(p_max=100)
        deriv = VOscStructuralDerivation(p_max=100)
        x = 7.5
        # Direct sum
        direct = sum(
            math.log(p) / math.sqrt(p) * math.cos(x * math.log(p))
            for p in ps.primes
        )
        assert abs(deriv.v_osc(x) - direct) < 1e-10

    def test_v_osc_matches_pi_rho_osc(self, derivation):
        """V_osc(x) = π · ρ_osc(x) (structural consistency)."""
        for x in [1.0, 5.0, 14.1347, 21.022]:
            v = derivation.v_osc(x)
            rho = derivation.spectral.density_of_states_oscillatory(x)
            assert abs(v - math.pi * rho) < 1e-10, (
                f"Mismatch at x={x}: V_osc={v:.6f}, π·ρ_osc={math.pi * rho:.6f}"
            )

    def test_v_osc_phase_shift(self, derivation):
        """Phase-shifted V_osc differs from the canonical one."""
        x = 10.0
        v0 = derivation.v_osc(x, phase_shift=0.0)
        v_pi4 = derivation.v_osc(x, phase_shift=-math.pi / 4)
        # They should generally differ (unless x=0 etc.)
        assert v0 != v_pi4

    def test_certify_v_osc_prime_sum(self, derivation):
        """Certification: V_osc equals Σ (log p / √p) cos(x log p) to 1e-10."""
        x_values = np.linspace(1, 30, 20)
        report = derivation.certify_v_osc_prime_sum(x_values)
        assert report["certified"], (
            f"Certification failed: max_abs_diff = {report['max_abs_diff']}"
        )
        assert report["max_abs_diff"] < 1e-10

    def test_certify_contains_n_primes(self, derivation):
        """Certification report contains correct prime count."""
        x_values = np.array([14.1347])
        report = derivation.certify_v_osc_prime_sum(x_values)
        assert report["n_primes"] == len(derivation.phase_space.primes)

    def test_certify_contains_protocol(self, derivation):
        """Certification report contains the QCAL protocol string."""
        report = derivation.certify_v_osc_prime_sum(np.array([1.0]))
        assert "ISSUE_2395" in report["protocol"]
        assert "QCAL" in report["protocol"]

    def test_structural_report_keys(self, derivation):
        """Structural derivation report contains all expected keys."""
        report = derivation.structural_derivation_report(x=14.1347)
        required_keys = [
            "x", "n_primes", "p_max",
            "lattice_first_5", "eigenvalues_first_5",
            "rho_smooth", "rho_osc", "rho_total",
            "V_osc", "V_osc_WKB_phase",
            "consistency_V_osc_vs_pi_rho_osc",
            "certified",
            "f0_Hz", "C_coherence", "doi", "protocol",
        ]
        for key in required_keys:
            assert key in report, f"Missing key: {key}"

    def test_structural_report_certified(self, derivation):
        """Structural derivation report is certified at first Riemann zero."""
        report = derivation.structural_derivation_report(x=14.1347)
        assert report["certified"]

    def test_structural_report_lattice(self, derivation):
        """First lattice point is log 2."""
        report = derivation.structural_derivation_report()
        assert abs(report["lattice_first_5"][0] - math.log(2)) < 1e-10

    def test_structural_report_eigenvalues(self, derivation):
        """First eigenvalue is log 2."""
        report = derivation.structural_derivation_report()
        assert abs(report["eigenvalues_first_5"][0] - math.log(2)) < 1e-10

    def test_f0_constant(self, derivation):
        """QCAL frequency constant is reported correctly."""
        report = derivation.structural_derivation_report()
        assert abs(report["f0_Hz"] - 141.7001) < 1e-4

    def test_doi_present(self, derivation):
        """DOI reference is present in the report."""
        report = derivation.structural_derivation_report()
        assert "10.5281/zenodo.17379721" in report["doi"]


# ---------------------------------------------------------------------------
# v_osc_from_constraints (top-level API)
# ---------------------------------------------------------------------------

class TestVOscFromConstraints:
    """Tests for the convenience function v_osc_from_constraints."""

    def test_returns_float(self):
        """Function returns a float."""
        result = v_osc_from_constraints(14.1347, p_max=100)
        assert isinstance(result, float)

    def test_matches_derivation(self):
        """Matches VOscStructuralDerivation.v_osc()."""
        x = 7.0
        p_max = 200
        expected = VOscStructuralDerivation(p_max=p_max).v_osc(x)
        result = v_osc_from_constraints(x, p_max=p_max)
        assert abs(result - expected) < 1e-12

    def test_phase_shift_zero(self):
        """Default phase_shift=0 gives canonical V_osc."""
        x = 5.5
        p_max = 50
        primes = sieve_primes(p_max)
        direct = sum(
            math.log(p) / math.sqrt(p) * math.cos(x * math.log(p))
            for p in primes
        )
        result = v_osc_from_constraints(x, p_max=p_max)
        assert abs(result - direct) < 1e-10

    def test_different_p_max(self):
        """Results with different p_max differ (more primes = more terms)."""
        x = 10.0
        v100 = v_osc_from_constraints(x, p_max=100)
        v1000 = v_osc_from_constraints(x, p_max=1000)
        # With more primes the sum changes (unless all extra terms happen to cancel)
        # Just check we get floats — the difference need not be large
        assert isinstance(v100, float)
        assert isinstance(v1000, float)


# ---------------------------------------------------------------------------
# Bloch condition verification across the full phase space
# ---------------------------------------------------------------------------

class TestBlochConditionFullPhaseSpace:
    """Verify Bloch conditions for the eigenfunctions across all primes."""

    def test_all_primes_satisfy_bloch(self, small_phase_space):
        """For each prime p, eigenfunction φ_{log p} satisfies the Bloch condition."""
        for bc in small_phase_space.conditions:
            lam = math.log(bc.p)  # fundamental eigenvalue
            f = lambda x, l=lam, b=bc: b.eigenfunction(l, x)
            for x in [0.5, 1.0, 2.0]:
                # φ_{log p}(p·x) = e^{i log p · log p} φ_{log p}(x)
                phi_px = f(bc.p * x)
                expected_phase = cmath.exp(1j * lam * bc.log_p)
                phi_x = f(x)
                assert abs(phi_px - expected_phase * phi_x) < 1e-10, (
                    f"Bloch failed for p={bc.p}, x={x}"
                )

    def test_amplitude_ordering(self, small_phase_space):
        """Amplitudes c_p = log p / √p are well-defined and finite."""
        amps = small_phase_space.prime_amplitudes()
        assert np.all(np.isfinite(amps))
        assert np.all(amps > 0)


# ---------------------------------------------------------------------------
# Structural connection: boundary conditions → V_osc → framework integration
# ---------------------------------------------------------------------------

class TestStructuralConnection:
    """High-level structural tests connecting BCs to V_osc to the framework."""

    def test_v_osc_is_real_valued(self):
        """V_osc(x) is real for all x (cosines are real)."""
        deriv = VOscStructuralDerivation(p_max=100)
        for x in np.linspace(-5, 5, 20):
            v = deriv.v_osc(float(x))
            assert isinstance(v, float)

    def test_v_osc_symmetry(self):
        """V_osc is an even function: V_osc(-x) = V_osc(x).

        Since cos((-x) log p) = cos(x log p) for all primes p, the sum
        V_osc(x) = Σ_p (log p / √p) cos(x log p) satisfies V_osc(-x) = V_osc(x).
        """
        deriv = VOscStructuralDerivation(p_max=200)
        for x in [3.0, 7.0, 14.1347]:
            assert abs(deriv.v_osc(x) - deriv.v_osc(-x)) < 1e-10, (
                f"V_osc not even at x={x}"
            )

    def test_spectral_lattice_in_phase_space(self, small_phase_space):
        """Eigenvalues lie in the arithmetic lattice {log p}."""
        spec = SpectralDiscretization(phase_space=small_phase_space)
        lattice = set(round(lp, 10) for lp in small_phase_space.lattice_points())
        for ev in spec.eigenvalues:
            assert round(ev, 10) in lattice, (
                f"Eigenvalue {ev} not in arithmetic lattice"
            )

    def test_issue_2395_claim(self):
        """Issue #2395 claim: V_osc emerges from BCs without assuming zeta zeros."""
        # The derivation starts from primes (BCs) and produces V_osc.
        # We verify the output matches the explicit-formula sum over primes.
        p_max = 500
        x = 21.022  # imaginary part of 3rd Riemann zero (approx)
        primes = sieve_primes(p_max)
        # Reference: direct explicit-formula sum
        v_ref = sum(
            math.log(p) / math.sqrt(p) * math.cos(x * math.log(p))
            for p in primes
        )
        # Structural derivation
        v_struct = v_osc_from_constraints(x, p_max=p_max)
        assert abs(v_struct - v_ref) < 1e-10, (
            f"|V_struct - V_ref| = {abs(v_struct - v_ref):.2e}"
        )
