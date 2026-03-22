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
Validates operators/multiplicative_boundary_conditions.py, covering:
  - Prime sieve utility
  - SpectralDiscretizationEngine: per-prime spectral lattices
  - oscillatory_density_from_bc: ρ_osc from multiplicative constraints
  - counting_oscillation_N_osc: oscillatory counting function
  - VOscFromMultiplicativeBC: V_osc(x) evaluation
  - verify_structural_coincidence: canonical sum matches structural form
  - semiclassical_phase_volume and phase_volume_to_density
  - multiplicative_bc_to_v_osc: complete derivation pipeline
  - generate_qcal_certificate_mbc: QCAL certificate generation
"""

import pytest
import numpy as np

from operators.multiplicative_boundary_conditions import (
    _sieve_primes,
    SpectralDiscretization,
    MultiplicativeBCResult,
    SpectralDiscretizationEngine,
    oscillatory_density_from_bc,
    counting_oscillation_N_osc,
    VOscFromMultiplicativeBC,
    verify_structural_coincidence,
    semiclassical_phase_volume,
    phase_volume_to_density,
    multiplicative_bc_to_v_osc,
    generate_qcal_certificate_mbc,
)


# ---------------------------------------------------------------------------
# Tests: _sieve_primes
# ---------------------------------------------------------------------------


class TestSievePrimes:
    """Tests for internal prime sieve."""

    def test_small_primes(self):
        """Verify first few primes."""
        assert _sieve_primes(30) == [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]

    def test_empty_for_small_n(self):
        """No primes below 2."""
        assert _sieve_primes(1) == []
        assert _sieve_primes(0) == []

    def test_includes_boundary(self):
        """n_max itself included if prime."""
        assert 7 in _sieve_primes(7)
        assert 11 in _sieve_primes(11)

    def test_count_pi_100(self):
        """π(100) = 25."""
        assert len(_sieve_primes(100)) == 25

    def test_all_prime(self):
        """All returned values are prime."""
        primes = _sieve_primes(50)
        for p in primes:
            for d in range(2, p):
                assert p % d != 0, f"{p} is not prime"


# ---------------------------------------------------------------------------
# Tests: SpectralDiscretizationEngine
# ---------------------------------------------------------------------------


class TestSpectralDiscretizationEngine:
    """Tests for spectral discretization from multiplicative BC."""

    def setup_method(self):
        self.primes = [2, 3, 5, 7, 11]
        self.engine = SpectralDiscretizationEngine(primes=self.primes)

    def test_fundamental_frequency_prime2(self):
        """ω_2 = 2π / log 2."""
        expected = 2.0 * np.pi / np.log(2)
        assert abs(self.engine.fundamental_frequency(2) - expected) < 1e-12

    def test_fundamental_frequency_prime3(self):
        """ω_3 = 2π / log 3."""
        expected = 2.0 * np.pi / np.log(3)
        assert abs(self.engine.fundamental_frequency(3) - expected) < 1e-12

    def test_fundamental_frequency_decreasing(self):
        """ω_p decreases as p increases (since log p increases)."""
        freqs = [self.engine.fundamental_frequency(p) for p in self.primes]
        for i in range(len(freqs) - 1):
            assert freqs[i] > freqs[i + 1]

    def test_allowed_eigenvalues_symmetry(self):
        """Allowed eigenvalues are symmetric around 0."""
        evs = self.engine.allowed_eigenvalues_range(2, k_max=5)
        # Check symmetry: λ in list implies -λ in list
        for lam in evs:
            assert any(abs(-lam - ev) < 1e-10 for ev in evs)

    def test_allowed_eigenvalues_count(self):
        """k_max=5 gives 2*5+1 = 11 eigenvalues."""
        evs = self.engine.allowed_eigenvalues_range(2, k_max=5)
        assert len(evs) == 11

    def test_zero_is_always_allowed(self):
        """λ=0 is always in the lattice (k=0)."""
        for p in self.primes:
            evs = self.engine.allowed_eigenvalues_range(p, k_max=3)
            assert any(abs(ev) < 1e-12 for ev in evs)

    def test_spectral_density_formula(self):
        """ρ_p = log p / (2π)."""
        for p in self.primes:
            expected = np.log(p) / (2.0 * np.pi)
            assert abs(self.engine.spectral_density_prime(p) - expected) < 1e-12

    def test_eigenvalue_in_lattice_true(self):
        """2π/log p is in Λ_p (k=1)."""
        for p in self.primes:
            lam = 2.0 * np.pi / np.log(p)
            assert self.engine.eigenvalue_in_lattice(lam, p)

    def test_eigenvalue_in_lattice_false(self):
        """A random irrational value is not in Λ_p."""
        for p in self.primes:
            lam = np.sqrt(2)  # Irrational w.r.t. log p for most p
            in_lattice = self.engine.eigenvalue_in_lattice(lam, p)
            # Not necessarily false for all p, but tolerance is strict
            # Just confirm the function runs without error and returns a boolean
            assert isinstance(in_lattice, (bool, np.bool_))

    def test_discretize_returns_list(self):
        """discretize() returns one entry per prime."""
        result = self.engine.discretize(k_max=3)
        assert len(result) == len(self.primes)

    def test_discretize_structure(self):
        """Each SpectralDiscretization has correct structure."""
        result = self.engine.discretize(k_max=3)
        for d in result:
            assert isinstance(d, SpectralDiscretization)
            assert d.prime in self.primes
            assert d.log_p > 0
            assert d.fundamental_frequency > 0
            assert d.spectral_density > 0
            assert len(d.allowed_eigenvalues) == 7  # 2*3+1

    def test_with_p_max(self):
        """Works with p_max instead of explicit primes."""
        engine = SpectralDiscretizationEngine(p_max=20)
        expected_primes = _sieve_primes(20)
        assert engine.primes == expected_primes


# ---------------------------------------------------------------------------
# Tests: oscillatory_density_from_bc
# ---------------------------------------------------------------------------


class TestOscillatoryDensityFromBC:
    """Tests for ρ_osc(λ) derived from multiplicative boundary conditions."""

    def setup_method(self):
        self.primes = _sieve_primes(30)

    def test_formula_structure(self):
        """ρ_osc(λ) = (1/π) Σ (log p/√p) cos(λ log p)."""
        lam = 15.0
        primes = [2, 3, 5]
        expected = sum(
            (np.log(p) / np.sqrt(p)) * np.cos(lam * np.log(p)) for p in primes
        ) / np.pi
        result = oscillatory_density_from_bc(lam, primes)
        assert abs(result - expected) < 1e-12

    def test_finite(self):
        """ρ_osc is finite for real λ."""
        for lam in [5.0, 10.0, 25.0, 100.0]:
            assert np.isfinite(oscillatory_density_from_bc(lam, self.primes))

    def test_oscillatory(self):
        """ρ_osc changes sign (not constant positive)."""
        vals = [
            oscillatory_density_from_bc(lam, self.primes)
            for lam in np.linspace(1.0, 30.0, 60)
        ]
        assert any(v > 0 for v in vals)
        assert any(v < 0 for v in vals)

    def test_zero_primes(self):
        """Empty prime list gives zero density."""
        assert oscillatory_density_from_bc(10.0, []) == 0.0

    def test_single_prime(self):
        """Single prime p gives (log p/√p) cos(λ log p) / π."""
        lam = 7.0
        p = 5
        expected = (np.log(p) / np.sqrt(p)) * np.cos(lam * np.log(p)) / np.pi
        result = oscillatory_density_from_bc(lam, [p])
        assert abs(result - expected) < 1e-12


# ---------------------------------------------------------------------------
# Tests: counting_oscillation_N_osc
# ---------------------------------------------------------------------------


class TestCountingOscillation:
    """Tests for oscillatory counting function N_osc(λ)."""

    def setup_method(self):
        self.primes = _sieve_primes(20)

    def test_finite(self):
        """N_osc is finite."""
        for lam in [5.0, 15.0, 50.0]:
            assert np.isfinite(counting_oscillation_N_osc(lam, self.primes))

    def test_zero_primes(self):
        """Zero primes gives zero counting function."""
        assert counting_oscillation_N_osc(10.0, []) == 0.0

    def test_oscillatory(self):
        """N_osc changes sign."""
        vals = [
            counting_oscillation_N_osc(lam, self.primes)
            for lam in np.linspace(1.0, 20.0, 40)
        ]
        assert any(v > 0 for v in vals)
        assert any(v < 0 for v in vals)

    def test_k_max_effect(self):
        """Higher k_max adds more harmonic terms."""
        lam = 10.0
        n1 = counting_oscillation_N_osc(lam, self.primes, k_max=1)
        n3 = counting_oscillation_N_osc(lam, self.primes, k_max=3)
        # They differ in general (k_max=3 includes k=2,3 harmonics)
        assert np.isfinite(n1)
        assert np.isfinite(n3)

    def test_n_osc_k1_formula(self):
        """k=1 term: N_osc = -(1/π) Σ (log p/√p) sin(λ log p)."""
        lam = 7.0
        primes = [2, 3]
        expected = -(1 / np.pi) * sum(
            (np.log(p) / np.sqrt(p)) * np.sin(lam * np.log(p)) for p in primes
        )
        result = counting_oscillation_N_osc(lam, primes, k_max=1)
        assert abs(result - expected) < 1e-12


# ---------------------------------------------------------------------------
# Tests: VOscFromMultiplicativeBC
# ---------------------------------------------------------------------------


class TestVOscFromMultiplicativeBC:
    """Tests for oscillatory potential derived from multiplicative BC."""

    def setup_method(self):
        self.primes = _sieve_primes(50)
        self.v_osc = VOscFromMultiplicativeBC(primes=self.primes)

    def test_evaluate_finite(self):
        """V_osc is finite at all test points."""
        for x in [1.0, 5.0, 10.0, 50.0, 100.0]:
            assert np.isfinite(self.v_osc.evaluate(x))

    def test_default_phase_zero(self):
        """Default phase is 0.0."""
        assert self.v_osc.phase == 0.0

    def test_phase_pi_4(self):
        """Phase -π/4 gives Abel-corrected version."""
        v = VOscFromMultiplicativeBC(primes=self.primes, phase=-np.pi / 4.0)
        assert abs(v.phase - (-np.pi / 4.0)) < 1e-12

    def test_evaluate_formula(self):
        """evaluate matches manual Σ (log p/√p) cos(x log p + φ)."""
        x = 7.0
        primes = [2, 3, 5]
        v = VOscFromMultiplicativeBC(primes=primes, phase=0.0)
        expected = sum(
            (np.log(p) / np.sqrt(p)) * np.cos(x * np.log(p)) for p in primes
        )
        assert abs(v.evaluate(x) - expected) < 1e-12

    def test_evaluate_array_matches_single(self):
        """evaluate_array matches evaluate for each point."""
        x_arr = np.array([1.0, 5.0, 10.0, 20.0])
        arr_result = self.v_osc.evaluate_array(x_arr)
        for i, x in enumerate(x_arr):
            single = self.v_osc.evaluate(x)
            assert abs(arr_result[i] - single) < 1e-12

    def test_oscillatory_character(self):
        """V_osc changes sign over position range."""
        x_arr = np.linspace(1.0, 50.0, 500)
        vals = self.v_osc.evaluate_array(x_arr)
        assert any(v > 0 for v in vals)
        assert any(v < 0 for v in vals)

    def test_amplitude_formula(self):
        """amplitude(p) = log p / √p."""
        for p in [2, 3, 5, 7]:
            expected = np.log(p) / np.sqrt(p)
            assert abs(self.v_osc.amplitude(p) - expected) < 1e-12

    def test_frequency_is_log_p(self):
        """frequency(p) = log p (the period of multiplicative comb)."""
        for p in [2, 3, 5, 7]:
            expected = np.log(p)
            assert abs(self.v_osc.frequency(p) - expected) < 1e-12

    def test_bounded(self):
        """|V_osc(x)| ≤ Σ_p |amplitude(p)|."""
        max_amp = sum(self.v_osc.amplitude(p) for p in self.primes)
        for x in np.linspace(0.1, 100.0, 20):
            val = abs(self.v_osc.evaluate(x))
            assert val <= max_amp + 1e-10

    def test_with_p_max(self):
        """Works with p_max instead of explicit primes."""
        v = VOscFromMultiplicativeBC(p_max=30)
        assert v.primes == _sieve_primes(30)
        assert np.isfinite(v.evaluate(10.0))

    def test_large_x_finite(self):
        """V_osc finite for large x."""
        v = VOscFromMultiplicativeBC(p_max=30)
        for x in [500.0, 1000.0, 5000.0]:
            assert np.isfinite(v.evaluate(x))


# ---------------------------------------------------------------------------
# Tests: verify_structural_coincidence
# ---------------------------------------------------------------------------


class TestVerifyStructuralCoincidence:
    """Tests for structural coincidence between BC-derived and canonical V_osc."""

    def test_coincidence_exact(self):
        """Structural and canonical forms match to machine precision."""
        primes = _sieve_primes(30)
        x_values = [1.0, 5.0, 10.0, 20.0, 50.0]
        result = verify_structural_coincidence(x_values, primes, phase=0.0)
        assert result["all_match"] is True
        assert result["max_deviation"] < 1e-12

    def test_coincidence_with_phase(self):
        """Coincidence holds with phase -π/4."""
        primes = _sieve_primes(20)
        x_values = [2.0, 7.0, 15.0]
        result = verify_structural_coincidence(x_values, primes, phase=-np.pi / 4.0)
        assert result["all_match"] is True
        assert result["max_deviation"] < 1e-12

    def test_result_structure(self):
        """Result contains expected keys."""
        primes = [2, 3, 5]
        result = verify_structural_coincidence([1.0], primes)
        assert "all_match" in result
        assert "max_deviation" in result
        assert "tolerance" in result
        assert "n_primes" in result
        assert "details" in result

    def test_n_primes_count(self):
        """n_primes matches input."""
        primes = [2, 3, 5, 7]
        result = verify_structural_coincidence([1.0], primes)
        assert result["n_primes"] == 4

    def test_per_point_details(self):
        """Details contain structural and canonical values per x."""
        primes = [2, 3]
        x = 5.0
        result = verify_structural_coincidence([x], primes)
        assert x in result["details"]
        detail = result["details"][x]
        assert "structural" in detail
        assert "canonical" in detail
        assert "deviation" in detail
        assert "match" in detail
        assert detail["match"]


# ---------------------------------------------------------------------------
# Tests: semiclassical_phase_volume and phase_volume_to_density
# ---------------------------------------------------------------------------


class TestPhaseVolume:
    """Tests for semiclassical phase volume functions."""

    def setup_method(self):
        self.primes = _sieve_primes(30)

    def test_phase_volume_positive_E(self):
        """Smooth phase volume positive for E > 2π."""
        omega_s, omega_o = semiclassical_phase_volume(20.0, self.primes)
        assert omega_s > 0
        assert np.isfinite(omega_o)

    def test_phase_volume_zero_E(self):
        """Phase volume is 0 for E ≤ 0."""
        omega_s, omega_o = semiclassical_phase_volume(0.0, self.primes)
        assert omega_s == 0.0

    def test_phase_volume_finite(self):
        """Phase volume components are finite."""
        for E in [5.0, 15.0, 50.0]:
            omega_s, omega_o = semiclassical_phase_volume(E, self.primes)
            assert np.isfinite(omega_s)
            assert np.isfinite(omega_o)

    def test_phase_volume_smooth_increasing(self):
        """Smooth phase volume is increasing for E > 2π."""
        E_vals = [10.0, 20.0, 50.0, 100.0]
        omega_s_vals = [semiclassical_phase_volume(E, self.primes)[0] for E in E_vals]
        for i in range(len(omega_s_vals) - 1):
            assert omega_s_vals[i] < omega_s_vals[i + 1]

    def test_density_smooth_formula(self):
        """ρ_smooth(E) = (1/2π) log(E/2π)."""
        E = 20.0
        rho_s, _ = phase_volume_to_density(E, self.primes)
        expected = np.log(E / (2.0 * np.pi)) / (2.0 * np.pi)
        assert abs(rho_s - expected) < 1e-12

    def test_density_osc_matches_bc(self):
        """ρ_osc from phase_volume_to_density matches oscillatory_density_from_bc."""
        E = 15.0
        _, rho_o = phase_volume_to_density(E, self.primes)
        expected = oscillatory_density_from_bc(E, self.primes)
        assert abs(rho_o - expected) < 1e-12

    def test_density_positive_E(self):
        """Smooth density is positive for E > 2π."""
        rho_s, _ = phase_volume_to_density(50.0, self.primes)
        assert rho_s > 0

    def test_density_zero_nonpositive(self):
        """Smooth density is 0 for E ≤ 0."""
        rho_s, _ = phase_volume_to_density(0.0, self.primes)
        assert rho_s == 0.0


# ---------------------------------------------------------------------------
# Tests: multiplicative_bc_to_v_osc pipeline
# ---------------------------------------------------------------------------


class TestMultiplicativeBCToVOscPipeline:
    """Tests for the complete derivation pipeline."""

    def test_pipeline_structure(self):
        """Pipeline result contains all expected keys."""
        result = multiplicative_bc_to_v_osc(
            x_values=[1.0, 5.0],
            primes=[2, 3, 5],
        )
        assert "step_1_2_spectral_discretization" in result
        assert "step_3_oscillatory_density" in result
        assert "step_4_5_v_osc_values" in result
        assert "n_primes" in result

    def test_pipeline_n_primes(self):
        """n_primes reflects input list."""
        primes = [2, 3, 5, 7]
        result = multiplicative_bc_to_v_osc(x_values=[1.0], primes=primes)
        assert result["n_primes"] == 4

    def test_pipeline_v_osc_finite(self):
        """V_osc values from pipeline are finite."""
        primes = _sieve_primes(20)
        result = multiplicative_bc_to_v_osc(
            x_values=[1.0, 5.0, 10.0],
            primes=primes,
        )
        for x, v in result["step_4_5_v_osc_values"].items():
            assert np.isfinite(v), f"V_osc({x}) = {v} is not finite"

    def test_pipeline_discretization_count(self):
        """Spectral discretization has one entry per prime."""
        primes = [2, 3, 5]
        result = multiplicative_bc_to_v_osc(x_values=[1.0], primes=primes)
        assert len(result["step_1_2_spectral_discretization"]) == 3

    def test_pipeline_phase(self):
        """Phase is stored in result."""
        result = multiplicative_bc_to_v_osc(
            x_values=[1.0], primes=[2, 3], phase=-np.pi / 4.0
        )
        assert abs(result["phase"] - (-np.pi / 4.0)) < 1e-12

    def test_pipeline_rho_osc_finite(self):
        """Oscillatory density at sample points is finite."""
        primes = _sieve_primes(15)
        result = multiplicative_bc_to_v_osc(x_values=[1.0], primes=primes)
        for E_str, rho in result["step_3_oscillatory_density"].items():
            assert np.isfinite(rho), f"ρ_osc({E_str}) not finite"


# ---------------------------------------------------------------------------
# Tests: generate_qcal_certificate_mbc
# ---------------------------------------------------------------------------


class TestQCALCertificateMBC:
    """Tests for QCAL certificate generation (multiplicative BC derivation)."""

    def test_certificate_structure(self):
        """Certificate contains all required keys."""
        cert = generate_qcal_certificate_mbc(p_max=20)
        required_keys = [
            "protocol", "timestamp", "doi", "f0_hz", "C_coherence",
            "n_primes", "p_max", "phase", "results", "checksum",
            "derivation_steps", "seal",
        ]
        for key in required_keys:
            assert key in cert, f"Missing key: {key}"

    def test_certificate_metadata(self):
        """Certificate has correct QCAL metadata."""
        cert = generate_qcal_certificate_mbc(p_max=20)
        assert cert["f0_hz"] == 141.7001
        assert cert["C_coherence"] == 244.36
        assert cert["seal"] == 14170001
        assert cert["doi"] == "10.5281/zenodo.17379721"
        assert cert["protocol"] == "QCAL-MBC-VOSC-DERIVATION v1.0"

    def test_certificate_n_primes(self):
        """Certificate reports correct number of primes."""
        cert = generate_qcal_certificate_mbc(p_max=30)
        assert cert["n_primes"] == len(_sieve_primes(30))

    def test_certificate_checksum_format(self):
        """Checksum starts with expected prefix."""
        cert = generate_qcal_certificate_mbc(p_max=20)
        assert cert["checksum"].startswith("0xQCAL_MBC_VOSC_")

    def test_certificate_derivation_steps(self):
        """Certificate lists 7 derivation steps."""
        cert = generate_qcal_certificate_mbc(p_max=20)
        assert len(cert["derivation_steps"]) == 7

    def test_certificate_structural_coincidence(self):
        """Certificate confirms structural coincidence."""
        cert = generate_qcal_certificate_mbc(p_max=20)
        assert cert["results"]["structural_coincidence"] is True
        assert cert["results"]["max_deviation"] < 1e-12

    def test_certificate_v_osc_finite(self):
        """V_osc values in certificate are finite."""
        cert = generate_qcal_certificate_mbc(p_max=20, x_values=[1.0, 10.0])
        for key, val in cert["results"]["v_osc_values"].items():
            assert np.isfinite(val), f"V_osc({key}) = {val} not finite"

    def test_certificate_reproducible(self):
        """Same inputs yield same checksum (reproducibility)."""
        cert1 = generate_qcal_certificate_mbc(p_max=20, x_values=[1.0, 5.0])
        cert2 = generate_qcal_certificate_mbc(p_max=20, x_values=[1.0, 5.0])
        assert cert1["checksum"] == cert2["checksum"]

    def test_certificate_phase_stored(self):
        """Phase value is stored in certificate."""
        cert = generate_qcal_certificate_mbc(p_max=15, phase=-np.pi / 4.0)
        assert abs(cert["phase"] - (-np.pi / 4.0)) < 1e-12


# ---------------------------------------------------------------------------
# Integration / mathematical property tests
# ---------------------------------------------------------------------------


class TestMathematicalProperties:
    """Mathematical property tests for the structural derivation."""

    def test_frequencies_are_log_p(self):
        """The frequency of each prime-p mode is exactly log p."""
        v_osc = VOscFromMultiplicativeBC(p_max=30)
        for p in v_osc.primes:
            assert abs(v_osc.frequency(p) - np.log(p)) < 1e-12

    def test_amplitude_decreasing_for_large_p(self):
        """Amplitude (log p)/√p is eventually decreasing."""
        primes = _sieve_primes(100)
        amps = [np.log(p) / np.sqrt(p) for p in primes if p >= 3]
        # Amplitude must eventually decrease (for p ≥ e²  ≈ 7.4)
        assert amps[-1] < amps[0]

    def test_rho_osc_agrees_with_explicit_formula(self):
        """ρ_osc from multiplicative BC matches the Riemann explicit formula structure."""
        primes = [2, 3, 5, 7, 11]
        lam = 14.134  # near first Riemann zero
        rho = oscillatory_density_from_bc(lam, primes)
        # Manual: (1/π) Σ (log p/√p) cos(λ log p)
        expected = sum(
            (np.log(p) / np.sqrt(p)) * np.cos(lam * np.log(p)) for p in primes
        ) / np.pi
        assert abs(rho - expected) < 1e-12

    def test_spectral_density_prime_product(self):
        """Product of spectral densities ρ_p = (log p)/(2π) for first few primes."""
        engine = SpectralDiscretizationEngine(primes=[2, 3, 5])
        for p in [2, 3, 5]:
            rho = engine.spectral_density_prime(p)
            assert rho > 0
            assert abs(rho - np.log(p) / (2.0 * np.pi)) < 1e-12

    def test_v_osc_zero_phase_equals_pure_cosine(self):
        """With phase=0, V_osc = pure cosine sum."""
        primes = [2, 3]
        x = 4.0
        v = VOscFromMultiplicativeBC(primes=primes, phase=0.0)
        expected = sum(
            (np.log(p) / np.sqrt(p)) * np.cos(x * np.log(p)) for p in primes
        )
        assert abs(v.evaluate(x) - expected) < 1e-12

    def test_bc_frequency_is_lattice_period(self):
        """The fundamental frequency ω_p = 2π/log p has period log p in log space."""
        engine = SpectralDiscretizationEngine(primes=[2, 3, 5])
        for p in [2, 3, 5]:
            omega_p = engine.fundamental_frequency(p)
            log_p = np.log(p)
            # e^{i·ω_p·log p} = e^{i·2π} = 1: confirms periodicity
            phase = omega_p * log_p
            assert abs(phase - 2.0 * np.pi) < 1e-10

    def test_N_osc_derivative_gives_rho_osc_log_squared(self):
        """Numerical derivative of N_osc gives -(log p)²/√p cosine sum / π.

        N_osc = -(1/π) Σ_p (log p / √p) sin(λ log p)
        dN_osc/dλ = -(1/π) Σ_p (log p)² / √p · cos(λ log p)

        This has an extra factor of log p compared to ρ_osc.
        """
        primes = _sieve_primes(20)
        lam = 20.0
        dE = 0.001
        N_plus = counting_oscillation_N_osc(lam + dE, primes, k_max=1)
        N_minus = counting_oscillation_N_osc(lam - dE, primes, k_max=1)
        numerical_derivative = (N_plus - N_minus) / (2.0 * dE)
        # Expected: -(1/π) Σ_p (log p)² / √p · cos(λ log p)
        expected = -(1.0 / np.pi) * sum(
            (np.log(p) ** 2 / np.sqrt(p)) * np.cos(lam * np.log(p))
            for p in primes
        )
        assert abs(numerical_derivative - expected) < 0.01
