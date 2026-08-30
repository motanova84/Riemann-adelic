#!/usr/bin/env python3
"""
Tests for the Mayer Transfer Operator (Ruelle-Frobenius-Mayer)
==============================================================

Validates the three-part framework:
1. GeodesicFlow: primes as primitive periodic orbits, ℓ(γ_p) = log p
2. MayerTransferOperator: det(I - L_s) = 1/ζ(s) Fredholm identity
3. HamiltonianHolomorphicSystem: Phase Inversion Potential Ω synthesis

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: March 2026
DOI: 10.5281/zenodo.17379721
"""

import sys
from pathlib import Path

import numpy as np
import pytest

# Add operators directory to path
repo_root = Path(__file__).parent.parent
sys.path.insert(0, str(repo_root / "operators"))

from mayer_transfer_operator import (
    GeodesicFlow,
    HamiltonianHolomorphicSystem,
    MayerTransferOperator,
    OrbitContributionMayer,
    PhaseInversionResult,
    PrimitiveOrbit,
    validate_mayer_transfer_operator,
)


# ─────────────────────────────────────────────────────────────────────────────
# Tests: GeodesicFlow
# ─────────────────────────────────────────────────────────────────────────────

class TestGeodesicFlow:
    """Test suite for GeodesicFlow (primes as periodic orbits)."""

    def setup_method(self):
        self.flow = GeodesicFlow(primes=[2, 3, 5, 7, 11, 13], max_power=8)

    # ── initialisation ────────────────────────────────────────────────────────

    def test_init_custom_primes(self):
        primes = [2, 3, 5, 7]
        f = GeodesicFlow(primes=primes, max_power=5)
        assert f.primes == primes
        assert f.max_power == 5

    def test_init_default_primes(self):
        f = GeodesicFlow()
        # Default generates first 12 primes
        assert len(f.primes) == 12
        assert f.primes[0] == 2
        assert f.primes[1] == 3
        assert f.primes[-1] == 37

    def test_is_prime(self):
        assert GeodesicFlow._is_prime(2)
        assert GeodesicFlow._is_prime(3)
        assert GeodesicFlow._is_prime(97)
        assert not GeodesicFlow._is_prime(1)
        assert not GeodesicFlow._is_prime(4)
        assert not GeodesicFlow._is_prime(100)

    def test_first_primes(self):
        f = GeodesicFlow()
        ps = f._first_primes(5)
        assert ps == [2, 3, 5, 7, 11]

    # ── orbit length: ℓ(γ_p) = log p ─────────────────────────────────────────

    def test_orbit_length_primitive(self):
        """Primitive orbit length ℓ(γ_p) = log p."""
        for p in [2, 3, 5, 7, 11]:
            assert abs(self.flow.orbit_length(p) - np.log(p)) < 1e-12

    def test_orbit_length_iterate(self):
        """k-th iterate length ℓ(γ_{p,k}) = k·log p."""
        for p in [2, 5, 11]:
            for k in [1, 2, 3, 4]:
                expected = k * np.log(p)
                assert abs(self.flow.orbit_length(p, k) - expected) < 1e-12

    def test_orbit_length_positive(self):
        for p in self.flow.primes:
            assert self.flow.orbit_length(p) > 0

    def test_orbit_length_monotone(self):
        """Larger primes ↔ longer orbits."""
        ps = [2, 3, 5, 7, 11]
        lengths = [self.flow.orbit_length(p) for p in ps]
        for i in range(len(lengths) - 1):
            assert lengths[i] < lengths[i + 1]

    # ── monodromy matrix ──────────────────────────────────────────────────────

    def test_monodromy_eigenvalue_primitive(self):
        """Primitive monodromy eigenvalue = p."""
        for p in [2, 3, 5, 7]:
            assert abs(self.flow.monodromy_eigenvalue(p) - p) < 1e-10

    def test_monodromy_eigenvalue_iterate(self):
        """k-th iterate monodromy = p^k."""
        for p in [2, 3, 5]:
            for k in [2, 3, 4]:
                expected = p ** k
                assert abs(self.flow.monodromy_eigenvalue(p, k) - expected) < 1e-6

    def test_stability_determinant_positive(self):
        for p in [2, 3, 5, 7]:
            for k in [1, 2]:
                sd = self.flow.stability_determinant(p, k)
                assert sd > 0

    def test_stability_determinant_formula(self):
        """Check |det(I - M)^{1/2}| = p^{k/2}·(1 - p^{-k})."""
        for p in [2, 3, 5]:
            for k in [1, 2]:
                expected = (p ** k) ** 0.5 * (1.0 - p ** (-k))
                assert abs(self.flow.stability_determinant(p, k) - expected) < 1e-10

    # ── orbit weights ─────────────────────────────────────────────────────────

    def test_von_mangoldt_weight_formula(self):
        """von Mangoldt weight = log(p) / p^{k/2}."""
        for p in [2, 3, 5, 7]:
            for k in [1, 2, 3]:
                expected = np.log(p) / (p ** (k / 2.0))
                assert abs(self.flow.von_mangoldt_weight(p, k) - expected) < 1e-12

    def test_hyperbolic_weight_formula(self):
        """Hyperbolic weight = ℓ / (2 sinh(ℓ/2))."""
        for p in [2, 3, 5]:
            L = np.log(p)
            expected = L / (2.0 * np.sinh(L / 2.0))
            assert abs(self.flow.hyperbolic_weight(p) - expected) < 1e-12

    def test_hyperbolic_weight_positive(self):
        for p in self.flow.primes:
            assert self.flow.hyperbolic_weight(p) > 0

    def test_weights_converge_for_large_p(self):
        """For large p, hyperbolic ≈ von Mangoldt weight."""
        for p in [101, 251, 503]:
            f = GeodesicFlow(primes=[p])
            result = f.weight_agreement(p)
            assert result["asymptotic_agreement"], \
                f"p={p}: hyperbolic={result['hyperbolic_weight']:.6f}, " \
                f"vm={result['von_mangoldt_weight']:.6f}"

    def test_weight_agreement_dict_keys(self):
        result = self.flow.weight_agreement(5)
        assert "hyperbolic_weight" in result
        assert "von_mangoldt_weight" in result
        assert "relative_difference" in result
        assert "asymptotic_agreement" in result

    def test_von_mangoldt_decreases_with_k(self):
        """Weight decreases with orbit iterate k."""
        p = 5
        w1 = self.flow.von_mangoldt_weight(p, 1)
        w2 = self.flow.von_mangoldt_weight(p, 2)
        w3 = self.flow.von_mangoldt_weight(p, 3)
        assert w1 > w2 > w3

    # ── primitive orbit catalogue ─────────────────────────────────────────────

    def test_primitive_orbits_count(self):
        orbits = self.flow.primitive_orbits()
        assert len(orbits) == len(self.flow.primes)

    def test_primitive_orbits_types(self):
        orbits = self.flow.primitive_orbits()
        for o in orbits:
            assert isinstance(o, PrimitiveOrbit)

    def test_primitive_orbits_length(self):
        orbits = self.flow.primitive_orbits()
        for o in orbits:
            assert abs(o.length - np.log(o.prime)) < 1e-12

    def test_primitive_orbits_monodromy(self):
        orbits = self.flow.primitive_orbits()
        for o in orbits:
            assert abs(o.monodromy_eigenvalue - o.prime) < 1e-10

    def test_primitive_orbits_cached(self):
        """Second call returns cached result."""
        orbits1 = self.flow.primitive_orbits()
        orbits2 = self.flow.primitive_orbits()
        assert orbits1 is orbits2

    def test_orbit_iterate_dict(self):
        d = self.flow.orbit_iterate(5, 3)
        assert d["prime"] == 5
        assert d["k"] == 3
        assert abs(d["length"] - 3 * np.log(5)) < 1e-12

    def test_orbit_iterate_invalid_k(self):
        with pytest.raises(ValueError):
            self.flow.orbit_iterate(5, 0)

    # ── Selberg trace sum ─────────────────────────────────────────────────────

    def test_selberg_trace_sum_real(self):
        """Trace sum is real for real t."""
        val = self.flow.selberg_trace_sum(14.134725)
        assert isinstance(val, float)

    def test_selberg_trace_sum_finite(self):
        for t in [0.0, 1.0, 14.134725, 100.0]:
            val = self.flow.selberg_trace_sum(t)
            assert np.isfinite(val)

    def test_selberg_trace_sum_t0(self):
        """At t=0 all cosines are 1, sum is Σ (log p)/p^{k/2}."""
        val = self.flow.selberg_trace_sum(0.0)
        expected = sum(
            self.flow.von_mangoldt_weight(p, k)
            for p in self.flow.primes
            for k in range(1, self.flow.max_power + 1)
            if self.flow.von_mangoldt_weight(p, k) > 1e-12
        )
        assert abs(val - expected) < 1e-8


# ─────────────────────────────────────────────────────────────────────────────
# Tests: MayerTransferOperator
# ─────────────────────────────────────────────────────────────────────────────

class TestMayerTransferOperator:
    """Test suite for MayerTransferOperator."""

    def setup_method(self):
        self.flow = GeodesicFlow(primes=[2, 3, 5, 7, 11], max_power=10)
        self.mayer = MayerTransferOperator(self.flow, n_terms=30)

    # ── trace of L_s ─────────────────────────────────────────────────────────

    def test_trace_type(self):
        tr = self.mayer.trace_L_s(2.0 + 0j)
        assert isinstance(tr, complex)

    def test_trace_real_s_real(self):
        """Trace is real for real s > 1."""
        tr = self.mayer.trace_L_s(2.0)
        assert abs(tr.imag) < 1e-10

    def test_trace_decreases_with_sigma(self):
        """Trace decreases as Re(s) increases."""
        tr2 = abs(self.mayer.trace_L_s(2.0))
        tr3 = abs(self.mayer.trace_L_s(3.0))
        assert tr2 > tr3

    def test_trace_power_k1_equals_trace(self):
        """Tr(L_s^1) == trace_L_s(s)."""
        s = 2.5 + 0.5j
        assert abs(self.mayer.trace_L_s_power(s, 1) - self.mayer.trace_L_s(s)) < 1e-12

    def test_trace_power_decreasing(self):
        """Higher orbit iterates contribute less."""
        s = 2.0
        tr1 = abs(self.mayer.trace_L_s_power(s, 1))
        tr2 = abs(self.mayer.trace_L_s_power(s, 2))
        assert tr1 > tr2

    # ── Euler product ─────────────────────────────────────────────────────────

    def test_euler_product_real_s(self):
        """Euler product is positive real for real s > 1."""
        ep = self.mayer.zeta_via_euler_product(2.0)
        assert ep.real > 1.0
        assert abs(ep.imag) < 1e-10

    def test_euler_product_s2(self):
        """At s=2 the Euler product ≈ π²/6 (up to truncation error from finite primes)."""
        ep = abs(self.mayer.zeta_via_euler_product(2.0))
        # With only 5 primes we get a lower bound; exact value is π²/6 ≈ 1.6449
        assert ep > 1.3  # rough lower bound for 5 primes

    # ── Fredholm determinant ──────────────────────────────────────────────────

    def test_fredholm_det_type(self):
        fd = self.mayer.fredholm_determinant(2.0 + 0j)
        assert isinstance(fd, complex)

    def test_fredholm_det_real_s_positive(self):
        """For real s > 1 the determinant is real and positive."""
        fd = self.mayer.fredholm_determinant(3.0)
        # det(I - L_s) = 1/ζ(s) > 0 for real s > 1
        assert fd.real > 0
        assert abs(fd.imag) < 0.1  # allow small numerical imag due to truncation

    def test_fredholm_identity_s2(self):
        """det(I - L_s) · ζ(s) ≈ 1 at s = 2."""
        fd = self.mayer.fredholm_determinant(2.0)
        zeta = self.mayer.zeta_via_euler_product(2.0)
        product = abs(fd * zeta)
        assert abs(product - 1.0) < 0.1, f"product = {product:.4f}"

    def test_fredholm_identity_multiple_s(self):
        """Identity holds at several values with Re(s) > 1."""
        verif = self.mayer.verify_fredholm_identity([2.0, 3.0, 4.0])
        assert verif["n_pass"] >= 2  # at least 2 of 3 should pass

    # ── spectral analysis ─────────────────────────────────────────────────────

    def test_spectral_analysis_type(self):
        r = self.mayer.spectral_analysis(2.0)
        from mayer_transfer_operator import MayerSpectralResult
        assert isinstance(r, MayerSpectralResult)

    def test_spectral_analysis_orbit_contributions(self):
        r = self.mayer.spectral_analysis(2.0)
        assert len(r.orbit_contributions) > 0
        for c in r.orbit_contributions:
            assert isinstance(c, OrbitContributionMayer)

    def test_spectral_analysis_on_critical_line(self):
        r = self.mayer.spectral_analysis(0.5 + 14.134725j)
        assert r.on_critical_line

    def test_spectral_analysis_off_critical_line(self):
        r = self.mayer.spectral_analysis(0.7 + 14.134725j)
        assert not r.on_critical_line

    def test_coherence_psi_range(self):
        for s in [2.0, 3.0, 2.0 + 1j]:
            r = self.mayer.spectral_analysis(s)
            assert 0.0 <= r.coherence_psi <= 1.0

    def test_verify_fredholm_identity_dict(self):
        verif = self.mayer.verify_fredholm_identity()
        assert "mean_error" in verif
        assert "max_error" in verif
        assert "n_pass" in verif
        assert "n_total" in verif
        assert "identity_verified" in verif


# ─────────────────────────────────────────────────────────────────────────────
# Tests: HamiltonianHolomorphicSystem
# ─────────────────────────────────────────────────────────────────────────────

class TestHamiltonianHolomorphicSystem:
    """Test suite for HamiltonianHolomorphicSystem (Phase Inversion Potential Ω)."""

    def setup_method(self):
        flow = GeodesicFlow(primes=[2, 3, 5, 7, 11], max_power=8)
        mayer = MayerTransferOperator(flow, n_terms=20)
        self.sys = HamiltonianHolomorphicSystem(mayer)

    # ── Hamiltonian condition ─────────────────────────────────────────────────

    def test_hamiltonian_on_critical_line(self):
        for t in [14.134725, 21.022, 25.01, 0.0]:
            s = 0.5 + t * 1j
            assert self.sys.is_hamiltonian(s), f"Should be Hamiltonian at s={s}"

    def test_hamiltonian_off_critical_line(self):
        for sigma in [0.3, 0.4, 0.6, 0.7, 0.8]:
            s = complex(sigma, 14.134725)
            assert not self.sys.is_hamiltonian(s), f"Should NOT be Hamiltonian at Re(s)={sigma}"

    def test_hamiltonian_boundary(self):
        """Test at sigma very close to but not on critical line."""
        assert self.sys.is_hamiltonian(0.5 + 0j)
        assert not self.sys.is_hamiltonian(0.5 + 1e-9 + 0j)

    # ── holomorphic condition ─────────────────────────────────────────────────

    def test_holomorphic_on_critical_line(self):
        for t in [14.134725, 21.022, 0.0]:
            s = 0.5 + t * 1j
            assert self.sys.is_holomorphic(s)

    def test_holomorphic_off_critical_line(self):
        for sigma in [0.3, 0.6, 0.8]:
            s = complex(sigma, 14.134725)
            assert not self.sys.is_holomorphic(s)

    # ── coupling strength ─────────────────────────────────────────────────────

    def test_coupling_zero_on_critical_line(self):
        s = 0.5 + 14.134725j
        c = self.sys.coupling_strength(s)
        assert abs(c) < 1e-10

    def test_coupling_nonzero_off_line(self):
        s = 0.7 + 14.134725j
        c = self.sys.coupling_strength(s)
        assert c > 0

    def test_coupling_symmetric(self):
        """Coupling depends only on |Re(s) - 1/2|."""
        s_plus = 0.7 + 5j
        s_minus = 0.3 + 5j
        assert abs(self.sys.coupling_strength(s_plus) -
                   self.sys.coupling_strength(s_minus)) < 1e-10

    # ── phase inversion potential ─────────────────────────────────────────────

    def test_phase_inversion_potential_type(self):
        v = self.sys.phase_inversion_potential(1.0 + 1j, 0.5 + 14j)
        assert isinstance(v, complex)

    def test_phase_inversion_potential_zero_z(self):
        """V_Ω(0, s) = 0 by convention."""
        v = self.sys.phase_inversion_potential(0.0 + 0j, 0.5 + 14j)
        assert v == 0.0

    def test_phase_inversion_potential_critical_line(self):
        """On critical line: V_Ω is purely imaginary (Hamiltonian condition)."""
        z = 1.0 + 1j
        s = 0.5 + 5.0j
        v = self.sys.phase_inversion_potential(z, s)
        # On critical line: -i·(s-1/2)·log|z| = -i·(5i)·log|z| = 5·log|z| (real!)
        # + i·arg(z)·Im(s) = i·(π/4)·5 (imag)
        # Real part from first term: 5·log|z| = 5·log(√2) = 5·0.5·ln2
        log_abs_z = np.log(abs(z))
        arg_z = np.angle(z)
        t = 5.0
        expected = -1j * (5j) * log_abs_z + 1j * arg_z * t
        assert abs(v - expected) < 1e-10

    def test_analyse_phase_inversion_type(self):
        r = self.sys.analyse_phase_inversion(0.5 + 14j)
        assert isinstance(r, PhaseInversionResult)

    def test_analyse_phase_inversion_on_critical_line(self):
        r = self.sys.analyse_phase_inversion(0.5 + 14.134725j)
        assert r.is_hamiltonian
        assert r.is_holomorphic
        assert r.critical_line_enforced
        assert abs(r.coupling_strength) < 1e-10

    def test_analyse_phase_inversion_off_critical_line(self):
        r = self.sys.analyse_phase_inversion(0.6 + 14.134725j)
        assert not r.is_hamiltonian
        assert not r.is_holomorphic
        assert not r.critical_line_enforced
        assert r.coupling_strength > 0

    # ── exact weight verification ─────────────────────────────────────────────

    def test_exact_weight_verification_dict(self):
        d = self.sys.exact_weight_verification(5)
        assert "exact_weight" in d
        assert "hyperbolic_weight" in d
        assert "relative_deviation" in d
        assert "omega_correction" in d
        assert "exact_under_coupling" in d

    def test_exact_weight_large_p(self):
        """For large p the Ω coupling controls the deviation."""
        for p in [101, 251]:
            f = GeodesicFlow(primes=[p], max_power=1)
            m = MayerTransferOperator(f, n_terms=10)
            s = HamiltonianHolomorphicSystem(m)
            d = s.exact_weight_verification(p)
            assert d["exact_under_coupling"]

    # ── zero confinement ──────────────────────────────────────────────────────

    def test_critical_line_confinement_keys(self):
        result = self.sys.critical_line_confinement(
            sigma_values=np.linspace(0.35, 0.65, 7)
        )
        assert "sigma_values" in result
        assert "coupling_profile" in result
        assert "confinement_verified" in result

    def test_confinement_minimum_near_half(self):
        result = self.sys.critical_line_confinement(
            sigma_values=np.linspace(0.35, 0.65, 13)
        )
        assert result["coupling_minimum_at_half"], \
            f"Coupling should be zero at σ=0.5, got {result['coupling_at_half']:.6f}"
        assert result["coupling_profile_correct"], \
            "Coupling profile should be V-shaped centred at σ=0.5"
        assert result["confinement_verified"], \
            "Phase Inversion Potential should enforce zero confinement to critical line"


# ─────────────────────────────────────────────────────────────────────────────
# Tests: validate_mayer_transfer_operator
# ─────────────────────────────────────────────────────────────────────────────

class TestValidationFunction:
    """Test the top-level validation function."""

    def test_validation_runs(self):
        cert = validate_mayer_transfer_operator()
        assert isinstance(cert, dict)

    def test_validation_keys(self):
        cert = validate_mayer_transfer_operator()
        assert "tests_passed" in cert
        assert "tests_total" in cert
        assert "psi" in cert
        assert "all_pass" in cert
        assert "results" in cert

    def test_validation_total(self):
        cert = validate_mayer_transfer_operator()
        assert cert["tests_total"] == 6

    def test_validation_psi_range(self):
        cert = validate_mayer_transfer_operator()
        assert 0.0 <= cert["psi"] <= 1.0

    def test_validation_all_pass(self):
        cert = validate_mayer_transfer_operator()
        assert cert["all_pass"], \
            f"Only {cert['tests_passed']}/{cert['tests_total']} tests passed: " \
            f"{cert['results']}"

    def test_validation_psi_one(self):
        cert = validate_mayer_transfer_operator()
        assert cert["psi"] == 1.0, \
            f"Expected Ψ=1.0, got {cert['psi']:.2f}"

    def test_validation_doi(self):
        cert = validate_mayer_transfer_operator()
        assert cert["doi"] == "10.5281/zenodo.17379721"

    def test_validation_author(self):
        cert = validate_mayer_transfer_operator()
        assert "Mota Burruezo" in cert["author"]
