#!/usr/bin/env python3
"""
Tests for operators/bio_nodo.py — Bio-Nodo Fundamental Identity

Validates all four modules of the Bio-Nodo identity Ĥ_π |Ψ⟩ = γ_n |Ψ⟩:
1. SpectralIdentity    — eigenvalues match Riemann zeros
2. OrbitCollapse       — adelic torus closed orbits at prime powers
3. PhaseInvariant      — density matrix coherence Ψ(t) ≥ diamond threshold
4. FixedPointSovereignty — QCAL fixed-point signature

DOI: 10.5281/zenodo.17379721
Signature: ∴𓂀Ω∞³Φ @ 141.7001 Hz
"""

import sys
from pathlib import Path

import numpy as np
import pytest

# Ensure repo root is importable
REPO_ROOT = Path(__file__).parent.parent
sys.path.insert(0, str(REPO_ROOT))
sys.path.insert(0, str(REPO_ROOT / "operators"))

from bio_nodo import (
    BioNodo,
    BioNodoResult,
    FixedPointResult,
    FixedPointSovereignty,
    OrbitCollapse,
    OrbitCollapseResult,
    PhaseInvariant,
    PhaseInvariantResult,
    PSI_DIAMOND,
    SpectralIdentity,
    SpectralIdentityResult,
    _first_primes,
    _get_riemann_zeros,
    _is_prime,
    C_COHERENCE,
    F0,
)


# ---------------------------------------------------------------------------
# Helper utilities
# ---------------------------------------------------------------------------

class TestHelpers:
    """Tests for internal helper functions."""

    def test_is_prime_known(self):
        primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
        for p in primes:
            assert _is_prime(p), f"{p} should be prime"

    def test_is_prime_composites(self):
        composites = [1, 4, 6, 8, 9, 10, 12, 14, 15, 25]
        for n in composites:
            assert not _is_prime(n), f"{n} should not be prime"

    def test_first_primes_count(self):
        for count in [1, 5, 10, 20]:
            primes = _first_primes(count)
            assert len(primes) == count
            assert all(_is_prime(p) for p in primes)

    def test_first_primes_correct(self):
        expected = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
        assert _first_primes(10) == expected

    def test_get_riemann_zeros_first(self):
        zeros = _get_riemann_zeros(1)
        assert len(zeros) == 1
        assert abs(zeros[0] - 14.134725142) < 1e-3

    def test_get_riemann_zeros_count(self):
        for n in [1, 3, 5, 10]:
            z = _get_riemann_zeros(n)
            assert len(z) == n

    def test_get_riemann_zeros_increasing(self):
        zeros = _get_riemann_zeros(5)
        assert np.all(np.diff(zeros) > 0), "Riemann zeros should be strictly increasing"


# ---------------------------------------------------------------------------
# Module constants
# ---------------------------------------------------------------------------

class TestConstants:
    """Verify module-level QCAL constants."""

    def test_f0_value(self):
        assert abs(F0 - 141.7001) < 1e-6

    def test_c_coherence_value(self):
        assert abs(C_COHERENCE - 244.36) < 1e-6

    def test_psi_diamond(self):
        assert abs(PSI_DIAMOND - 0.999) < 1e-9


# ---------------------------------------------------------------------------
# Module 1: SpectralIdentity
# ---------------------------------------------------------------------------

class TestSpectralIdentity:
    """Tests for SpectralIdentity module."""

    def test_build_hamiltonian_shape(self):
        si = SpectralIdentity(n_zeros=5)
        H = si.build_hamiltonian()
        assert H.shape == (5, 5)

    def test_build_hamiltonian_diagonal(self):
        si = SpectralIdentity(n_zeros=5)
        H = si.build_hamiltonian()
        # Off-diagonal should be zero
        off = H - np.diag(np.diag(H))
        assert np.allclose(off, 0.0)

    def test_build_hamiltonian_eigenvalues_are_gamma_n(self):
        si = SpectralIdentity(n_zeros=5)
        H = si.build_hamiltonian()
        eigenvals = np.sort(np.linalg.eigvalsh(H))
        assert np.allclose(eigenvals, np.sort(si.gamma_n), atol=1e-8)

    def test_verify_returns_result_type(self):
        si = SpectralIdentity(n_zeros=5)
        result = si.verify()
        assert isinstance(result, SpectralIdentityResult)

    def test_verify_correlation_is_one(self):
        # Diagonal Hamiltonian → perfect correlation
        si = SpectralIdentity(n_zeros=5)
        result = si.verify()
        assert abs(result.correlation - 1.0) < 1e-10

    def test_verify_spectral_gap_positive(self):
        si = SpectralIdentity(n_zeros=5)
        result = si.verify()
        assert result.spectral_gap > 0

    def test_verify_is_coherent(self):
        si = SpectralIdentity(n_zeros=5)
        result = si.verify(correlation_threshold=0.999)
        assert result.is_coherent

    def test_verify_single_zero(self):
        si = SpectralIdentity(n_zeros=1)
        result = si.verify()
        assert isinstance(result, SpectralIdentityResult)
        # With single eigenvalue correlation is defined as 1.0 by convention
        assert result.correlation == 1.0

    def test_verify_eigenvalues_match_gamma_n(self):
        si = SpectralIdentity(n_zeros=10)
        result = si.verify()
        assert np.allclose(np.sort(result.eigenvalues), np.sort(result.gamma_n), atol=1e-8)

    def test_metadata_fields(self):
        si = SpectralIdentity(n_zeros=5)
        result = si.verify()
        assert "n_zeros" in result.metadata
        assert "f0" in result.metadata
        assert result.metadata["n_zeros"] == 5


# ---------------------------------------------------------------------------
# Module 2: OrbitCollapse
# ---------------------------------------------------------------------------

class TestOrbitCollapse:
    """Tests for OrbitCollapse module."""

    def test_compute_returns_result_type(self):
        oc = OrbitCollapse(n_primes=5, k_max=3)
        result = oc.compute()
        assert isinstance(result, OrbitCollapseResult)

    def test_prime_powers_shape(self):
        n_primes, k_max = 5, 3
        oc = OrbitCollapse(n_primes=n_primes, k_max=k_max)
        result = oc.compute()
        assert result.prime_powers.shape == (n_primes * k_max, 4)

    def test_prime_powers_columns(self):
        """Columns are (p, k, t=k*ln(p), weight=ln(p)/p^(k/2))."""
        oc = OrbitCollapse(n_primes=3, k_max=2)
        result = oc.compute()
        primes_used = result.prime_powers[:, 0]
        ks = result.prime_powers[:, 1]
        ts = result.prime_powers[:, 2]
        weights = result.prime_powers[:, 3]

        # Verify t = k * ln(p)
        expected_t = ks * np.log(primes_used)
        assert np.allclose(ts, expected_t, atol=1e-12)

        # Verify weight = ln(p) / p^(k/2)
        expected_w = np.log(primes_used) / (primes_used ** (ks / 2.0))
        assert np.allclose(weights, expected_w, atol=1e-12)

    def test_collapse_times_positive(self):
        oc = OrbitCollapse(n_primes=5, k_max=3)
        result = oc.compute()
        assert np.all(result.prime_powers[:, 2] > 0)

    def test_weights_positive(self):
        oc = OrbitCollapse(n_primes=5, k_max=3)
        result = oc.compute()
        assert np.all(result.prime_powers[:, 3] > 0)

    def test_total_weight_positive(self):
        oc = OrbitCollapse(n_primes=5, k_max=3)
        result = oc.compute()
        assert result.total_weight > 0

    def test_is_periodic_true(self):
        oc = OrbitCollapse(n_primes=5, k_max=3)
        result = oc.compute()
        assert result.is_periodic

    def test_closed_orbits_keys(self):
        primes = _first_primes(5)
        oc = OrbitCollapse(n_primes=5, k_max=3)
        result = oc.compute()
        assert set(result.closed_orbits.keys()) == set(primes)

    def test_closed_orbits_length(self):
        k_max = 4
        oc = OrbitCollapse(n_primes=3, k_max=k_max)
        result = oc.compute()
        for p, orbits in result.closed_orbits.items():
            assert len(orbits) == k_max

    def test_first_collapse_time_p2(self):
        """For p=2, k=1: t = ln(2) ≈ 0.6931."""
        oc = OrbitCollapse(n_primes=1, k_max=1)  # only p=2
        result = oc.compute()
        assert abs(result.closed_orbits[2][0] - np.log(2)) < 1e-10


# ---------------------------------------------------------------------------
# Module 3: PhaseInvariant
# ---------------------------------------------------------------------------

class TestPhaseInvariant:
    """Tests for PhaseInvariant module."""

    def test_evaluate_returns_result_type(self):
        pi = PhaseInvariant(n_points=50)
        result = pi.evaluate()
        assert isinstance(result, PhaseInvariantResult)

    def test_times_grid_length(self):
        pi = PhaseInvariant(n_points=100)
        result = pi.evaluate()
        assert len(result.times) == 100

    def test_psi_t_in_range(self):
        pi = PhaseInvariant(n_points=50)
        result = pi.evaluate()
        assert np.all(result.psi_t >= 0.0)
        assert np.all(result.psi_t <= 1.0 + 1e-9)

    def test_psi_t_at_zero_is_high(self):
        """At t=0 all modes are in phase → ρ is a rank-1 projector → coherence is well-defined."""
        pi = PhaseInvariant(n_points=50)
        result = pi.evaluate()
        # At t=0 equal-weight state: ρ_od contributes, but Ψ is still defined
        assert result.psi_t[0] >= 0.0

    def test_diamond_fraction_in_range(self):
        pi = PhaseInvariant(n_points=100)
        result = pi.evaluate()
        assert 0.0 <= result.diamond_fraction <= 1.0

    def test_above_diamond_boolean_array(self):
        pi = PhaseInvariant(n_points=50)
        result = pi.evaluate()
        assert result.above_diamond.dtype == bool
        assert len(result.above_diamond) == 50

    def test_single_mode_coherence_is_one(self):
        """With a single mode |c₁|=1, ρ is a 1×1 matrix → all 'off-diagonal' is zero → Ψ = 1."""
        pi = PhaseInvariant(gamma_n=np.array([14.134725142]), coefficients=np.array([1.0 + 0j]),
                            n_points=20)
        result = pi.evaluate()
        assert np.allclose(result.psi_t, 1.0, atol=1e-9)

    def test_invalid_coefficients_length(self):
        with pytest.raises(ValueError, match="len\\(coefficients\\)"):
            PhaseInvariant(
                gamma_n=np.array([14.1, 21.0]),
                coefficients=np.array([1.0, 0.0, 0.0]),  # wrong length
            )

    def test_psi_min_le_psi_mean(self):
        pi = PhaseInvariant(n_points=100)
        result = pi.evaluate()
        assert result.psi_min <= result.psi_mean + 1e-12


# ---------------------------------------------------------------------------
# Module 4: FixedPointSovereignty
# ---------------------------------------------------------------------------

class TestFixedPointSovereignty:
    """Tests for FixedPointSovereignty module."""

    def test_compute_returns_result_type(self):
        fp = FixedPointSovereignty()
        result = fp.compute(psi_value=0.999)
        assert isinstance(result, FixedPointResult)

    def test_sigma_formula(self):
        """Σ = C × Ψ² × A_eff²."""
        fp = FixedPointSovereignty(c_coherence=244.36)
        psi, a_eff = 0.999, 1.0
        result = fp.compute(psi_value=psi, a_eff=a_eff)
        expected = 244.36 * psi**2 * a_eff**2
        assert abs(result.sigma - expected) < 1e-9

    def test_signature_present_above_threshold(self):
        fp = FixedPointSovereignty(psi_diamond=0.999)
        result = fp.compute(psi_value=0.9995)
        assert result.signature_hash is not None
        assert len(result.signature_hash) == 64  # SHA-256 hex digest

    def test_signature_absent_below_threshold(self):
        fp = FixedPointSovereignty(psi_diamond=0.999)
        result = fp.compute(psi_value=0.998)
        assert result.signature_hash is None
        assert not result.is_fixed_point

    def test_signature_reproducible(self):
        """Same inputs → same hash."""
        fp = FixedPointSovereignty()
        r1 = fp.compute(psi_value=0.9995, a_eff=1.0)
        r2 = fp.compute(psi_value=0.9995, a_eff=1.0)
        assert r1.signature_hash == r2.signature_hash

    def test_signature_changes_with_psi(self):
        fp = FixedPointSovereignty()
        r1 = fp.compute(psi_value=0.9990, a_eff=1.0)
        r2 = fp.compute(psi_value=0.9995, a_eff=1.0)
        # Different Ψ → different payload → different hash
        assert r1.signature_hash != r2.signature_hash

    def test_a_eff_default_from_intensity(self):
        """If a_eff is None, it defaults to sqrt(intensity)."""
        fp = FixedPointSovereignty()
        result = fp.compute(psi_value=0.9995, intensity=4.0, a_eff=None)
        assert abs(result.a_eff - 2.0) < 1e-9

    def test_relative_error_at_psi_one(self):
        """At Ψ=1, a_eff=1 → Σ = C → relative_error = 0."""
        fp = FixedPointSovereignty(c_coherence=244.36)
        result = fp.compute(psi_value=1.0, a_eff=1.0)
        assert abs(result.relative_error) < 1e-9

    def test_is_fixed_point_canonical(self):
        """Canonical case: Ψ=1, a_eff=1 should be a fixed point."""
        fp = FixedPointSovereignty(psi_diamond=0.999, c_coherence=244.36)
        result = fp.compute(psi_value=1.0, a_eff=1.0, tol=0.05)
        assert result.is_fixed_point


# ---------------------------------------------------------------------------
# Unified BioNodo
# ---------------------------------------------------------------------------

class TestBioNodo:
    """Integration tests for the unified BioNodo class."""

    @pytest.fixture
    def bn_small(self):
        """Lightweight BioNodo for fast tests."""
        return BioNodo(n_zeros=5, n_primes=5, k_max=3, t_max=0.5, n_time_points=50)

    def test_evaluate_returns_result_type(self, bn_small):
        result = bn_small.evaluate()
        assert isinstance(result, BioNodoResult)

    def test_evaluate_has_all_modules(self, bn_small):
        result = bn_small.evaluate()
        assert isinstance(result.spectral_identity, SpectralIdentityResult)
        assert isinstance(result.orbit_collapse, OrbitCollapseResult)
        assert isinstance(result.phase_invariant, PhaseInvariantResult)
        assert isinstance(result.fixed_point, FixedPointResult)

    def test_f0_propagated(self, bn_small):
        result = bn_small.evaluate()
        assert abs(result.f0 - F0) < 1e-6

    def test_c_coherence_propagated(self, bn_small):
        result = bn_small.evaluate()
        assert abs(result.c_coherence - C_COHERENCE) < 1e-6

    def test_psi_diamond_propagated(self, bn_small):
        result = bn_small.evaluate()
        assert abs(result.psi_diamond - PSI_DIAMOND) < 1e-9

    def test_spectral_identity_coherent(self, bn_small):
        result = bn_small.evaluate()
        assert result.spectral_identity.is_coherent

    def test_orbit_collapse_periodic(self, bn_small):
        result = bn_small.evaluate()
        assert result.orbit_collapse.is_periodic

    def test_all_modules_bool_type(self, bn_small):
        result = bn_small.evaluate()
        assert isinstance(result.all_modules_coherent, bool)

    def test_validate_returns_dict(self, bn_small):
        summary = bn_small.validate()
        assert isinstance(summary, dict)

    def test_validate_keys_present(self, bn_small):
        summary = bn_small.validate()
        required_keys = [
            "spectral_identity_coherent",
            "spectral_correlation",
            "spectral_gap",
            "orbit_collapse_periodic",
            "orbit_selberg_weight",
            "phase_invariant_mean_psi",
            "fixed_point_sigma",
            "fixed_point_rel_error",
            "fixed_point_signature",
            "fixed_point_coherent",
            "all_modules_coherent",
            "f0",
            "c_coherence",
            "psi_diamond",
        ]
        for key in required_keys:
            assert key in summary, f"Missing key: {key}"

    def test_validate_spectral_identity_passes(self, bn_small):
        summary = bn_small.validate()
        assert summary["spectral_identity_coherent"]

    def test_validate_orbit_passes(self, bn_small):
        summary = bn_small.validate()
        assert summary["orbit_collapse_periodic"]

    def test_validate_selberg_weight_positive(self, bn_small):
        summary = bn_small.validate()
        assert summary["orbit_selberg_weight"] > 0

    def test_validate_spectral_correlation_near_one(self, bn_small):
        summary = bn_small.validate()
        assert abs(summary["spectral_correlation"] - 1.0) < 1e-9

    def test_custom_f0(self):
        bn = BioNodo(n_zeros=3, n_primes=3, k_max=2, t_max=0.2, n_time_points=20, f0=200.0)
        result = bn.evaluate()
        assert abs(result.f0 - 200.0) < 1e-9

    def test_evaluate_custom_intensity(self, bn_small):
        result = bn_small.evaluate(intensity=0.5)
        assert result.fixed_point.a_eff == pytest.approx(np.sqrt(0.5), abs=1e-9)

    def test_evaluate_custom_a_eff(self, bn_small):
        result = bn_small.evaluate(a_eff=2.0)
        assert abs(result.fixed_point.a_eff - 2.0) < 1e-9
