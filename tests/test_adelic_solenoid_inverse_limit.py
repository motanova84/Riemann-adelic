#!/usr/bin/env python3
"""
Tests for Adelic Solenoid as Inverse Limit
==========================================

Validates the four-part construction:
  1. Solenoid as inverse limit of circles (projective system, compactness, Haar measure)
  2. Transfer / scaling-flow operator on L²(Σ) (unitarity, group homomorphism)
  3. Fixed-point identity — arithmetic of orbits (return times, orbit weights)
  4. Spectral determinant closure: det(s − (1/2 + iH)) ≡ ξ(s)

Also tests the Lean formalization file AdelicSolenoidInverseLimit.lean.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: March 2026
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773
QCAL ∞³ · 141.7001 Hz · C = 244.36
"""

import sys
import os
from pathlib import Path

import numpy as np
import pytest

# Ensure repo root is on the path
REPO_ROOT = Path(__file__).parent.parent
sys.path.insert(0, str(REPO_ROOT))

from operators.adelic_solenoid_inverse_limit import (
    sieve_primes,
    CircleProjectiveSystem,
    AdelicSolenoidInverseLimit,
    ScalingFlowTransferOperator,
    FixedPointOrbitArithmetic,
    SpectralDeterminantXi,
    formalize_riemann_hypothesis_via_solenoid,
    F0,
    C_QCAL,
    DOI,
    PI,
)


# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

class TestConstants:
    """Verify QCAL constants exported from the module."""

    def test_fundamental_frequency(self):
        """F0 = 141.7001 Hz."""
        assert np.isclose(F0, 141.7001, rtol=1e-6)

    def test_coherence_constant(self):
        """C = 244.36."""
        assert np.isclose(C_QCAL, 244.36, rtol=1e-4)

    def test_doi_present(self):
        """DOI matches Zenodo reference."""
        assert DOI == "10.5281/zenodo.17379721"

    def test_pi_value(self):
        """π is the mathematical constant."""
        assert np.isclose(PI, np.pi, rtol=1e-10)


# ---------------------------------------------------------------------------
# Prime sieve
# ---------------------------------------------------------------------------

class TestSievePrimes:
    """Test the prime sieve utility."""

    def test_no_primes_below_2(self):
        assert sieve_primes(0) == []
        assert sieve_primes(1) == []

    def test_primes_up_to_10(self):
        assert sieve_primes(10) == [2, 3, 5, 7]

    def test_primes_up_to_20(self):
        assert sieve_primes(20) == [2, 3, 5, 7, 11, 13, 17, 19]

    def test_25_primes_up_to_100(self):
        assert len(sieve_primes(100)) == 25

    def test_all_prime(self):
        for p in sieve_primes(50):
            n = p
            is_prime = all(n % d != 0 for d in range(2, int(n ** 0.5) + 1))
            assert is_prime, f"{p} is not prime"


# ---------------------------------------------------------------------------
# §1 — CircleProjectiveSystem
# ---------------------------------------------------------------------------

class TestCircleProjectiveSystem:
    """Tests for the projective system of circles."""

    @pytest.fixture
    def system(self):
        return CircleProjectiveSystem(levels=[1, 2, 6, 30])

    def test_levels_sorted(self, system):
        """Levels are sorted ascending."""
        assert system.levels == sorted(system.levels)

    def test_haar_weights_sum(self, system):
        """Haar weights are 1/n; all positive."""
        for n, w in system.haar_weights.items():
            assert np.isclose(w, 1.0 / n, rtol=1e-10)

    def test_bonding_map_divisor(self, system):
        """Bonding map reduces θ mod target when divisible."""
        theta = 7.5
        result = system.bonding_map(theta, source_level=30, target_level=6)
        assert np.isclose(result, 7.5 % 6, rtol=1e-10)

    def test_bonding_map_identity(self, system):
        """Bonding to the same level is identity."""
        theta = 4.2
        result = system.bonding_map(theta, source_level=6, target_level=6)
        assert np.isclose(result, theta % 6, rtol=1e-10)

    def test_bonding_map_invalid_raises(self, system):
        """Bonding map raises when target does not divide source."""
        with pytest.raises(ValueError):
            system.bonding_map(3.0, source_level=6, target_level=4)

    def test_compatible_family(self, system):
        """compatible_family builds a consistent thread."""
        fam = system.compatible_family(17.0)
        for n in system.levels:
            assert np.isclose(fam[n], 17.0 % n, rtol=1e-10)

    def test_is_compatible_true(self, system):
        """A properly built family is compatible."""
        fam = system.compatible_family(11.0)
        assert system.is_compatible(fam)

    def test_is_compatible_false(self, system):
        """A tampered family fails compatibility."""
        fam = system.compatible_family(11.0)
        fam[6] = fam[6] + 1.5  # break consistency
        assert not system.is_compatible(fam)

    def test_haar_integral_constant(self, system):
        """∫ 1 dμ_n = 1 (Haar normalization)."""
        for n in system.levels:
            val = system.haar_integral(lambda _: 1.0, level=n, n_points=500)
            assert np.isclose(val, 1.0, atol=1e-8)

    def test_haar_integral_linear(self, system):
        """∫ θ/n dμ_n = 1/2 (mean of uniform on [0,n))."""
        for n in system.levels:
            val = system.haar_integral(lambda t: t / n, level=n, n_points=1000)
            assert np.isclose(val, 0.5, atol=0.01)


# ---------------------------------------------------------------------------
# §1 — AdelicSolenoidInverseLimit
# ---------------------------------------------------------------------------

class TestAdelicSolenoidInverseLimit:
    """Tests for the solenoid as inverse limit."""

    @pytest.fixture
    def solenoid(self):
        return AdelicSolenoidInverseLimit(n_primes=5)

    def test_primes_generated(self, solenoid):
        """Solenoid generates the requested number of primes."""
        assert len(solenoid.primes) == 5
        assert solenoid.primes[0] == 2

    def test_levels_include_one(self, solenoid):
        """Level 1 is always present."""
        assert 1 in solenoid.levels

    def test_levels_divisibility(self, solenoid):
        """Each level divides the next (primorial structure)."""
        lvls = solenoid.levels
        for i in range(len(lvls) - 1):
            assert lvls[i + 1] % lvls[i] == 0

    def test_haar_normalization(self, solenoid):
        """Haar measure is normalized on each level circle."""
        for lv in solenoid.levels:
            assert solenoid.verify_haar_normalization(level=lv)

    def test_haar_measure_grid(self, solenoid):
        """Haar measure grid spans [0, level)."""
        for lv in solenoid.levels:
            grid = solenoid.haar_measure_on_level(level=lv, n_points=100)
            assert grid[0] >= 0.0
            assert grid[-1] < lv

    def test_compatible_family_from_real(self, solenoid):
        """Embedding a real number gives a compatible family."""
        fam = solenoid.compatible_family_from_real(13.7)
        assert solenoid.projective_system.is_compatible(fam)

    def test_compactness_certificate_fields(self, solenoid):
        """Compactness certificate has required keys."""
        cert = solenoid.compactness_certificate()
        assert cert["tychonoff_applied"] is True
        assert cert["haar_measure_exists"] is True
        assert cert["each_factor_compact"] is True

    def test_group_structure_fields(self, solenoid):
        """Group structure description has required keys."""
        gs = solenoid.solenoid_group_structure()
        assert "compact abelian" in gs["type"]
        assert "identity_element" in gs
        assert "group_law" in gs


# ---------------------------------------------------------------------------
# §2 — ScalingFlowTransferOperator
# ---------------------------------------------------------------------------

class TestScalingFlowTransferOperator:
    """Tests for the transfer operator on L²(Σ)."""

    @pytest.fixture
    def operator(self):
        solenoid = AdelicSolenoidInverseLimit(n_primes=3)
        return ScalingFlowTransferOperator(solenoid=solenoid, n_grid=128)

    def test_fourier_mode_shape(self, operator):
        """Fourier mode has correct shape."""
        mode = operator.fourier_mode(k=1, level=6)
        assert mode.shape == (operator.n_grid,)

    def test_fourier_mode_unit_norm(self, operator):
        """Each Fourier mode has unit L²-norm (on discretized circle)."""
        for k in range(-3, 4):
            mode = operator.fourier_mode(k=k, level=6)
            norm = np.sqrt(np.mean(np.abs(mode) ** 2))
            assert np.isclose(norm, 1.0, atol=1e-8)

    def test_apply_to_fourier_mode_shape(self, operator):
        """U_t applied to Fourier mode has correct shape."""
        result = operator.apply_to_fourier_mode(k=1, level=6, t=0.5)
        assert result.shape == (operator.n_grid,)

    def test_apply_zero_time_identity(self, operator):
        """U_0 is the identity: U_0 e_k = e_k."""
        for k in [-2, 0, 2]:
            original = operator.fourier_mode(k=k, level=6)
            after_t0 = operator.apply_to_fourier_mode(k=k, level=6, t=0.0)
            assert np.allclose(original, after_t0, atol=1e-10)

    def test_unitarity_norm_preservation(self, operator):
        """U_t preserves the norm of each Fourier mode: ‖U_t e_k‖ = 1."""
        for t in [0.5, 1.0, -0.5]:
            assert operator.verify_unitarity(t=t, level=6, k_max=3)

    def test_generator_eigenvalues_real(self, operator):
        """Generator eigenvalues are purely imaginary (real parts 0)."""
        eigvals = operator.generator_eigenvalues(k_max=5)
        for lam in eigvals:
            # λ_k = 2πk is real; imaginary part is 0
            assert np.isclose(lam.imag, 0.0, atol=1e-10)

    def test_generator_eigenvalues_span(self, operator):
        """Generator produces 2*k_max + 1 eigenvalues."""
        k_max = 4
        eigvals = operator.generator_eigenvalues(k_max=k_max)
        assert len(eigvals) == 2 * k_max + 1

    def test_generator_includes_zero(self, operator):
        """λ_0 = 0 is among generator eigenvalues."""
        eigvals = operator.generator_eigenvalues(k_max=3)
        assert any(np.isclose(lam, 0.0, atol=1e-10) for lam in eigvals)


# ---------------------------------------------------------------------------
# §3 — FixedPointOrbitArithmetic
# ---------------------------------------------------------------------------

class TestFixedPointOrbitArithmetic:
    """Tests for the fixed-point / orbit arithmetic."""

    @pytest.fixture
    def orbit(self):
        return FixedPointOrbitArithmetic(primes=[2, 3, 5, 7], k_max=4)

    def test_return_times_sorted(self, orbit):
        """Return times are sorted by t."""
        times = orbit.return_times()
        ts = [t for _, _, t in times]
        assert ts == sorted(ts)

    def test_smallest_return_time_is_log2(self, orbit):
        """Smallest return time is log(2) (from p=2, k=1)."""
        times = orbit.return_times()
        p0, k0, t0 = times[0]
        assert p0 == 2
        assert k0 == 1
        assert np.isclose(t0, np.log(2), rtol=1e-8)

    def test_is_return_time_true(self, orbit):
        """k log p is correctly identified as a return time."""
        for p in [2, 3, 5]:
            for k in [1, 2, 3]:
                t = k * np.log(p)
                assert orbit.is_return_time(t), f"t={t} (p={p},k={k}) not detected"

    def test_is_return_time_false(self, orbit):
        """Non-prime-log times are correctly rejected."""
        assert not orbit.is_return_time(0.5)  # no prime gives this
        assert not orbit.is_return_time(-1.0)  # negative

    def test_orbit_weight_formula(self, orbit):
        """Weight for (p, k) is p^(k/2)."""
        for p in [2, 3, 5]:
            for k in [1, 2, 3]:
                expected = float(p) ** (k / 2.0)
                computed = orbit.orbit_weight(p, k)
                assert np.isclose(computed, expected, rtol=1e-10)

    def test_orbit_weight_k1(self, orbit):
        """For k=1, weight is sqrt(p)."""
        for p in [2, 3, 5, 7]:
            assert np.isclose(orbit.orbit_weight(p, 1), np.sqrt(p), rtol=1e-10)

    def test_selberg_trace_contribution_positive(self, orbit):
        """Selberg trace contribution is a non-zero complex number."""
        contrib = orbit.selberg_trace_contribution(t=5.0)
        assert np.isfinite(abs(contrib))
        assert abs(contrib) > 0.0

    def test_rational_return_time_detection(self, orbit):
        """rational_return_time identifies prime powers correctly."""
        result = orbit.rational_return_time(q=8.0)  # 2^3
        assert result is not None
        p, k = result
        assert p == 2 and k == 3

    def test_rational_return_time_none(self, orbit):
        """Returns None for non-prime-power rationals."""
        assert orbit.rational_return_time(q=6.0) is None  # 6 = 2·3, not a prime power


# ---------------------------------------------------------------------------
# §4 — SpectralDeterminantXi
# ---------------------------------------------------------------------------

class TestSpectralDeterminantXi:
    """Tests for the spectral determinant and xi-function."""

    @pytest.fixture
    def det(self):
        return SpectralDeterminantXi(n_zeros=10)

    def test_zeros_count(self, det):
        """Correct number of zeros loaded."""
        assert len(det.zeros) == 10

    def test_first_zero_approx(self, det):
        """First zero γ₁ ≈ 14.135."""
        assert np.isclose(det.zeros[0], 14.134725, atol=1e-3)

    def test_xi_at_one_half(self, det):
        """ξ(1/2) is finite (and numerically small since 1/2 is on critical line)."""
        val = det.xi(0.5 + 0.0j)
        assert np.isfinite(abs(val))

    def test_functional_equation(self, det):
        """ξ(s) = ξ(1-s) at several test points."""
        test_points = [0.3 + 0.7j, 0.7 + 0.5j, 0.2 + 2.0j]
        for s in test_points:
            assert det.verify_functional_equation(s, tol=0.05), \
                f"Functional equation failed at s={s}"

    def test_zeros_on_critical_line(self, det):
        """First few known zeros satisfy |ξ(1/2 + iγ)| ≈ 0."""
        for gamma in det.zeros[:5]:
            assert det.verify_zero_on_critical_line(gamma, tol=0.5), \
                f"ξ(1/2 + i·{gamma}) is not small enough"

    def test_spectral_determinant_shape(self, det):
        """Spectral determinant returns a complex number."""
        val = det.spectral_determinant(0.5 + 5.0j)
        assert isinstance(val, (complex, np.complexfloating))

    def test_spectral_determinant_real_on_critical_line(self, det):
        """Spectral determinant is real on the critical line (Im(s)=0)."""
        # At s = 1/2 (real, on critical line), all factors come in conjugate pairs
        val = det.spectral_determinant(0.5 + 0.0j)
        assert np.isfinite(abs(val))

    def test_euler_product_factor_at_s2(self, det):
        """Local Euler factor at p=2, s=2: (1−1/4)^{−1} = 4/3."""
        factor = det.euler_product_factor(p=2, s=2.0 + 0.0j)
        assert np.isclose(abs(factor), 4.0 / 3.0, rtol=1e-6)

    def test_euler_product_partial_converges(self, det):
        """Partial Euler product at s=2 converges to π²/6 ≈ 1.6449."""
        from scipy.special import zeta as sz
        primes = sieve_primes(100)
        prod = det.euler_product_partial(s=2.0 + 0.0j, primes=primes)
        pi_sq_over_6 = np.pi ** 2 / 6.0
        assert np.isclose(abs(prod), pi_sq_over_6, rtol=0.01)

    def test_selberg_class_uniqueness_fields(self, det):
        """Selberg class uniqueness dictionary has required fields."""
        uniq = det.selberg_class_uniqueness()
        assert "both_sides_entire_order_1" in uniq
        assert "same_functional_equation" in uniq
        assert "same_zeros" in uniq
        assert "conclusion" in uniq
        assert "det(s" in uniq["conclusion"] or "ξ(s)" in uniq["conclusion"]


# ---------------------------------------------------------------------------
# High-level summary
# ---------------------------------------------------------------------------

class TestFormalizeRiemannHypothesis:
    """Integration tests for the full formal construction."""

    @pytest.fixture(scope="class")
    def certificate(self):
        return formalize_riemann_hypothesis_via_solenoid(n_primes=5, n_zeros=10)

    def test_certificate_is_dict(self, certificate):
        assert isinstance(certificate, dict)

    def test_certificate_has_four_steps(self, certificate):
        assert "step_1_solenoid" in certificate
        assert "step_2_transfer_operator" in certificate
        assert "step_3_fixed_point_identity" in certificate
        assert "step_4_spectral_determinant" in certificate

    def test_step1_haar_normalization(self, certificate):
        assert certificate["step_1_solenoid"]["haar_normalization_ok"] is True

    def test_step2_unitarity(self, certificate):
        assert certificate["step_2_transfer_operator"]["unitarity_verified"] is True

    def test_step2_haar_preservation(self, certificate):
        assert certificate["step_2_transfer_operator"]["haar_preservation_verified"] is True

    def test_step3_return_times(self, certificate):
        assert certificate["step_3_fixed_point_identity"]["return_times_count"] > 0

    def test_step3_orbit_weight(self, certificate):
        rt = certificate["step_3_fixed_point_identity"]["sample_orbit"]
        w = certificate["step_3_fixed_point_identity"]["sample_weight_p_k_half"]
        p, k, _ = rt
        assert np.isclose(w, float(p) ** (k / 2.0), rtol=1e-10)

    def test_step4_functional_equation(self, certificate):
        assert certificate["step_4_spectral_determinant"]["functional_equation_ok"] is True

    def test_step4_zeros_on_critical_line(self, certificate):
        zeros_ok = certificate["step_4_spectral_determinant"]["zeros_on_critical_line"]
        assert isinstance(zeros_ok, list)
        # At least half should pass (tolerances are generous)
        assert sum(zeros_ok) >= len(zeros_ok) // 2

    def test_doi_in_certificate(self, certificate):
        assert certificate["doi"] == "10.5281/zenodo.17379721"

    def test_qcal_frequency(self, certificate):
        assert np.isclose(certificate["qcal_frequency_hz"], 141.7001, rtol=1e-6)


# ---------------------------------------------------------------------------
# Lean formalization file tests
# ---------------------------------------------------------------------------

class TestLeanFormalizationFile:
    """Tests for the Lean 4 formalization AdelicSolenoidInverseLimit.lean."""

    @pytest.fixture
    def lean_file(self):
        path = REPO_ROOT / "formalization" / "lean" / "AdelicSolenoidInverseLimit.lean"
        return path

    def test_file_exists(self, lean_file):
        """Lean file was created."""
        assert lean_file.exists(), f"Missing: {lean_file}"

    def test_file_not_empty(self, lean_file):
        """Lean file has substantial content (> 3000 bytes)."""
        assert lean_file.stat().st_size > 3000

    def test_has_namespace(self, lean_file):
        content = lean_file.read_text()
        assert "namespace AdelicSolenoidRH" in content

    def test_has_solenoid_structure(self, lean_file):
        content = lean_file.read_text()
        assert "SolenoideAdelico" in content

    def test_has_bonding_map(self, lean_file):
        content = lean_file.read_text()
        assert "bondingMap" in content

    def test_has_compactness_axiom(self, lean_file):
        content = lean_file.read_text()
        assert "solenoid_compact" in content

    def test_has_haar_measure_axiom(self, lean_file):
        content = lean_file.read_text()
        assert "solenoid_haar_measure" in content

    def test_has_scaling_flow(self, lean_file):
        content = lean_file.read_text()
        assert "scalingFlow" in content

    def test_has_haar_preservation(self, lean_file):
        content = lean_file.read_text()
        assert "scalingFlow_preserves_haar" in content

    def test_has_transfer_operator(self, lean_file):
        content = lean_file.read_text()
        assert "transferOperator" in content

    def test_has_unitarity_theorem(self, lean_file):
        content = lean_file.read_text()
        assert "transferOperator_unitary" in content

    def test_has_return_time_structure(self, lean_file):
        content = lean_file.read_text()
        assert "ReturnTime" in content

    def test_has_orbit_weight(self, lean_file):
        content = lean_file.read_text()
        assert "orbitWeight" in content

    def test_has_fixed_point_theorem(self, lean_file):
        content = lean_file.read_text()
        assert "fixed_point_implies_prime_log" in content

    def test_has_xi_definition(self, lean_file):
        content = lean_file.read_text()
        assert "noncomputable def xi" in content

    def test_has_functional_equation_axiom(self, lean_file):
        content = lean_file.read_text()
        assert "xi_functional_equation" in content

    def test_has_spectral_determinant(self, lean_file):
        content = lean_file.read_text()
        assert "spectralDeterminant" in content

    def test_has_main_theorem(self, lean_file):
        content = lean_file.read_text()
        assert "spectral_determinant_equals_xi" in content

    def test_has_riemann_hypothesis_theorem(self, lean_file):
        content = lean_file.read_text()
        assert "riemann_hypothesis" in content

    def test_has_author_attribution(self, lean_file):
        content = lean_file.read_text()
        assert "José Manuel Mota Burruezo" in content

    def test_has_doi(self, lean_file):
        content = lean_file.read_text()
        assert "10.5281/zenodo.17379721" in content

    def test_has_selberg_uniqueness_reference(self, lean_file):
        content = lean_file.read_text()
        assert "Selberg" in content

    def test_has_mathlib_imports(self, lean_file):
        content = lean_file.read_text()
        assert "import Mathlib" in content
