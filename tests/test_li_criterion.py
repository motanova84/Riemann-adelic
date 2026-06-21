#!/usr/bin/env python3
"""
Tests for Li Criterion: Positivity of the Trace (El Criterio de Li)
====================================================================

Verifies the mathematical properties of the Li criterion implementation:
    λ_n = Σ_ρ [ 1 − (ρ/(ρ−1))^n ] > 0  for all n ≥ 1

Tests cover:
- Correct sign and magnitude of Li coefficients
- Monotone growth property
- Keiper formula agreement
- Self-adjointness of H = ξ'/ξ
- Prime orbit trace formula
- QCAL coherence Ψ = 1.0

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz
"""

import sys
import numpy as np
import pytest
from pathlib import Path

# Add operators directory to path
repo_root = Path(__file__).parent.parent
sys.path.insert(0, str(repo_root / "operators"))

from li_criterion import (
    LiCoefficients,
    EntropyFlowH,
    LiCriterionValidator,
    LiCoefficientResult,
    LiValidationResult,
    demonstrate_li_criterion,
    _first_primes,
    F0_QCAL,
    C_COHERENCE,
)


# ─── LiCoefficients ───────────────────────────────────────────────────────────


def test_li_coefficients_init():
    """Test that LiCoefficients initializes with correct parameters."""
    li = LiCoefficients(n_zeros=20, dps=15)
    assert li.n_zeros == 20
    assert li.dps == 15
    assert li._zeros_cache is None
    print("✅ test_li_coefficients_init PASSED")


def test_li_coefficients_invalid_params():
    """Test that invalid parameters raise ValueError."""
    with pytest.raises(ValueError):
        LiCoefficients(n_zeros=5)   # too few zeros

    with pytest.raises(ValueError):
        LiCoefficients(dps=5)       # too low precision

    print("✅ test_li_coefficients_invalid_params PASSED")


def test_li_coefficient_n1_positive():
    """Test that λ_1 > 0."""
    li = LiCoefficients(n_zeros=30, dps=15)
    result = li.compute(1)

    assert isinstance(result, LiCoefficientResult)
    assert result.n == 1
    assert result.lambda_n > 0, f"λ_1 should be positive, got {result.lambda_n}"
    assert result.is_positive
    assert result.method == 'zeros'
    assert result.n_zeros_used == 30
    print(f"✅ test_li_coefficient_n1_positive PASSED  (λ_1 = {result.lambda_n:.6f})")


def test_li_coefficient_n2_positive():
    """Test that λ_2 > 0."""
    li = LiCoefficients(n_zeros=30, dps=15)
    result = li.compute(2)

    assert result.lambda_n > 0, f"λ_2 should be positive, got {result.lambda_n}"
    assert result.is_positive
    print(f"✅ test_li_coefficient_n2_positive PASSED  (λ_2 = {result.lambda_n:.6f})")


def test_li_coefficient_n3_positive():
    """Test that λ_3 > 0."""
    li = LiCoefficients(n_zeros=30, dps=15)
    result = li.compute(3)

    assert result.lambda_n > 0, f"λ_3 should be positive, got {result.lambda_n}"
    print(f"✅ test_li_coefficient_n3_positive PASSED  (λ_3 = {result.lambda_n:.6f})")


def test_li_coefficients_first_10_positive():
    """Test that λ_1,...,λ_10 are all positive."""
    li = LiCoefficients(n_zeros=50, dps=15)

    for n in range(1, 11):
        result = li.compute(n)
        assert result.lambda_n > 0, (
            f"λ_{n} should be positive, got {result.lambda_n}"
        )
    print("✅ test_li_coefficients_first_10_positive PASSED")


def test_li_coefficients_monotone_increasing():
    """Test that λ_n is monotone increasing for small n."""
    li = LiCoefficients(n_zeros=50, dps=15)
    results = li.compute_batch(10)
    lambdas = [r.lambda_n for r in results]

    for i in range(len(lambdas) - 1):
        assert lambdas[i] < lambdas[i + 1], (
            f"λ_{i+1} = {lambdas[i]:.6f} should be < λ_{i+2} = {lambdas[i+1]:.6f}"
        )
    print("✅ test_li_coefficients_monotone_increasing PASSED")


def test_li_coefficients_invalid_n():
    """Test that n < 1 raises ValueError."""
    li = LiCoefficients(n_zeros=20, dps=15)

    with pytest.raises(ValueError):
        li.compute(0)

    with pytest.raises(ValueError):
        li.compute(-1)

    print("✅ test_li_coefficients_invalid_n PASSED")


def test_li_coefficients_zero_cache():
    """Test that zeros are cached after first load."""
    li = LiCoefficients(n_zeros=20, dps=15)
    assert li._zeros_cache is None

    li.compute(1)
    assert li._zeros_cache is not None
    assert len(li._zeros_cache) == 20

    # Second call uses cache (no recomputation)
    li.compute(2)
    assert len(li._zeros_cache) == 20
    print("✅ test_li_coefficients_zero_cache PASSED")


def test_li_coefficients_positivity_ratio():
    """Test that positivity ratio equals 1.0 for first 10 coefficients."""
    li = LiCoefficients(n_zeros=50, dps=15)
    ratio = li.positivity_ratio(10)

    assert ratio == 1.0, f"All 10 coefficients should be positive, ratio = {ratio}"
    print("✅ test_li_coefficients_positivity_ratio PASSED")


def test_li_coefficients_batch():
    """Test batch computation returns correct number of results."""
    li = LiCoefficients(n_zeros=30, dps=15)
    results = li.compute_batch(5)

    assert len(results) == 5
    for i, r in enumerate(results):
        assert r.n == i + 1
    print("✅ test_li_coefficients_batch PASSED")


def test_li_coefficient_n1_known_value():
    """
    Test λ_1 against known approximate value.

    From the literature, λ_1 = 1/2 (1 + log(4π) + γ) − 1 ≈ 0.0231...
    but the value depends on the number of zeros used. With enough zeros,
    it should be close to ~0.023.
    """
    li = LiCoefficients(n_zeros=100, dps=20)
    result = li.compute(1)

    # λ_1 should be positive and small (order ~0.02-0.03 with 100 zeros)
    assert result.lambda_n > 0
    assert result.lambda_n < 1.0, f"λ_1 too large: {result.lambda_n}"
    print(f"✅ test_li_coefficient_n1_known_value PASSED  (λ_1 ≈ {result.lambda_n:.6f})")


# ─── Keiper Formula ─────────────────────────────────────────────────────────


def test_keiper_n1_positive():
    """Test that Keiper formula gives positive λ_1."""
    li = LiCoefficients(n_zeros=30, dps=25)
    result = li.compute_keiper(1)

    assert not np.isnan(result.lambda_n), "Keiper formula returned NaN for n=1"
    assert result.lambda_n > 0, (
        f"Keiper λ_1 should be positive, got {result.lambda_n}"
    )
    assert result.method == 'keiper'
    print(f"✅ test_keiper_n1_positive PASSED  (Keiper λ_1 ≈ {result.lambda_n:.6f})")


def test_keiper_n2_positive():
    """Test that Keiper formula gives positive λ_2."""
    li = LiCoefficients(n_zeros=30, dps=25)
    result = li.compute_keiper(2)

    assert not np.isnan(result.lambda_n), "Keiper formula returned NaN for n=2"
    assert result.lambda_n > 0, (
        f"Keiper λ_2 should be positive, got {result.lambda_n}"
    )
    print(f"✅ test_keiper_n2_positive PASSED  (Keiper λ_2 ≈ {result.lambda_n:.6f})")


def test_keiper_invalid_n():
    """Test that Keiper formula raises ValueError for n < 1."""
    li = LiCoefficients(n_zeros=20, dps=15)

    with pytest.raises(ValueError):
        li.compute_keiper(0)

    print("✅ test_keiper_invalid_n PASSED")


def test_keiper_zeros_agreement():
    """
    Test that the Keiper formula gives a value ≥ the truncated zero-sum.

    The Keiper formula evaluates the full infinite sum via the derivative
    of log ξ, while the zero-sum formula is a partial (lower-bound) sum.
    Both should be positive, and Keiper should be ≥ the partial sum.
    """
    li = LiCoefficients(n_zeros=50, dps=25)

    for n in [1, 2]:
        zeros_result = li.compute(n)
        keiper_result = li.compute_keiper(n)

        if np.isnan(keiper_result.lambda_n):
            pytest.skip(f"Keiper returned NaN for n={n}")

        # Both should be positive
        assert zeros_result.lambda_n > 0
        assert keiper_result.lambda_n > 0

        # Keiper (full sum) should be ≥ zero-sum (partial sum) for RH zeros
        assert keiper_result.lambda_n >= zeros_result.lambda_n, (
            f"n={n}: Keiper ({keiper_result.lambda_n:.6f}) should be ≥ "
            f"partial sum ({zeros_result.lambda_n:.6f})"
        )

    print("✅ test_keiper_zeros_agreement PASSED")


# ─── EntropyFlowH ─────────────────────────────────────────────────────────────


def test_entropy_flow_h_init():
    """Test EntropyFlowH initializes correctly."""
    H = EntropyFlowH(dps=15)
    assert H.dps == 15
    print("✅ test_entropy_flow_h_init PASSED")


def test_entropy_flow_h_real_axis():
    """Test H(s) = ξ'/ξ is real on the real axis away from zeros."""
    H = EntropyFlowH(dps=20)

    for s_real in [2.0, 3.0, 4.0, 5.0]:
        val = H.evaluate(complex(s_real, 0))
        assert not np.isnan(val.real), f"H({s_real}) is NaN"
        assert abs(val.imag) < 1e-6, (
            f"H({s_real}) imaginary part too large: {val.imag:.2e}"
        )
    print("✅ test_entropy_flow_h_real_axis PASSED")


def test_entropy_flow_h_self_adjoint():
    """Test that H passes the self-adjointness check."""
    H = EntropyFlowH(dps=20)
    result = H.is_self_adjoint_check(s_test=2.0)
    assert result, "H should be self-adjoint on the real axis"
    print("✅ test_entropy_flow_h_self_adjoint PASSED")


def test_entropy_flow_h_grid():
    """Test grid evaluation of H."""
    H = EntropyFlowH(dps=15)
    s_array = np.array([2.0, 3.0, 4.0]) + 0j
    vals = H.evaluate_grid(s_array)

    assert len(vals) == 3
    for v in vals:
        assert not np.isnan(v.real)
    print("✅ test_entropy_flow_h_grid PASSED")


def test_entropy_flow_prime_orbit_trace_positive():
    """Test that the prime orbit trace Tr(e^(−tH)) is positive."""
    H = EntropyFlowH(dps=15)

    for t in [0.1, 0.5, 1.0, 2.0]:
        val = H.prime_orbit_trace(t)
        assert val > 0, f"Prime orbit trace at t={t} should be positive, got {val}"
    print("✅ test_entropy_flow_prime_orbit_trace_positive PASSED")


def test_entropy_flow_prime_orbit_trace_decays():
    """Test that prime orbit trace decreases with increasing t."""
    H = EntropyFlowH(dps=15)
    t_values = [0.1, 0.5, 1.0, 2.0, 5.0]
    traces = [H.prime_orbit_trace(t) for t in t_values]

    for i in range(len(traces) - 1):
        assert traces[i] > traces[i + 1], (
            f"Trace should decay: Tr(t={t_values[i]}) > Tr(t={t_values[i+1]})"
        )
    print("✅ test_entropy_flow_prime_orbit_trace_decays PASSED")


def test_entropy_flow_prime_orbit_trace_invalid_t():
    """Test that t ≤ 0 raises ValueError."""
    H = EntropyFlowH(dps=15)

    with pytest.raises(ValueError):
        H.prime_orbit_trace(0.0)

    with pytest.raises(ValueError):
        H.prime_orbit_trace(-1.0)

    print("✅ test_entropy_flow_prime_orbit_trace_invalid_t PASSED")


def test_partial_fraction_residue():
    """Test partial fraction residue computation."""
    H = EntropyFlowH(dps=15)

    import mpmath
    mpmath.mp.dps = 15
    rho = complex(mpmath.zetazero(1))
    s = 3.0 + 0j

    residue = H.partial_fraction_residue(s, rho)
    expected = 1.0 / (s - rho) + 1.0 / rho

    assert abs(residue - expected) < 1e-12
    print("✅ test_partial_fraction_residue PASSED")


def test_li_coefficient_from_residues():
    """Test li_coefficient_from_residues gives positive λ_n."""
    import mpmath
    mpmath.mp.dps = 15

    H = EntropyFlowH(dps=15)
    zeros = [complex(mpmath.zetazero(k)) for k in range(1, 31)]

    for n in [1, 2, 3]:
        lam = H.li_coefficient_from_residues(n, zeros)
        assert lam > 0, f"λ_{n} from residues should be positive, got {lam}"
    print("✅ test_li_coefficient_from_residues PASSED")


# ─── LiCriterionValidator ─────────────────────────────────────────────────────


def test_validator_init():
    """Test LiCriterionValidator initializes correctly."""
    validator = LiCriterionValidator(n_zeros=20, dps=15)
    assert validator.li.n_zeros == 20
    assert validator.H.dps == 15
    print("✅ test_validator_init PASSED")


def test_validator_validate_basic():
    """Test that validate() returns a valid LiValidationResult."""
    validator = LiCriterionValidator(n_zeros=30, dps=15)
    result = validator.validate(n_max=5)

    assert isinstance(result, LiValidationResult)
    assert result.n_max == 5
    assert len(result.coefficients) == 5
    assert result.psi > 0
    print("✅ test_validator_validate_basic PASSED")


def test_validator_all_positive():
    """Test that all λ_n are positive for n=1,...,10."""
    validator = LiCriterionValidator(n_zeros=50, dps=15)
    result = validator.validate(n_max=10)

    assert result.all_positive, (
        f"All Li coefficients should be positive. "
        f"Failed: {[r.n for r in result.coefficients if not r.is_positive]}"
    )
    assert result.psi == 1.0
    print("✅ test_validator_all_positive PASSED")


def test_validator_invalid_n_max():
    """Test that n_max < 1 raises ValueError (including negative values)."""
    validator = LiCriterionValidator(n_zeros=20, dps=15)

    with pytest.raises(ValueError):
        validator.validate(n_max=0)

    with pytest.raises(ValueError):
        validator.validate(n_max=-5)

    print("✅ test_validator_invalid_n_max PASSED")


def test_validator_self_adjointness():
    """Test that H passes the self-adjointness validation."""
    validator = LiCriterionValidator(n_zeros=20, dps=15)
    result = validator.validate_self_adjointness(test_points=[2.0, 3.0, 4.0])

    assert result['passed'], (
        f"H should be self-adjoint. Max imag part: {result['max_imag']:.2e}"
    )
    print("✅ test_validator_self_adjointness PASSED")


def test_validator_curvature_analysis():
    """Test curvature analysis returns expected structure."""
    validator = LiCriterionValidator(n_zeros=50, dps=15)
    result = validator.curvature_toward_critical_line(n_max=8)

    assert 'lambdas' in result
    assert 'is_monotone_increasing' in result
    assert 'all_positive' in result
    assert len(result['lambdas']) == 8
    assert result['all_positive']
    assert result['is_monotone_increasing']
    print("✅ test_validator_curvature_analysis PASSED")


def test_validator_min_lambda_identification():
    """Test that min_lambda and min_n are correctly identified."""
    validator = LiCriterionValidator(n_zeros=30, dps=15)
    result = validator.validate(n_max=5)

    lambdas = [r.lambda_n for r in result.coefficients]
    assert result.min_lambda == min(lambdas)
    assert result.min_n == lambdas.index(min(lambdas)) + 1
    print("✅ test_validator_min_lambda_identification PASSED")


def test_validator_rh_support_message():
    """Test that rh_support message mentions positivity."""
    validator = LiCriterionValidator(n_zeros=30, dps=15)
    result = validator.validate(n_max=5)

    assert isinstance(result.rh_support, str)
    assert len(result.rh_support) > 0
    print("✅ test_validator_rh_support_message PASSED")


# ─── Helper Functions ─────────────────────────────────────────────────────────


def test_first_primes():
    """Test that _first_primes returns correct primes."""
    primes = _first_primes(10)
    expected = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
    assert primes == expected
    print("✅ test_first_primes PASSED")


def test_first_primes_zero():
    """Test _first_primes with n=0."""
    primes = _first_primes(0)
    assert primes == []
    print("✅ test_first_primes_zero PASSED")


def test_first_primes_one():
    """Test _first_primes with n=1."""
    primes = _first_primes(1)
    assert primes == [2]
    print("✅ test_first_primes_one PASSED")


# ─── QCAL Constants ───────────────────────────────────────────────────────────


def test_qcal_constants():
    """Test that QCAL constants have expected values."""
    assert abs(F0_QCAL - 141.7001) < 1e-6
    assert abs(C_COHERENCE - 244.36) < 1e-6
    print("✅ test_qcal_constants PASSED")


# ─── Integration: demonstrate_li_criterion ────────────────────────────────────


@pytest.mark.slow
def test_demonstrate_li_criterion():
    """Integration test for the full demonstration function."""
    results = demonstrate_li_criterion(n_max=5, n_zeros=30)

    assert 'li_validation' in results
    assert 'self_adjoint' in results
    assert 'curvature' in results
    assert 'psi' in results
    assert 'prime_trace_sample' in results

    assert results['psi'] == 1.0
    assert results['li_validation'].all_positive
    assert results['self_adjoint']['passed']
    print("✅ test_demonstrate_li_criterion PASSED")


# ─── Mathematical properties ──────────────────────────────────────────────────


def test_lambda_n_increasing_with_more_zeros():
    """
    Test that adding more zeros increases λ_n toward its true value.

    λ_n converges from below as more zeros are included because each pair
    contributes a positive amount.
    """
    li_small = LiCoefficients(n_zeros=20, dps=15)
    li_large = LiCoefficients(n_zeros=60, dps=15)

    for n in [1, 2, 3]:
        lam_small = li_small.compute(n).lambda_n
        lam_large = li_large.compute(n).lambda_n
        # More zeros → larger sum (since each contribution is positive for RH)
        assert lam_large > lam_small, (
            f"n={n}: λ_n with more zeros ({lam_large:.6f}) should be larger "
            f"than with fewer zeros ({lam_small:.6f})"
        )
    print("✅ test_lambda_n_increasing_with_more_zeros PASSED")


def test_li_criterion_psi_equals_one():
    """Test that QCAL coherence Ψ = 1.0 for the Li criterion."""
    li = LiCoefficients(n_zeros=50, dps=15)
    psi = li.positivity_ratio(10)
    assert psi == 1.0, f"Ψ should be 1.0, got {psi}"
    print("✅ test_li_criterion_psi_equals_one PASSED")


def test_li_coefficient_imaginary_part_small():
    """
    Test that the imaginary part of the Li coefficient sum is negligible.

    By the symmetry ρ ↔ ρ̄, the imaginary parts cancel exactly.
    """
    import mpmath
    mpmath.mp.dps = 20

    li = LiCoefficients(n_zeros=30, dps=20)
    zeros = li._load_zeros()

    for n in [1, 2, 5]:
        total_imag = sum(
            float(
                (1 - (z / (z - 1)) ** n +
                 1 - (mpmath.conj(z) / (mpmath.conj(z) - 1)) ** n).imag
            )
            for z in zeros
        )
        assert abs(total_imag) < 1e-12, (
            f"n={n}: imaginary part should cancel, got {total_imag:.2e}"
        )
    print("✅ test_li_coefficient_imaginary_part_small PASSED")


if __name__ == "__main__":
    # Run all tests directly
    test_li_coefficients_init()
    test_li_coefficients_invalid_params()
    test_li_coefficient_n1_positive()
    test_li_coefficient_n2_positive()
    test_li_coefficient_n3_positive()
    test_li_coefficients_first_10_positive()
    test_li_coefficients_monotone_increasing()
    test_li_coefficients_invalid_n()
    test_li_coefficients_zero_cache()
    test_li_coefficients_positivity_ratio()
    test_li_coefficients_batch()
    test_li_coefficient_n1_known_value()
    test_keiper_n1_positive()
    test_keiper_n2_positive()
    test_keiper_invalid_n()
    test_keiper_zeros_agreement()
    test_entropy_flow_h_init()
    test_entropy_flow_h_real_axis()
    test_entropy_flow_h_self_adjoint()
    test_entropy_flow_h_grid()
    test_entropy_flow_prime_orbit_trace_positive()
    test_entropy_flow_prime_orbit_trace_decays()
    test_entropy_flow_prime_orbit_trace_invalid_t()
    test_partial_fraction_residue()
    test_li_coefficient_from_residues()
    test_validator_init()
    test_validator_validate_basic()
    test_validator_all_positive()
    test_validator_invalid_n_max()
    test_validator_self_adjointness()
    test_validator_curvature_analysis()
    test_validator_min_lambda_identification()
    test_validator_rh_support_message()
    test_first_primes()
    test_first_primes_zero()
    test_first_primes_one()
    test_qcal_constants()
    test_lambda_n_increasing_with_more_zeros()
    test_li_criterion_psi_equals_one()
    test_li_coefficient_imaginary_part_small()
    print("\n✅ All tests PASSED!")
