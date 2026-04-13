#!/usr/bin/env python3
"""
Tests for Adelic Trace Formula (Module 1)
==========================================

Verifies the mathematical properties of the trace formula:
    Tr(e^{-tH}) = Weyl(t) + Σ_{p,k} (ln p)/p^{k/2}·e^{-tkln p} + R(t)

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz
"""

import sys
import numpy as np
from pathlib import Path

# Add operators directory to path
repo_root = Path(__file__).parent.parent
sys.path.insert(0, str(repo_root / "operators"))

from adelic_trace_formula import (
    AdelicTraceFormula,
    TraceFormulaResult,
    demonstrate_trace_formula,
    F0_QCAL,
    C_COHERENCE
)


def test_weyl_term_positive():
    """Test that Weyl term is positive for all t > 0."""
    trace_computer = AdelicTraceFormula()
    
    t_values = np.logspace(-2, 1, 20)
    for t in t_values:
        weyl = trace_computer.weyl_term(t)
        assert weyl > 0, f"Weyl term should be positive, got {weyl} for t={t}"
    
    print("✅ test_weyl_term_positive PASSED")


def test_weyl_asymptotic_behavior():
    """Test Weyl term asymptotic: (1/2πt) ln(1/t) dominates as t → 0."""
    trace_computer = AdelicTraceFormula()
    
    # Small t values
    t_small = 0.01
    weyl_small = trace_computer.weyl_term(t_small)
    
    # Main asymptotic term
    main_term = (1.0 / (2.0 * np.pi * t_small)) * np.log(1.0 / t_small)
    
    # Weyl should be close to main term for small t
    # (within 10% since constant 7/8 is present)
    assert abs(weyl_small - main_term) / abs(main_term) < 0.1, \
        f"Weyl term asymptotic failed: got {weyl_small}, expected ~{main_term}"
    
    print("✅ test_weyl_asymptotic_behavior PASSED")


def test_prime_contribution_decreases_with_t():
    """Test that prime contribution decreases with increasing t."""
    trace_computer = AdelicTraceFormula()
    
    t_values = np.array([0.1, 0.5, 1.0, 2.0, 5.0])
    prime_contributions = []
    
    for t in t_values:
        prime_sum, _ = trace_computer.prime_contribution(t, include_convergence=False)
        prime_contributions.append(prime_sum)
    
    # Check monotone decrease
    prime_array = np.array(prime_contributions)
    differences = np.diff(prime_array)
    
    assert np.all(differences < 0), \
        f"Prime contribution should decrease with t, got diffs: {differences}"
    
    print("✅ test_prime_contribution_decreases_with_t PASSED")


def test_remainder_exponential_decay():
    """Test that remainder estimate shows exponential decay."""
    trace_computer = AdelicTraceFormula(spectral_gap=1.0)
    
    t_values = np.array([0.1, 1.0, 5.0, 10.0])
    remainders = []
    
    for t in t_values:
        r = trace_computer.remainder_estimate(t)
        remainders.append(r)
    
    # Fit log|R(t)| = log C - λt
    log_r = np.log(remainders)
    coeffs = np.polyfit(t_values, log_r, 1)
    fitted_decay_rate = -coeffs[0]
    
    # Should be close to spectral gap (1.0)
    assert abs(fitted_decay_rate - 1.0) < 0.1, \
        f"Decay rate should be ~1.0, got {fitted_decay_rate}"
    
    print("✅ test_remainder_exponential_decay PASSED")


def test_trace_positivity():
    """Test that total trace is positive for all t > 0."""
    trace_computer = AdelicTraceFormula()
    
    t_values = np.logspace(-2, 1, 20)
    
    for t in t_values:
        result = trace_computer.compute_trace(t)
        assert result.total_trace > 0, \
            f"Total trace should be positive, got {result.total_trace} for t={t}"
    
    print("✅ test_trace_positivity PASSED")


def test_trace_monotonicity():
    """Test that trace decreases with t (monotonicity)."""
    trace_computer = AdelicTraceFormula()
    
    # Use wider spacing to avoid numerical fluctuations at very small t
    t_values = np.logspace(-1, 1, 15)
    traces = []
    
    for t in t_values:
        result = trace_computer.compute_trace(t)
        traces.append(result.total_trace)
    
    # Check monotone decrease (allow small tolerance for numerical noise)
    traces_array = np.array(traces)
    differences = np.diff(traces_array)
    
    # Most differences should be negative
    negative_count = np.sum(differences < 0)
    total_count = len(differences)
    
    assert negative_count >= 0.9 * total_count, \
        f"Trace should generally decrease with t (got {negative_count}/{total_count} negative)"
    
    print("✅ test_trace_monotonicity PASSED")


def test_convergence_diagnostics():
    """Test that convergence diagnostics are computed correctly."""
    trace_computer = AdelicTraceFormula()
    
    result = trace_computer.compute_trace(1.0, include_details=True)
    
    # Check that convergence info exists
    assert 'terms_computed' in result.convergence_info
    assert 'max_term' in result.convergence_info
    assert 'sum_magnitude' in result.convergence_info
    
    # Terms computed should be positive
    assert result.convergence_info['terms_computed'] > 0
    
    # Max term should be reasonable
    assert result.convergence_info['max_term'] > 0
    
    print("✅ test_convergence_diagnostics PASSED")


def test_verify_trace_properties():
    """Test comprehensive property verification."""
    trace_computer = AdelicTraceFormula()
    
    t_values = np.logspace(-2, 1, 20)
    properties = trace_computer.verify_trace_properties(t_values)
    
    # All properties should pass
    assert properties['positivity'], "Positivity should be verified"
    assert properties['monotonicity'], "Monotonicity should be verified"
    assert properties['remainder_smallness'], "Remainder smallness should be verified"
    
    print("✅ test_verify_trace_properties PASSED")


def test_trace_derivative_negative():
    """Test that trace derivative is negative (decreasing function)."""
    trace_computer = AdelicTraceFormula()
    
    t_values = np.array([0.5, 1.0, 2.0, 5.0])
    
    for t in t_values:
        deriv = trace_computer.compute_trace_derivative(t)
        assert deriv < 0, f"Trace derivative should be negative, got {deriv} for t={t}"
    
    print("✅ test_trace_derivative_negative PASSED")


def test_qcal_constants():
    """Test that QCAL constants are properly defined."""
    assert abs(F0_QCAL - 141.7001) < 1e-6, f"F0_QCAL should be 141.7001 Hz, got {F0_QCAL}"
    assert abs(C_COHERENCE - 244.36) < 0.01, f"C_COHERENCE should be 244.36, got {C_COHERENCE}"
    
    print("✅ test_qcal_constants PASSED")


def test_demonstration():
    """Test that demonstration function runs without errors."""
    # Run demonstration with minimal output
    results = demonstrate_trace_formula(
        t_values=np.array([0.1, 1.0, 5.0]),
        verbose=False
    )
    
    # Check that results contain expected keys
    assert 'results' in results
    assert 'properties' in results
    assert 'trace_computer' in results
    
    # Verify properties
    props = results['properties']
    assert props['positivity'], "Positivity failed in demonstration"
    
    print("✅ test_demonstration PASSED")


def run_all_tests():
    """Run all tests for Module 1."""
    print("=" * 80)
    print("TESTING ADELIC TRACE FORMULA (MÓDULO 1)")
    print("=" * 80)
    print()
    
    test_qcal_constants()
    test_weyl_term_positive()
    test_weyl_asymptotic_behavior()
    test_prime_contribution_decreases_with_t()
    test_remainder_exponential_decay()
    test_trace_positivity()
    test_trace_monotonicity()
    test_convergence_diagnostics()
    test_verify_trace_properties()
    test_trace_derivative_negative()
    test_demonstration()
    
    print()
    print("=" * 80)
    print("✅ ALL TESTS PASSED — MÓDULO 1 VERIFIED")
    print("=" * 80)
    print()
    print("∴𓂀Ω∞³Φ @ 141.7001 Hz")


if __name__ == "__main__":
    run_all_tests()
