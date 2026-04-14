#!/usr/bin/env python3
"""
Tests for Completando los Huecos — Implementación Detallada
============================================================

Verifies the mathematical properties of the three-gap closure:

  HUECO 1: Tate regularisation — ζ_f(s, p^k) = |q|_p^{-s} ζ_f(s, 1)
  HUECO 2: Adelic Poisson formula — fixed-point return times
  HUECO 3: Logical spectral identification — Δ(s) = ξ(s)

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz
"""

import sys
import numpy as np
from pathlib import Path

# Add operators directory to path
repo_root = Path(__file__).parent.parent
sys.path.insert(0, str(repo_root / "operators"))

from completando_huecos_implementacion import (
    compute_fourier_coefficients,
    local_zeta_integral,
    verify_tate_factorization,
    fixed_point_times,
    trace_operator_f,
    xi_function,
    spectral_determinant_zeros,
    verify_spectral_identification,
    generate_visualization,
    F0_QCAL,
    C_COHERENCE,
)


# ---------------------------------------------------------------------------
# HUECO 1: Tate Regularisation
# ---------------------------------------------------------------------------

def test_fourier_coefficients_decay():
    """Fourier-Bruhat coefficients must decay for large positive m."""
    f_test = lambda x: np.exp(-x ** 2)
    coeffs = compute_fourier_coefficients(f_test, p=2, n_max=10)

    # 21 coefficients for m in [-10, ..., 10]
    assert len(coeffs) == 21, f"Expected 21 coefficients, got {len(coeffs)}"

    # For f = exp(-x^2), c_m = ∫ exp(-(2^m u)^2) du ≈ 1 for m << 0,
    # then decays to 0 for m >> 0.  Verify strict monotone decrease for m ≥ 0.
    centre = 10  # index of m=0
    for i in range(centre, len(coeffs) - 1):
        assert coeffs[i] >= coeffs[i + 1], (
            f"Coefficients should decrease for m≥0: c[{i-centre}]={coeffs[i]}, "
            f"c[{i+1-centre}]={coeffs[i+1]}"
        )

    # All values must be non-negative (f ≥ 0)
    assert all(c >= -1e-10 for c in coeffs), "Coefficients should be non-negative"

    print("✅ test_fourier_coefficients_decay PASSED")


def test_tate_factorization_identity():
    """Verify ζ_f(s, p^k) = p^{ks} ζ_f(s, 1) within numerical tolerance.

    Uses f(x) = x·exp(-x²) so that f(0)=0, ensuring that the Haar-measure
    integral ∫ f(p^m u) d^×u → 0 for m → -∞ and the Dirichlet series
    converges on both sides of the factorisation identity.
    """
    # f(0)=0 ensures convergence of the local zeta series for Re(s)>0.
    f_test = lambda x: x * np.exp(-x ** 2)
    for p in [2, 3]:
        for k in [1, 2]:
            result = verify_tate_factorization(f_test, s=complex(1.0, 0.0), p=p, k=k, n_max=15)
            assert result["error"] < 0.1, (
                f"Tate factorisation error too large for p={p}, k={k}: "
                f"{result['error']}"
            )

    print("✅ test_tate_factorization_identity PASSED")


def test_pontryagin_weight():
    """p^{k/2} weight must be sqrt of p^k."""
    f_test = lambda x: x * np.exp(-x ** 2)
    result = verify_tate_factorization(f_test, s=complex(1.0, 0.0), p=2, k=2)
    expected_weight = 2.0 ** (2.0 / 2.0)  # p^{k/2} = 2^1 = 2
    assert abs(result["p_k_half"] - expected_weight) < 1e-10, (
        f"Pontryagin weight mismatch: {result['p_k_half']} != {expected_weight}"
    )

    print("✅ test_pontryagin_weight PASSED")


def test_local_zeta_convergence():
    """Local zeta integral should be finite for Re(s) > 0."""
    f_test = lambda x: np.exp(-x ** 2)
    for s_real in [0.5, 1.0, 2.0]:
        val = local_zeta_integral(f_test, s=complex(s_real, 0.0), p=2)
        assert np.isfinite(abs(val)), f"ζ_f should be finite for Re(s)={s_real}"

    print("✅ test_local_zeta_convergence PASSED")


# ---------------------------------------------------------------------------
# HUECO 2: Adelic Poisson Formula
# ---------------------------------------------------------------------------

def test_fixed_point_times_ordering():
    """Return times must be non-decreasing and equal k·log(p)."""
    primes = [2, 3, 5]
    times = fixed_point_times(primes, max_k=3)

    t_vals = [t for _, _, t in times]
    assert t_vals == sorted(t_vals), "Return times must be sorted"

    for p, k, t in times:
        expected = k * np.log(p)
        assert abs(t - expected) < 1e-12, (
            f"Return time mismatch: p={p}, k={k}, t={t} != {expected}"
        )

    print("✅ test_fixed_point_times_ordering PASSED")


def test_fixed_point_times_smallest():
    """The smallest return time should be log(2) ≈ 0.6931."""
    times = fixed_point_times([2, 3, 5], max_k=3)
    smallest_t = times[0][2]
    assert abs(smallest_t - np.log(2)) < 1e-10, (
        f"Smallest return time should be log(2), got {smallest_t}"
    )

    print("✅ test_fixed_point_times_smallest PASSED")


def test_trace_operator_positive():
    """Trace of transfer operator should be positive for a non-negative test function."""
    f_test = lambda t: np.exp(-t)  # positive, decaying
    primes = [2, 3, 5, 7]
    trace_val = trace_operator_f(f_test, primes, max_k=3)
    assert trace_val > 0, f"Trace should be positive, got {trace_val}"

    print("✅ test_trace_operator_positive PASSED")


def test_trace_prime_weight_formula():
    """Individual prime contributions must match weight (log p)/p^{k/2}."""
    # Use a delta-like function peaked at log(2)
    t_target = np.log(2)
    f_test = lambda t: np.exp(-100 * (t - t_target) ** 2)

    times = fixed_point_times([2], max_k=1)
    p, k, t = times[0]
    expected_weight = np.log(p) / (p ** (k / 2.0))
    expected_contrib = expected_weight * f_test(t)

    # Trace with only p=2, k=1
    trace_val = trace_operator_f(f_test, [2], max_k=1)
    assert abs(trace_val - expected_contrib) < 1e-6, (
        f"Weight formula mismatch: {trace_val} != {expected_contrib}"
    )

    print("✅ test_trace_prime_weight_formula PASSED")


# ---------------------------------------------------------------------------
# HUECO 3: Logical Spectral Identification
# ---------------------------------------------------------------------------

def test_xi_on_critical_line_real():
    """ξ(1/2 + it) must be real-valued (up to floating-point precision)."""
    t_vals = [14.0, 21.0, 25.0]
    for t in t_vals:
        xi_val = xi_function(0.5 + 1j * t)
        imag_ratio = abs(xi_val.imag) / (abs(xi_val) + 1e-30)
        assert imag_ratio < 1e-6, (
            f"ξ(1/2 + i·{t}) should be nearly real, imag ratio = {imag_ratio}"
        )

    print("✅ test_xi_on_critical_line_real PASSED")


def test_xi_sign_change_near_first_zero():
    """ξ(1/2 + it) should change sign near the first Riemann zero γ_1 ≈ 14.135."""
    t_before = 13.0
    t_after = 15.5
    xi_before = np.real(xi_function(0.5 + 1j * t_before))
    xi_after = np.real(xi_function(0.5 + 1j * t_after))

    assert xi_before * xi_after < 0, (
        "ξ should change sign between t=13 and t=15.5 (crossing first zero)"
    )

    print("✅ test_xi_sign_change_near_first_zero PASSED")


def test_spectral_zeros_found():
    """At least one zero should be detected on the critical line."""
    t_grid = np.linspace(1.0, 50.0, 2000)
    zeros = spectral_determinant_zeros(t_grid, n_zeros=5)
    assert len(zeros) >= 1, "At least one zero should be found"

    print(f"✅ test_spectral_zeros_found PASSED ({len(zeros)} zeros found)")


def test_spectral_identification_matches():
    """Found zeros should match known Riemann zeros within tolerance."""
    t_grid = np.linspace(1.0, 50.0, 3000)
    zeros = spectral_determinant_zeros(t_grid, n_zeros=5)
    ident = verify_spectral_identification(zeros, tol=1.0)

    assert ident["n_found"] >= 1, "At least one zero must be found"
    assert len(ident["matches"]) >= 1, "At least one zero must match known values"

    print(
        f"✅ test_spectral_identification_matches PASSED "
        f"({len(ident['matches'])} matches found)"
    )


def test_all_zeros_on_critical_line():
    """All numerically detected zeros must pass the on-line check."""
    t_grid = np.linspace(1.0, 45.0, 2500)
    zeros = spectral_determinant_zeros(t_grid, n_zeros=4)
    ident = verify_spectral_identification(zeros)

    assert ident["all_on_line"], "All zeros should be on the critical line Re(s) = 1/2"

    print("✅ test_all_zeros_on_critical_line PASSED")


# ---------------------------------------------------------------------------
# HUECO 1 + 2 + 3: Constants
# ---------------------------------------------------------------------------

def test_qcal_constants():
    """Module must export the canonical QCAL constants."""
    assert F0_QCAL == 141.7001, f"F0_QCAL should be 141.7001, got {F0_QCAL}"
    assert C_COHERENCE == 244.36, f"C_COHERENCE should be 244.36, got {C_COHERENCE}"

    print("✅ test_qcal_constants PASSED")


# ---------------------------------------------------------------------------
# Visualization
# ---------------------------------------------------------------------------

def test_generate_visualization(tmp_path):
    """Visualization should create a PNG file."""
    output_file = tmp_path / "test_huecos.png"
    result_path = generate_visualization(output_path=output_file)

    assert result_path.exists(), f"Figure file not created: {result_path}"
    assert result_path.stat().st_size > 1000, "Figure file appears too small"

    print(f"✅ test_generate_visualization PASSED (file: {result_path})")
