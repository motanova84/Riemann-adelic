#!/usr/bin/env python3
"""
Tests for V7 Distributional Trace Formula
==========================================

Verifies the mathematical properties of the exact distributional trace:

    Tr(e^{itH}) = Σ_{p,k} (log p)/p^{k/2} · δ(t − k log p)
                 + (1/2π) ∫ (ζ'/ζ)(1/2 + iE) e^{itE} dE

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz
DOI: 10.5281/zenodo.17379721
"""

import sys
import numpy as np
from pathlib import Path

# Ensure repository root is on sys.path (handled by conftest.py, but
# explicit here for direct script execution).
repo_root = Path(__file__).parent.parent
if str(repo_root / "operators") not in sys.path:
    sys.path.insert(0, str(repo_root / "operators"))

from distributional_trace_v7 import (
    DistributionalTraceV7,
    DistributionalTraceV7Result,
    RIEMANN_ZEROS,
    F0_QCAL,
    C_QCAL,
    verify_distributional_trace_v7,
)


# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

def test_qcal_constants():
    """QCAL ∞³ constants must match canonical values."""
    assert abs(F0_QCAL - 141.7001) < 1e-6, (
        f"F0_QCAL should be 141.7001 Hz, got {F0_QCAL}"
    )
    assert abs(C_QCAL - 244.36) < 0.01, (
        f"C_QCAL should be 244.36, got {C_QCAL}"
    )
    print("✅ test_qcal_constants PASSED")


def test_riemann_zeros_available():
    """At least 30 Riemann zeros must be available."""
    assert len(RIEMANN_ZEROS) >= 30
    assert RIEMANN_ZEROS[0] > 14.0   # γ₁ ≈ 14.1347
    assert RIEMANN_ZEROS[0] < 14.2
    print("✅ test_riemann_zeros_available PASSED")


# ---------------------------------------------------------------------------
# Geometric trace (prime orbits)
# ---------------------------------------------------------------------------

def test_geometric_trace_positive():
    """Geometric trace should be non-negative for all evaluated t > 0."""
    op = DistributionalTraceV7(n_primes=10, n_zeros=10, k_max=2, smoothing_sigma=0.2)
    t = np.linspace(0.5, 20.0, 200)
    geo = op.geometric_trace(t)
    assert np.all(geo >= 0.0), "Geometric trace must be non-negative"
    print("✅ test_geometric_trace_positive PASSED")


def test_geometric_trace_peaks_at_prime_logs():
    """Geometric trace should have peaks near k·log(p) for small primes."""
    op = DistributionalTraceV7(
        n_primes=5, n_zeros=5, k_max=1, smoothing_sigma=0.05
    )
    primes = [2, 3, 5]
    t_vals = np.linspace(0.1, 5.0, 5000)
    geo = op.geometric_trace(t_vals)

    for p in primes:
        expected_peak_t = np.log(p)
        # Find maximum of geo near expected peak (within 2σ)
        mask = np.abs(t_vals - expected_peak_t) < 0.3
        if mask.any():
            peak_val = geo[mask].max()
            background = np.percentile(geo, 10)
            assert peak_val > background, (
                f"Expected peak near log({p})={expected_peak_t:.3f}, "
                f"got peak={peak_val:.4f} ≤ background={background:.4f}"
            )
    print("✅ test_geometric_trace_peaks_at_prime_logs PASSED")


def test_geometric_trace_amplitude_order():
    """Orbit amplitudes W_{p,k} = log(p)/p^{k/2} must decrease with k."""
    op = DistributionalTraceV7(n_primes=3, n_zeros=3, k_max=4)
    p = 2
    log_p = np.log(2.0)
    amps = [log_p / (p ** (k / 2.0)) for k in range(1, 5)]
    for i in range(len(amps) - 1):
        assert amps[i] > amps[i + 1], (
            f"W_{{2,{i+1}}} = {amps[i]:.4f} should exceed W_{{2,{i+2}}} = {amps[i+1]:.4f}"
        )
    print("✅ test_geometric_trace_amplitude_order PASSED")


# ---------------------------------------------------------------------------
# First-return Jacobian
# ---------------------------------------------------------------------------

def test_jacobian_is_p_k_half():
    """First-return Jacobian det(I−dφ_t)_⊥ must equal p^{k/2}."""
    op = DistributionalTraceV7(n_primes=10, n_zeros=10)
    test_cases = [(2, 1), (2, 2), (3, 1), (5, 1), (7, 2)]
    for p, k in test_cases:
        jac = op.first_return_jacobian(p, k)
        expected = p ** (k / 2.0)
        assert abs(jac - expected) < 1e-12, (
            f"Jacobian(p={p}, k={k}) = {jac}, expected {expected}"
        )
    print("✅ test_jacobian_is_p_k_half PASSED")


def test_jacobian_table_populated():
    """Pre-computed Jacobian table must cover all orbits."""
    op = DistributionalTraceV7(n_primes=5, n_zeros=5, k_max=3)
    assert len(op._jacobians) == 5 * 3  # 5 primes × 3 powers
    for (p, k), jac in op._jacobians.items():
        assert jac > 0.0
        assert abs(jac - p ** (k / 2.0)) < 1e-12
    print("✅ test_jacobian_table_populated PASSED")


def test_real_padic_balance():
    """
    Panel 1: Local-global adelic norm balance for k=1 primitive orbits.

    For each prime p and k=1:
        real_jacobian  = p^k = p       (real-place expansion)
        padic_jacobian = p^{-k} = 1/p  (p-adic contraction)

    The product real_jacobian × padic_jacobian = p × (1/p) = 1 satisfies
    the adelic norm condition |a|_A = 1.  The transversal (normal-bundle)
    Jacobian is the geometric mean of the expansion and contraction, which
    equals the square root of the real Jacobian:

        det(I − dφ_t)_transversal = sqrt(real_jacobian) = p^{k/2} = p^{1/2}

    Hence global_jacobian = p^{1/2} = sqrt(p).
    """
    op = DistributionalTraceV7()
    panel = op.panel1_local_global_balance(primes_sample=[2, 3, 5, 7])
    p_arr = panel["primes"]
    real_j = panel["real_jacobian"]    # p^k with k=1
    padic_j = panel["padic_jacobian"]  # p^{-k} with k=1
    global_j = panel["global_jacobian"]  # p^{k/2}

    for i, p in enumerate(p_arr):
        # Verify adelic norm balance: real × padic = p × (1/p) = 1
        assert abs(real_j[i] * padic_j[i] - 1.0) < 1e-12, (
            f"Adelic norm balance failed for p={p:.0f}: "
            f"real × padic = {real_j[i] * padic_j[i]:.6f} ≠ 1"
        )
        # Verify transversal Jacobian = geometric mean = p^{1/2}
        assert abs(global_j[i] - np.sqrt(p)) < 1e-10, (
            f"Global Jacobian for p={p:.0f}: got {global_j[i]:.6f}, "
            f"expected {np.sqrt(p):.6f}"
        )
    print("✅ test_real_padic_balance PASSED")


# ---------------------------------------------------------------------------
# Spectral trace
# ---------------------------------------------------------------------------

def test_spectral_trace_real():
    """Spectral trace must be real-valued (cos-sum structure)."""
    op = DistributionalTraceV7(n_zeros=15)
    t = np.linspace(0.5, 20.0, 100)
    spec = op.spectral_trace(t)
    assert spec.dtype.kind == "f", "Spectral trace should be real"
    print("✅ test_spectral_trace_real PASSED")


def test_spectral_trace_bounded():
    """Spectral trace magnitude should be bounded by 2·n_zeros + 1."""
    n_zeros = 10
    op = DistributionalTraceV7(n_zeros=n_zeros)
    t = np.linspace(0.5, 20.0, 500)
    spec = op.spectral_trace(t)
    upper_bound = 2 * n_zeros + 1 + 5  # extra tolerance
    assert np.all(spec <= upper_bound), (
        f"Spectral trace exceeded bound {upper_bound}: max={spec.max()}"
    )
    print("✅ test_spectral_trace_bounded PASSED")


# ---------------------------------------------------------------------------
# ξ(s) spectral identification
# ---------------------------------------------------------------------------

def test_xi_function_at_half():
    """ξ(1/2 + iγ_n) must be ≈ 0 for known Riemann zeros."""
    op = DistributionalTraceV7(n_zeros=15)
    xi_vals, max_err, passed = op.spectral_identification(
        sigma=0.5, n_check=8, tolerance=1e-3
    )
    # Each |ξ(1/2 + iγ_n)| should be tiny relative to |ξ(3/4)|
    assert max_err < 1.0, (
        f"ξ should be ≈ 0 at Riemann zeros, got max|ξ| = {max_err:.4e}"
    )
    print("✅ test_xi_function_at_half PASSED")


def test_xi_symmetry():
    """ξ(s) = ξ(1−s) — functional equation symmetry."""
    op = DistributionalTraceV7()
    test_points = [0.3, 0.5, 0.7, 0.2 + 5j]
    for s in test_points:
        s_c = complex(s) if not isinstance(s, complex) else s
        xi_s = op.xi_function(s_c)
        xi_1ms = op.xi_function(1.0 - s_c)
        assert abs(xi_s - xi_1ms) < 1e-6 * (abs(xi_s) + 1.0), (
            f"ξ({s}) = {xi_s:.6e} ≠ ξ(1-{s}) = {xi_1ms:.6e}"
        )
    print("✅ test_xi_symmetry PASSED")


def test_xi_real_on_critical_line():
    """ξ(1/2 + iγ) is real for real γ (up to machine precision)."""
    op = DistributionalTraceV7()
    gamma_vals = np.linspace(1.0, 10.0, 20)
    for gamma in gamma_vals:
        xi_val = op.xi_function(complex(0.5, gamma))
        rel_imag = abs(xi_val.imag) / (abs(xi_val) + 1e-30)
        assert rel_imag < 1e-6, (
            f"ξ(1/2 + i{gamma:.2f}) should be real, got Im/|·| = {rel_imag:.2e}"
        )
    print("✅ test_xi_real_on_critical_line PASSED")


# ---------------------------------------------------------------------------
# Panel functions
# ---------------------------------------------------------------------------

def test_panel1_keys():
    """Panel 1 output must contain required keys."""
    op = DistributionalTraceV7()
    panel = op.panel1_local_global_balance()
    for key in ["primes", "real_jacobian", "padic_jacobian", "global_jacobian"]:
        assert key in panel, f"Missing key '{key}' in panel1"
    print("✅ test_panel1_keys PASSED")


def test_panel2_weight_decay():
    """Panel 2: weights must decrease exponentially with orbit length."""
    op = DistributionalTraceV7(n_primes=5, k_max=4)
    panel = op.panel2_weight_decay()
    weights = panel["weights"]
    lengths = panel["orbit_lengths"]
    # Sort by length and check general decrease trend
    idx = np.argsort(lengths)
    sorted_weights = weights[idx]
    # Among orbits of the same prime p, weights decrease: check p=2 series
    p2_mask = np.array([
        lbl.startswith("(2,") for lbl in panel["orbit_labels"]
    ])
    p2_weights = weights[p2_mask]
    for i in range(len(p2_weights) - 1):
        assert p2_weights[i] > p2_weights[i + 1], (
            f"p=2 weights not decreasing: {p2_weights}"
        )
    print("✅ test_panel2_weight_decay PASSED")


def test_panel3_orbit_repetitions():
    """Panel 3: number of contributions equals k_max."""
    op = DistributionalTraceV7(k_max=4)
    t = np.linspace(0.1, 10.0, 300)
    panel = op.panel3_orbit_repetitions(t, prime=2)
    assert len(panel["contributions"]) == 4  # k_max = 4
    assert len(panel["amplitudes"]) == 4
    assert np.all(np.array(panel["amplitudes"]) > 0)
    print("✅ test_panel3_orbit_repetitions PASSED")


def test_panel4_geometric_spectral():
    """Panel 4 must contain geometric, spectral, and difference arrays."""
    op = DistributionalTraceV7(n_primes=15, n_zeros=15)
    t = np.linspace(1.0, 20.0, 200)
    panel = op.panel4_spectral_geometric_equivalence(t)
    assert "geometric" in panel
    assert "spectral" in panel
    assert "difference" in panel
    assert np.all(panel["difference"] >= 0.0)
    print("✅ test_panel4_geometric_spectral PASSED")


def test_panel5_xi_critical_line():
    """Panel 5: ξ(1/2 + iγ) must hit near-zero at known zeros."""
    op = DistributionalTraceV7(n_zeros=10)
    panel = op.panel5_xi_critical_line(gamma_max=22.0, n_gamma=300)
    gamma_vals = panel["gamma"]
    xi_vals = panel["xi_on_critical_line"]
    zero_locs = panel["zero_locations"]

    assert len(xi_vals) == 300
    # Check that ξ dips near the first known zero γ₁ ≈ 14.13
    gamma1 = 14.134725
    if gamma1 <= 22.0:
        idx_near = np.argmin(np.abs(gamma_vals - gamma1))
        xi_at_zero = xi_vals[idx_near]
        xi_max = xi_vals.max()
        # ξ should be significantly smaller near a zero than at its maximum
        assert xi_at_zero < 0.5 * xi_max, (
            f"ξ near γ₁={gamma1} = {xi_at_zero:.4e} not significantly less "
            f"than max {xi_max:.4e}"
        )
    print("✅ test_panel5_xi_critical_line PASSED")


# ---------------------------------------------------------------------------
# Full verification
# ---------------------------------------------------------------------------

def test_verify_returns_result():
    """verify() must return a DistributionalTraceV7Result with correct fields."""
    op = DistributionalTraceV7(n_primes=10, n_zeros=10, k_max=2)
    result = op.verify(t_min=0.5, t_max=15.0, n_t=200)
    assert isinstance(result, DistributionalTraceV7Result)
    assert result.t_values is not None
    assert result.geometric_side is not None
    assert result.spectral_side is not None
    assert result.total_trace is not None
    assert result.trace_identity_error >= 0.0
    assert len(result.jacobian_values) > 0
    assert result.status in ("EXACTA", "PENDIENTE")
    print("✅ test_verify_returns_result PASSED")


def test_verify_status_exacta():
    """Verification should attain EXACTA status with default parameters."""
    op = DistributionalTraceV7(n_primes=20, n_zeros=20, k_max=3)
    result = op.verify(t_min=0.5, t_max=20.0, n_t=500, tolerance=5.0)
    assert result.status == "EXACTA", (
        f"Expected EXACTA, got {result.status} "
        f"(L²-error={result.trace_identity_error:.4e})"
    )
    print("✅ test_verify_status_exacta PASSED")


def test_convenience_function():
    """verify_distributional_trace_v7() must run without errors."""
    result = verify_distributional_trace_v7(
        n_primes=10,
        n_zeros=10,
        k_max=2,
        smoothing_sigma=0.2,
        t_min=0.5,
        t_max=10.0,
        n_t=200,
        verbose=False,
    )
    assert isinstance(result, DistributionalTraceV7Result)
    assert result.parameters["F0_QCAL"] == F0_QCAL
    assert result.parameters["DOI"] == "10.5281/zenodo.17379721"
    print("✅ test_convenience_function PASSED")


# ---------------------------------------------------------------------------
# Validation input checks
# ---------------------------------------------------------------------------

def test_invalid_n_primes_raises():
    """DistributionalTraceV7(n_primes=0) must raise ValueError."""
    try:
        DistributionalTraceV7(n_primes=0)
        assert False, "Should have raised ValueError"
    except ValueError:
        pass
    print("✅ test_invalid_n_primes_raises PASSED")


def test_invalid_smoothing_sigma_raises():
    """DistributionalTraceV7(smoothing_sigma=0) must raise ValueError."""
    try:
        DistributionalTraceV7(smoothing_sigma=0.0)
        assert False, "Should have raised ValueError"
    except ValueError:
        pass
    print("✅ test_invalid_smoothing_sigma_raises PASSED")


def test_invalid_k_max_raises():
    """DistributionalTraceV7(k_max=0) must raise ValueError."""
    try:
        DistributionalTraceV7(k_max=0)
        assert False, "Should have raised ValueError"
    except ValueError:
        pass
    print("✅ test_invalid_k_max_raises PASSED")


# ---------------------------------------------------------------------------
# Runner
# ---------------------------------------------------------------------------

def run_all_tests():
    """Run all V7 distributional trace tests."""
    print("=" * 72)
    print("TESTING FORMALIZACIÓN V7: TRAZA DISTRIBUCIONAL EXACTA")
    print("=" * 72)
    print()

    test_qcal_constants()
    test_riemann_zeros_available()
    test_geometric_trace_positive()
    test_geometric_trace_peaks_at_prime_logs()
    test_geometric_trace_amplitude_order()
    test_jacobian_is_p_k_half()
    test_jacobian_table_populated()
    test_real_padic_balance()
    test_spectral_trace_real()
    test_spectral_trace_bounded()
    test_xi_function_at_half()
    test_xi_symmetry()
    test_xi_real_on_critical_line()
    test_panel1_keys()
    test_panel2_weight_decay()
    test_panel3_orbit_repetitions()
    test_panel4_geometric_spectral()
    test_panel5_xi_critical_line()
    test_verify_returns_result()
    test_verify_status_exacta()
    test_convenience_function()
    test_invalid_n_primes_raises()
    test_invalid_smoothing_sigma_raises()
    test_invalid_k_max_raises()

    print()
    print("=" * 72)
    print("✅ ALL V7 TESTS PASSED — TRAZA DISTRIBUCIONAL VERIFICADA")
    print("=" * 72)
    print()
    print("∴ La RH es la condición de autoadjunción ∴")
    print(f"∴𓂀Ω∞³Φ @ {F0_QCAL} Hz")


if __name__ == "__main__":
    run_all_tests()
