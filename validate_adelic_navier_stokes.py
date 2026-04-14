#!/usr/bin/env python3
"""
Simple validation script for Adelic Navier-Stokes Implementation
=================================================================

Basic validation without pytest dependency.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
"""

import numpy as np
import sys
from pathlib import Path

# Add operators directory to path
sys.path.insert(0, str(Path(__file__).parent.parent / 'operators'))

from adelic_laplacian import AdelicLaplacian, SeeleyDeWittTensor
from navier_stokes_adelic import NavierStokesAdelic, FredholmDeterminant


def test_adelic_laplacian_basic():
    """Basic test of Adelic Laplacian."""
    print("Testing AdelicLaplacian basic functionality...")
    
    laplacian = AdelicLaplacian(n_points=50, n_primes=5)
    
    # Check initialization
    assert laplacian.kappa > 2.5 and laplacian.kappa < 2.6, "Kappa value incorrect"
    assert laplacian.f0 == 141.7001, "f0 value incorrect"
    assert len(laplacian.x) == 50, "Grid size incorrect"
    
    # Test archimedean Laplacian
    psi = np.random.randn(50)
    result = laplacian.archimedean_laplacian(psi)
    assert result.shape == psi.shape, "Shape mismatch"
    assert not np.any(np.isnan(result)), "NaN values detected"
    
    # Test p-adic Laplacian
    result_p = laplacian.p_adic_laplacian(psi, 2)
    assert result_p.shape == psi.shape, "Shape mismatch"
    
    # Test total action
    total = laplacian.total_action(psi)
    assert total.shape == psi.shape, "Shape mismatch"
    
    # Test symmetry
    verification = laplacian.verify_symmetry()
    assert verification['is_symmetric'], "Operator not symmetric"
    assert verification['is_positive'], "Operator not positive"
    
    print("✓ AdelicLaplacian tests passed")
    return True


def test_navier_stokes_basic():
    """Basic test of Navier-Stokes operator."""
    print("Testing NavierStokesAdelic basic functionality...")
    
    nse = NavierStokesAdelic(n_points=50, n_primes=5)
    
    # Check initialization
    assert nse.kappa > 2.5 and nse.kappa < 2.6, "Kappa value incorrect"
    assert nse.f0 == 141.7001, "f0 value incorrect"
    
    # Test effective potential
    V = nse.effective_potential(nse.x)
    assert V.shape == nse.x.shape, "Shape mismatch"
    assert np.all(V > 0), "Potential not positive"
    
    # Test transport term
    psi = nse.x**2
    transport = nse.transport_term(psi)
    assert transport.shape == psi.shape, "Shape mismatch"
    
    # Test diffusion term
    psi = np.random.randn(50)
    diffusion = nse.diffusion_term(psi)
    assert diffusion.shape == psi.shape, "Shape mismatch"
    
    # Test total action
    H_psi = nse.total_action(psi)
    assert H_psi.shape == psi.shape, "Shape mismatch"
    assert not np.any(np.isnan(H_psi)), "NaN values detected"
    
    # Test self-adjointness
    verification = nse.verify_self_adjointness()
    assert verification['hermiticity_error'] < 1e-6, f"Not Hermitian: error={verification['hermiticity_error']}"
    assert verification['all_eigenvalues_real'], "Eigenvalues not all real"
    
    print("✓ NavierStokesAdelic tests passed")
    return True


def test_spectrum_computation():
    """Test spectrum computation."""
    print("Testing spectrum computation...")
    
    nse = NavierStokesAdelic(n_points=50, n_primes=3)
    
    eigenvalues, eigenvectors = nse.get_spectrum(n_eigenvalues=10)
    
    assert len(eigenvalues) == 10, "Wrong number of eigenvalues"
    assert eigenvectors.shape == (50, 10), "Wrong eigenvector shape"
    
    # Eigenvalues should be real
    imag_part = np.max(np.abs(np.imag(eigenvalues)))
    assert imag_part < 1e-6, f"Eigenvalues not real: max imag={imag_part}"
    
    # Eigenvalues should be sorted
    assert np.all(np.diff(eigenvalues) >= -1e-10), "Eigenvalues not sorted"
    
    print(f"  First 10 eigenvalues: {eigenvalues[:10]}")
    print("✓ Spectrum computation tests passed")
    return True


def test_heat_kernel_trace():
    """Test heat kernel trace."""
    print("Testing heat kernel trace...")
    
    nse = NavierStokesAdelic(n_points=30, n_primes=3)
    
    trace = nse.heat_kernel_trace(t=0.1, method='spectral')
    
    assert not np.isnan(trace), "Trace is NaN"
    assert not np.isinf(trace), "Trace is infinite"
    
    print(f"  Heat kernel trace at t=0.1: {trace}")
    print("✓ Heat kernel trace tests passed")
    return True


def test_trace_decomposition():
    """Test trace decomposition."""
    print("Testing trace decomposition...")
    
    nse = NavierStokesAdelic(n_points=30, n_primes=5)
    
    decomp = nse.trace_decomposition(t=0.5)
    
    required_keys = ['weyl', 'prime_sum', 'remainder', 'total_approx', 'exact', 'error']
    for key in required_keys:
        assert key in decomp, f"Missing key: {key}"
        assert not np.isnan(decomp[key]), f"{key} is NaN"
    
    print(f"  Weyl term: {decomp['weyl']:.6f}")
    print(f"  Prime sum: {decomp['prime_sum']:.6f}")
    print(f"  Remainder: {decomp['remainder']:.6f}")
    print(f"  Total approx: {decomp['total_approx']:.6f}")
    print(f"  Exact: {decomp['exact']:.6f}")
    print(f"  Error: {decomp['error']:.6f}")
    print("✓ Trace decomposition tests passed")
    return True


def test_fredholm_determinant():
    """Test Fredholm determinant."""
    print("Testing Fredholm determinant...")
    
    nse = NavierStokesAdelic(n_points=30, n_primes=3)
    fredholm = FredholmDeterminant(nse)
    
    det = fredholm.determinant(t=0.5)
    log_det = fredholm.log_determinant(t=0.5)
    
    assert not np.isnan(det), "Determinant is NaN"
    assert not np.isnan(log_det), "Log determinant is NaN"
    
    # Check consistency: det = exp(log_det)
    det_from_log = np.exp(log_det)
    relative_error = np.abs(det - det_from_log) / (np.abs(det) + 1e-10)
    assert relative_error < 0.1, f"Inconsistent determinant: error={relative_error}"
    
    print(f"  Determinant at t=0.5: {det}")
    print(f"  Log determinant: {log_det}")
    print("✓ Fredholm determinant tests passed")
    return True


def test_constants_consistency():
    """Test that constants are consistent."""
    print("Testing constants consistency...")
    
    laplacian = AdelicLaplacian()
    nse = NavierStokesAdelic()
    
    assert laplacian.kappa == nse.kappa, "Kappa mismatch"
    assert laplacian.f0 == nse.f0, "f0 mismatch"
    
    # Verify kappa calculation
    f0 = 141.7001
    phi = (1 + np.sqrt(5)) / 2
    expected_kappa = 4 * np.pi / (f0 * phi)
    
    error = abs(nse.kappa - expected_kappa)
    assert error < 1e-6, f"Kappa calculation error: {error}"
    
    print(f"  κ = {nse.kappa:.6f} (expected: {expected_kappa:.6f})")
    print(f"  f₀ = {nse.f0} Hz")
    print("✓ Constants consistency tests passed")
    return True


def main():
    """Run all tests."""
    print("=" * 70)
    print("ADELIC NAVIER-STOKES VALIDATION")
    print("=" * 70)
    print()
    
    tests = [
        test_adelic_laplacian_basic,
        test_navier_stokes_basic,
        test_spectrum_computation,
        test_heat_kernel_trace,
        test_trace_decomposition,
        test_fredholm_determinant,
        test_constants_consistency,
    ]
    
    passed = 0
    failed = 0
    
    for test in tests:
        try:
            if test():
                passed += 1
            else:
                failed += 1
                print(f"✗ {test.__name__} FAILED")
        except Exception as e:
            failed += 1
            print(f"✗ {test.__name__} FAILED with exception:")
            print(f"  {type(e).__name__}: {e}")
        print()
    
    print("=" * 70)
    print(f"RESULTS: {passed} passed, {failed} failed")
    print("=" * 70)
    
    if failed == 0:
        print("✓ All tests passed successfully!")
        return 0
    else:
        print(f"✗ {failed} test(s) failed")
        return 1


if __name__ == '__main__':
    sys.exit(main())
