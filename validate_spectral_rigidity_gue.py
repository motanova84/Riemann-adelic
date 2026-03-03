#!/usr/bin/env python3
"""
Validation Script for Spectral Rigidity & GUE Module

Tests the implementation of validar_rigidez_espectral() and verifies:
1. Level spacing calculations for k=1 and k=2
2. GUE distance metrics
3. Visualization generation
4. Statistical properties

Author: José Manuel Mota Burruezo Ψ ∴ ∞³
Date: March 2026
"""

import sys
import os
import numpy as np
from pathlib import Path

# Add operators directory to path
sys.path.insert(0, str(Path(__file__).parent / 'operators'))

from spectral_rigidity_gue import (
    validar_rigidez_espectral,
    V_osc,
    compute_level_spacings,
    measure_gue_distance,
    poisson_distribution,
    wigner_dyson_distribution,
    generate_primes,
    generate_mock_eigenvalues,
)


def test_prime_generation():
    """Test that prime generation works correctly."""
    primes = generate_primes(50)
    assert len(primes) > 0
    assert primes[0] == 2
    assert primes[1] == 3
    assert primes[2] == 5
    # All should be prime
    for p in primes:
        assert all(p % i != 0 for i in range(2, int(p**0.5) + 1))
    print("✓ test_prime_generation passed")


def test_V_osc_k1():
    """Test oscillatory potential with k=1."""
    x = np.linspace(0.1, 10, 100)
    V1 = V_osc(x, k=1, n_primes=10)
    
    assert V1.shape == x.shape
    assert np.all(np.isfinite(V1))
    assert np.abs(np.mean(V1)) < 1.0  # Should oscillate around 0
    print("✓ test_V_osc_k1 passed")


def test_V_osc_k2():
    """Test oscillatory potential with k=2."""
    x = np.linspace(0.1, 10, 100)
    V2 = V_osc(x, k=2, n_primes=10)
    
    assert V2.shape == x.shape
    assert np.all(np.isfinite(V2))
    assert np.abs(np.mean(V2)) < 1.0
    print("✓ test_V_osc_k2 passed")


def test_level_spacings():
    """Test level spacing calculation."""
    # Simple test with uniform eigenvalues
    eigenvalues = np.array([1.0, 2.0, 3.0, 4.0, 5.0])
    spacings = compute_level_spacings(eigenvalues, unfold=False)
    
    assert len(spacings) == 4
    assert np.allclose(spacings, 1.0)
    print("✓ test_level_spacings passed")


def test_level_spacings_unfolded():
    """Test unfolded level spacing calculation."""
    eigenvalues = np.linspace(10, 100, 50)
    spacings = compute_level_spacings(eigenvalues, unfold=True)
    
    assert len(spacings) == 49
    assert np.all(spacings > 0)
    assert np.all(np.isfinite(spacings))
    print("✓ test_level_spacings_unfolded passed")


def test_poisson_distribution():
    """Test Poisson distribution function."""
    s = np.linspace(0, 5, 100)
    P_poisson = poisson_distribution(s)
    
    assert P_poisson.shape == s.shape
    assert np.all(P_poisson > 0)
    assert P_poisson[0] == 1.0  # P(0) = exp(0) = 1
    assert P_poisson[-1] < 0.01  # Should decay
    print("✓ test_poisson_distribution passed")


def test_wigner_dyson_distribution():
    """Test Wigner-Dyson (GUE) distribution function."""
    s = np.linspace(0, 5, 100)
    P_gue = wigner_dyson_distribution(s)
    
    assert P_gue.shape == s.shape
    assert np.all(P_gue >= 0)
    assert P_gue[0] == 0.0  # P(0) = 0 due to s^2 factor (level repulsion)
    # Should have maximum around s ≈ 1
    max_idx = np.argmax(P_gue)
    assert 0.5 < s[max_idx] < 1.5
    print("✓ test_wigner_dyson_distribution passed")


def test_gue_distance_metrics():
    """Test GUE distance metric calculation."""
    # Generate Poissonian spacings
    spacings_poisson = np.random.exponential(scale=1.0, size=100)
    metrics = measure_gue_distance(spacings_poisson)
    
    assert 'chi2_poisson' in metrics
    assert 'chi2_gue' in metrics
    assert 'poisson_ratio' in metrics
    assert metrics['chi2_poisson'] >= 0
    assert metrics['chi2_gue'] >= 0
    # For Poissonian data, should be closer to Poisson than GUE
    assert metrics['poisson_ratio'] > 1.0
    print("✓ test_gue_distance_metrics passed")


def test_generate_mock_eigenvalues_k1():
    """Test eigenvalue generation for k=1."""
    eigvals = generate_mock_eigenvalues(n_zeros=50, k=1)
    
    assert len(eigvals) == 50
    assert np.all(eigvals > 0)
    assert np.all(np.diff(eigvals) > 0)  # Should be sorted
    print("✓ test_generate_mock_eigenvalues_k1 passed")


def test_generate_mock_eigenvalues_k2():
    """Test eigenvalue generation for k=2."""
    eigvals = generate_mock_eigenvalues(n_zeros=50, k=2)
    
    assert len(eigvals) == 50
    assert np.all(eigvals > 0)
    assert np.all(np.diff(eigvals) > 0)  # Should be sorted
    print("✓ test_generate_mock_eigenvalues_k2 passed")


def test_validar_rigidez_espectral_basic():
    """Test basic functionality of validar_rigidez_espectral."""
    # Run with small n_zeros for speed
    results = validar_rigidez_espectral(n_zeros=50, verbose=False)
    
    assert 'conclusion' in results
    assert 'frequency' in results
    assert 'coherence' in results
    assert 'k1_metrics' in results
    assert 'k2_metrics' in results
    
    # Check frequency and coherence
    assert results['frequency'] == 888.0
    assert results['coherence'] == 244.36
    
    # Check that we got metrics
    assert 'chi2_poisson' in results['k1_metrics']
    assert 'chi2_gue' in results['k2_metrics']
    
    print("✓ test_validar_rigidez_espectral_basic passed")


def test_validar_rigidez_espectral_full():
    """Test full functionality with output generation."""
    # Create temporary output directory
    import tempfile
    with tempfile.TemporaryDirectory() as tmpdir:
        results = validar_rigidez_espectral(
            n_zeros=100,
            output_dir=tmpdir,
            verbose=False
        )
        
        # Check that plot was created
        assert 'plot_file' in results
        plot_path = Path(results['plot_file'])
        assert plot_path.exists()
        
        print("✓ test_validar_rigidez_espectral_full passed")


def test_k2_shows_repulsion():
    """Test that k=2 shows stronger repulsion than k=1."""
    results = validar_rigidez_espectral(n_zeros=100, verbose=False)
    
    k1_metrics = results['k1_metrics']
    k2_metrics = results['k2_metrics']
    
    # k=2 should be closer to GUE than k=1
    # (lower chi2_gue relative to chi2_poisson)
    k1_ratio = k1_metrics['chi2_gue'] / (k1_metrics['chi2_poisson'] + 1e-10)
    k2_ratio = k2_metrics['chi2_gue'] / (k2_metrics['chi2_poisson'] + 1e-10)
    
    # k=2 should have lower ratio (closer to GUE)
    assert k2_ratio < k1_ratio, "k=2 should show stronger GUE character than k=1"
    
    print("✓ test_k2_shows_repulsion passed")
    print(f"  k=1 GUE/Poisson ratio: {k1_ratio:.4f}")
    print(f"  k=2 GUE/Poisson ratio: {k2_ratio:.4f}")


def test_output_file_generation():
    """Test that output files are generated correctly."""
    import tempfile
    import json
    
    with tempfile.TemporaryDirectory() as tmpdir:
        results = validar_rigidez_espectral(
            n_zeros=50,
            output_dir=tmpdir,
            verbose=False
        )
        
        # Save JSON
        json_file = os.path.join(tmpdir, 'test_results.json')
        with open(json_file, 'w') as f:
            json.dump(results, f, indent=2)
        
        assert os.path.exists(json_file)
        
        # Verify JSON is valid
        with open(json_file, 'r') as f:
            loaded_results = json.load(f)
        
        assert loaded_results['frequency'] == 888.0
        
        print("✓ test_output_file_generation passed")


def run_all_tests():
    """Run all validation tests."""
    print("=" * 80)
    print("SPECTRAL RIGIDITY & GUE VALIDATION TESTS")
    print("=" * 80)
    print()
    
    tests = [
        test_prime_generation,
        test_V_osc_k1,
        test_V_osc_k2,
        test_level_spacings,
        test_level_spacings_unfolded,
        test_poisson_distribution,
        test_wigner_dyson_distribution,
        test_gue_distance_metrics,
        test_generate_mock_eigenvalues_k1,
        test_generate_mock_eigenvalues_k2,
        test_validar_rigidez_espectral_basic,
        test_validar_rigidez_espectral_full,
        test_k2_shows_repulsion,
        test_output_file_generation,
    ]
    
    passed = 0
    failed = 0
    
    for test in tests:
        try:
            test()
            passed += 1
        except AssertionError as e:
            print(f"✗ {test.__name__} FAILED: {e}")
            failed += 1
        except Exception as e:
            print(f"✗ {test.__name__} ERROR: {e}")
            failed += 1
    
    print()
    print("=" * 80)
    print(f"TEST SUMMARY: {passed} passed, {failed} failed out of {passed + failed} total")
    print("=" * 80)
    
    return failed == 0


if __name__ == '__main__':
    success = run_all_tests()
    sys.exit(0 if success else 1)
