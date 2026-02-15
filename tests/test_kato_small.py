#!/usr/bin/env python3
"""
Tests for Kato-Small Property Verifier

This module validates the implementation of the Kato-small property verification
for operator B with respect to T.

Test Coverage:
    1. Matrix construction (T and B)
    2. Kato-small condition verification
    3. Convergence behavior as ε varies
    4. Boundary conditions
    5. Integration with QCAL framework

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: February 2026
QCAL ∞³ Active · 141.7001 Hz · C = 244.36 · Ψ = I × A_eff² × C^∞
"""

import pytest
import numpy as np
import sys
from pathlib import Path
import importlib.util

# Add root to path
sys.path.insert(0, str(Path(__file__).parent.parent))

# Import directly to avoid operators/__init__.py dependency issues
spec = importlib.util.spec_from_file_location(
    "kato_small_verifier",
    Path(__file__).parent.parent / "operators" / "kato_small_verifier.py"
)
kato_module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(kato_module)

KatoSmallTest = kato_module.KatoSmallTest
verify_kato_small_property = kato_module.verify_kato_small_property
KAPPA_DEFAULT = kato_module.KAPPA_DEFAULT
F0 = kato_module.F0
C_QCAL = kato_module.C_QCAL


class TestConstants:
    """Test QCAL constants."""
    
    def test_f0_value(self):
        """Fundamental frequency should be 141.7001 Hz."""
        assert abs(F0 - 141.7001) < 1e-4
    
    def test_c_qcal_value(self):
        """QCAL coherence constant should be 244.36."""
        assert abs(C_QCAL - 244.36) < 0.01
    
    def test_kappa_default(self):
        """Default κ should be 2.577310."""
        assert abs(KAPPA_DEFAULT - 2.577310) < 1e-6


class TestKatoSmallTest:
    """Test KatoSmallTest class."""
    
    def test_initialization(self):
        """Test basic initialization."""
        tester = KatoSmallTest(L=10.0, N=100, kappa=2.5)
        assert tester.L == 10.0
        assert tester.N == 100
        assert tester.kappa == 2.5
        assert len(tester.x) == 100
        assert tester.x[0] > 0  # Should start at small positive value
        assert tester.x[-1] <= 10.0
    
    def test_T_matrix_shape(self):
        """T matrix should be square."""
        tester = KatoSmallTest(N=100)
        T = tester.T_matrix()
        assert T.shape == (100, 100)
    
    def test_T_matrix_complex(self):
        """T matrix should be complex (anti-Hermitian)."""
        tester = KatoSmallTest(N=100)
        T = tester.T_matrix()
        assert np.iscomplexobj(T)
    
    def test_B_matrix_shape(self):
        """B matrix should be square."""
        tester = KatoSmallTest(N=100)
        B = tester.B_matrix()
        assert B.shape == (100, 100)
    
    def test_B_matrix_structure(self):
        """B matrix should have Laplacian + diagonal potential."""
        tester = KatoSmallTest(N=100)
        B = tester.B_matrix()
        # Check it's tridiagonal plus diagonal
        # (not strictly tridiagonal due to diagonal potential, but off-diagonal
        # should only be on superdiagonal and subdiagonal from Laplacian)
        for i in range(100):
            for j in range(100):
                if abs(i - j) > 1:
                    # Should be zero except on diagonal
                    if i != j:
                        assert abs(B[i, j]) < 1e-10
    
    def test_smooth_vector_generation(self):
        """Generated vectors should be smooth and satisfy boundary conditions."""
        tester = KatoSmallTest(N=100)
        psi = tester._generate_smooth_vector()
        
        # Check shape
        assert len(psi) == 100
        
        # Check boundary conditions
        assert abs(psi[0]) < 1e-10
        assert abs(psi[-1]) < 1e-10
        
        # Check it's complex
        assert np.iscomplexobj(psi)


class TestKatoSmallCondition:
    """Test Kato-small condition verification."""
    
    def test_kato_small_basic(self):
        """Test basic Kato-small verification."""
        tester = KatoSmallTest(L=20.0, N=200, kappa=KAPPA_DEFAULT)
        
        # Test with a single epsilon
        results = tester.test_kato_small(
            eps_values=[0.1],
            n_tests=100,
            verbose=False
        )
        
        assert len(results) == 1
        assert 'eps' in results[0]
        assert 'C_eps' in results[0]
        assert 'condition_met' in results[0]
        assert results[0]['eps'] == 0.1
        assert results[0]['condition_met'] is True
        assert results[0]['C_eps'] >= 0
        assert results[0]['C_eps'] < np.inf
    
    def test_kato_small_multiple_eps(self):
        """Test with multiple epsilon values."""
        tester = KatoSmallTest(L=20.0, N=200, kappa=KAPPA_DEFAULT)
        
        eps_values = [0.1, 0.05, 0.01]
        results = tester.test_kato_small(
            eps_values=eps_values,
            n_tests=100,
            verbose=False
        )
        
        assert len(results) == 3
        for i, r in enumerate(results):
            assert r['eps'] == eps_values[i]
            assert r['condition_met'] is True
    
    def test_C_eps_increases_as_eps_decreases(self):
        """C_ε should generally increase as ε decreases."""
        tester = KatoSmallTest(L=20.0, N=200, kappa=KAPPA_DEFAULT)
        
        eps_values = [0.1, 0.05, 0.01]
        results = tester.test_kato_small(
            eps_values=eps_values,
            n_tests=500,
            verbose=False
        )
        
        # Extract C_eps values
        C_eps_values = [r['C_eps'] for r in results]
        
        # Check monotonicity (allowing for some numerical variation)
        # At least the trend should be increasing
        assert C_eps_values[-1] > C_eps_values[0]
    
    def test_expected_C_eps_ranges(self):
        """Test that C_ε values are in expected ranges (from problem statement)."""
        tester = KatoSmallTest(L=20.0, N=500, kappa=KAPPA_DEFAULT)
        
        # Expected from problem statement (with some tolerance)
        expected = {
            0.1: (1.5, 3.5),    # Expected ~2.35
            0.05: (2.5, 4.5),   # Expected ~3.46
            0.01: (4.5, 7.0),   # Expected ~5.68
        }
        
        for eps, (min_C, max_C) in expected.items():
            results = tester.test_kato_small(
                eps_values=[eps],
                n_tests=1000,
                verbose=False
            )
            C_eps = results[0]['C_eps']
            assert min_C <= C_eps <= max_C, \
                f"C_ε for ε={eps} is {C_eps}, expected in [{min_C}, {max_C}]"


class TestCertificateGeneration:
    """Test certificate generation."""
    
    def test_certificate_format(self):
        """Certificate should be properly formatted."""
        tester = KatoSmallTest()
        results = [
            {'eps': 0.1, 'C_eps': 2.35, 'condition_met': True},
            {'eps': 0.05, 'C_eps': 3.46, 'condition_met': True},
        ]
        certificate = tester.generate_certificate(results)
        
        # Check key strings are present
        assert "KATO-PEQUEÑO" in certificate
        assert "OPERADORES" in certificate
        assert "VERIFICACIÓN NUMÉRICA" in certificate
        assert "COROLARIO" in certificate
        assert "JMMB" in certificate
        assert "∴𓂀Ω∞³Φ" in certificate
    
    def test_certificate_includes_results(self):
        """Certificate should include all results."""
        tester = KatoSmallTest()
        results = [
            {'eps': 0.1, 'C_eps': 2.35, 'condition_met': True},
            {'eps': 0.05, 'C_eps': 3.46, 'condition_met': True},
        ]
        certificate = tester.generate_certificate(results)
        
        # Check that epsilon values appear in certificate
        assert "0.100" in certificate
        assert "0.050" in certificate


class TestMainFunction:
    """Test main verification function."""
    
    def test_verify_kato_small_property(self):
        """Test main entry point."""
        results, certificate = verify_kato_small_property(
            L=15.0,
            N=200,
            kappa=KAPPA_DEFAULT,
            eps_values=[0.1, 0.05],
            n_tests=100,
            verbose=False
        )
        
        # Check results
        assert len(results) == 2
        assert all(r['condition_met'] for r in results)
        
        # Check certificate
        assert isinstance(certificate, str)
        assert len(certificate) > 100
        assert "KATO-PEQUEÑO" in certificate
    
    def test_reproducibility(self):
        """Test that results are stable across runs."""
        # Run twice with same seed
        np.random.seed(42)
        results1, _ = verify_kato_small_property(
            L=15.0,
            N=200,
            eps_values=[0.1],
            n_tests=100,
            verbose=False
        )
        
        np.random.seed(42)
        results2, _ = verify_kato_small_property(
            L=15.0,
            N=200,
            eps_values=[0.1],
            n_tests=100,
            verbose=False
        )
        
        # Results should be very close
        assert abs(results1[0]['C_eps'] - results2[0]['C_eps']) < 0.1


class TestNumericalStability:
    """Test numerical stability."""
    
    def test_no_nan_or_inf(self):
        """Results should not contain NaN or Inf."""
        tester = KatoSmallTest(N=200)
        results = tester.test_kato_small(
            eps_values=[0.1, 0.01],
            n_tests=100,
            verbose=False
        )
        
        for r in results:
            assert not np.isnan(r['C_eps'])
            assert not np.isinf(r['C_eps'])
    
    def test_different_grid_sizes(self):
        """Test with different grid sizes."""
        for N in [100, 200, 500]:
            tester = KatoSmallTest(N=N)
            results = tester.test_kato_small(
                eps_values=[0.1],
                n_tests=50,
                verbose=False
            )
            
            assert len(results) == 1
            assert results[0]['condition_met'] is True
            assert 0 < results[0]['C_eps'] < 10


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
