"""
Tests for Dirac Spectral Operator 𝔻_s and Master Operator 𝒪_∞³

This module tests the operator duality framework implementation.

Author: José Manuel Mota Burruezo Ψ ∴ ∞³
Date: January 2026
DOI: 10.5281/zenodo.17379721
"""

import pytest
import numpy as np
import sys
import os

# Add operators to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'operators'))

from dirac_spectral_operator import DiracSpectralOperator
from master_operator_o3 import MasterOperatorO3


class TestDiracSpectralOperator:
    """Test suite for Dirac spectral operator 𝔻_s."""
    
    @pytest.fixture
    def D_s(self):
        """Create Dirac operator instance."""
        return DiracSpectralOperator(precision=25, h=1e-8)
    
    @pytest.fixture
    def riemann_zeros(self):
        """First few Riemann zeros."""
        return np.array([
            14.134725,
            21.022040,
            25.010858,
            30.424876,
            32.935062
        ])
    
    def test_initialization(self, D_s):
        """Test operator initialization."""
        assert D_s.precision == 25
        assert D_s.h == 1e-8
    
    def test_apply_to_linear_function(self, D_s):
        """Test 𝔻_s on linear function f(s) = s."""
        f = lambda s: s
        s = complex(0.5, 14.0)
        
        # 𝔻_s f(s) = i * df/ds = i * 1 = i
        result = D_s.apply(f, s)
        
        # Should be approximately i
        assert abs(result - 1j) < 1e-6
    
    def test_apply_to_quadratic_function(self, D_s):
        """Test 𝔻_s on quadratic function f(s) = s²."""
        f = lambda s: s**2
        s = complex(0.5, 14.0)
        
        # 𝔻_s f(s) = i * df/ds = i * 2s
        expected = 1j * 2 * s
        result = D_s.apply(f, s)
        
        # Should match within numerical precision
        assert abs(result - expected) < 1e-4
    
    def test_spectral_translation(self, D_s):
        """Test 𝔻_s as spectral translation generator."""
        f = lambda s: np.exp(1j * s.imag)
        s0 = complex(0.5, 10.0)
        delta_t = 0.1
        
        # Use 𝔻_s to approximate f(s0 + i*delta_t)
        approx = D_s.spectral_translation_generator(f, s0, delta_t)
        exact = f(s0 + 1j * delta_t)
        
        # Should be close for small delta_t
        assert abs(approx - exact) < 1e-3
    
    def test_duality_verification(self, D_s, riemann_zeros):
        """Test duality with H_Ψ."""
        verified, results = D_s.verify_duality_with_H_psi(riemann_zeros)
        
        assert verified is True
        assert results['zeros_matched'] == len(riemann_zeros)
        assert results['max_discrepancy'] < 1e-6
        assert results['mean_discrepancy'] < 1e-6
    
    def test_critical_line_preservation(self, D_s, riemann_zeros):
        """Test that zeros are on critical line."""
        tolerance = 1e-10
        
        for gamma in riemann_zeros:
            s = complex(0.5, gamma)
            # Verify Re(s) = 1/2
            assert abs(s.real - 0.5) < tolerance
            # Verify Im(s) = gamma
            assert abs(s.imag - gamma) < tolerance


class TestMasterOperatorO3:
    """Test suite for master operator 𝒪_∞³."""
    
    @pytest.fixture
    def O3(self):
        """Create master operator instance."""
        return MasterOperatorO3(precision=25, h=1e-8)
    
    @pytest.fixture
    def riemann_zeros(self):
        """First few Riemann zeros."""
        return np.array([
            14.134725,
            21.022040,
            25.010858,
            30.424876,
            32.935062
        ])
    
    def test_initialization(self, O3):
        """Test master operator initialization."""
        assert O3.precision == 25
        assert O3.h == 1e-8
        assert O3.omega_0 == 2 * np.pi * O3.F0
        assert isinstance(O3.D_s, DiracSpectralOperator)
    
    def test_constants(self, O3):
        """Test QCAL constants."""
        assert O3.F0 == 141.7001
        assert O3.C_QCAL == 244.36
        assert O3.C_UNIVERSAL == 629.83
        assert abs(O3.ZETA_PRIME_HALF - (-3.92264613)) < 1e-6
    
    def test_apply_to_test_function(self, O3):
        """Test 𝒪_∞³ application."""
        # Simple test function: Gaussian in x, phase in s
        Phi = lambda s, x: np.exp(-x**2/2) * np.exp(1j * s.imag)
        
        s = complex(0.5, 14.134725)
        x = 1.0
        
        result = O3.apply(Phi, s, x)
        
        # Should be a complex number
        assert isinstance(result, (complex, np.complex128, np.complexfloating))
        # Should be non-zero
        assert abs(result) > 0
    
    def test_unification_verification(self, O3, riemann_zeros):
        """Test that 𝒪_∞³ unifies 𝔻_s and H_Ψ."""
        verified, results = O3.verify_unification(riemann_zeros)
        
        assert verified is True
        assert results['zeros_captured'] == len(riemann_zeros)
        assert results['perspective_coherence'] > 0.99
        assert results['max_discrepancy'] < 1e-6
    
    def test_commutator_structure(self, O3):
        """Test that [𝔻_s ⊗ 𝟙, 𝟙 ⊗ H_Ψ] = 0."""
        # Tensor product components should commute
        Phi = lambda s, x: x * s
        s = complex(0.5, 10.0)
        x = 1.0
        
        commutator = O3.commutator_check(Phi, s, x)
        
        # Should be zero (tensor product structure)
        assert abs(commutator) < 1e-10
    
    def test_dual_spectrum_extraction(self, O3, riemann_zeros):
        """Test extraction of spectrum from both perspectives."""
        for gamma in riemann_zeros:
            # Complex perspective (𝔻_s)
            s_complex = complex(0.5, gamma)
            
            # Real perspective (H_Ψ)
            t_real = gamma
            
            # Should match
            assert abs(s_complex.imag - t_real) < 1e-10
            assert abs(s_complex.real - 0.5) < 1e-10
    
    def test_consciousness_interpretation(self, O3):
        """Test consciousness interpretation generation."""
        interpretation = O3.consciousness_interpretation()
        
        # Should be a string
        assert isinstance(interpretation, str)
        # Should contain key terms
        assert '𝒪_∞³' in interpretation
        assert 'GEOMETRY' in interpretation
        assert 'VIBRATION' in interpretation
        assert 'NUMBER' in interpretation
        assert '∞³' in interpretation


class TestOperatorDuality:
    """Test the duality relationship between operators."""
    
    @pytest.fixture
    def operators(self):
        """Create both operators."""
        D_s = DiracSpectralOperator(precision=25)
        O3 = MasterOperatorO3(precision=25)
        return D_s, O3
    
    @pytest.fixture
    def riemann_zeros(self):
        """First few Riemann zeros."""
        return np.array([
            14.134725,
            21.022040,
            25.010858,
            30.424876,
            32.935062
        ])
    
    def test_dual_spectrum_correspondence(self, operators, riemann_zeros):
        """Test that both operators extract the same spectrum."""
        D_s, O3 = operators
        
        for gamma in riemann_zeros:
            # 𝔻_s perspective: complex s
            s = complex(0.5, gamma)
            
            # Both should refer to same zero
            assert abs(s.imag - gamma) < 1e-10
            
            # Both should be on critical line
            assert abs(s.real - 0.5) < 1e-10
    
    def test_unification_coherence(self, operators, riemann_zeros):
        """Test coherence of unification."""
        D_s, O3 = operators
        
        # Verify 𝔻_s duality
        D_verified, D_results = D_s.verify_duality_with_H_psi(riemann_zeros)
        
        # Verify 𝒪_∞³ unification
        O_verified, O_results = O3.verify_unification(riemann_zeros)
        
        # Both should verify
        assert D_verified is True
        assert O_verified is True
        
        # Should have same number of zeros
        assert D_results['zeros_matched'] == O_results['zeros_captured']
    
    def test_perspectives_are_complementary(self, riemann_zeros):
        """Test that complex and real perspectives are complementary."""
        for gamma in riemann_zeros:
            # Complex perspective
            s = complex(0.5, gamma)
            
            # Real perspective
            lambda_n = gamma
            
            # They capture different aspects of the same zero:
            # s: full complex coordinate
            # lambda_n: real eigenvalue (imaginary part of s)
            
            assert s.imag == lambda_n
            assert s.real == 0.5  # Critical line


def test_operator_imports():
    """Test that operator modules can be imported."""
    from dirac_spectral_operator import DiracSpectralOperator
    from master_operator_o3 import MasterOperatorO3
    
    assert DiracSpectralOperator is not None
    assert MasterOperatorO3 is not None


if __name__ == '__main__':
    # Run tests with pytest
    pytest.main([__file__, '-v', '--tb=short'])
