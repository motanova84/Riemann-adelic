"""
Test suite for Horizon Detector.

Tests the mathematical formalization:
    Horizonte ⟺ ker(H_Ψ - λI) ≠ {0}
    
That is:
    - Horizons occur when real eigenvalues appear
    - Zeros are points where the resolvent becomes singular
"""

import numpy as np
import pytest
import os
import sys

# Add parent directory to path for imports
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from operators.horizon_detector import (
    HorizonDetector,
    detect_horizons_from_operator,
    validate_horizon_riemann_correspondence
)
from operators.riemann_operator import (
    construct_H_psi,
    load_riemann_zeros
)


class TestHorizonDetectorBasics:
    """Test basic horizon detection functionality."""
    
    def test_simple_diagonal_operator(self):
        """Test horizon detection on simple diagonal operator."""
        # Create diagonal operator with known eigenvalues
        eigenvalues = np.array([1.0, 2.0, 3.0, 4.0, 5.0])
        H = np.diag(eigenvalues)
        
        detector = HorizonDetector(H)
        
        # All eigenvalues should be detected as horizons
        for ev in eigenvalues:
            assert detector.is_horizon(ev), f"Eigenvalue {ev} should be a horizon"
        
        # Non-eigenvalues should not be horizons
        assert not detector.is_horizon(1.5), "1.5 should not be a horizon"
        assert not detector.is_horizon(6.0), "6.0 should not be a horizon"
    
    def test_get_all_horizons(self):
        """Test retrieval of all horizons."""
        eigenvalues = np.array([1.0, 2.0, 3.0])
        H = np.diag(eigenvalues)
        
        detector = HorizonDetector(H)
        horizons = detector.get_all_horizons()
        
        assert len(horizons) == 3, "Should have 3 horizons"
        assert np.allclose(np.sort(horizons), eigenvalues), "Horizons should match eigenvalues"
    
    def test_kernel_dimension(self):
        """Test kernel dimension computation."""
        # Simple diagonal operator
        H = np.diag([1.0, 2.0, 2.0, 3.0])  # 2.0 has multiplicity 2
        
        detector = HorizonDetector(H)
        
        assert detector.get_kernel_dimension(1.0) == 1
        assert detector.get_kernel_dimension(2.0) == 2  # Degenerate eigenvalue
        assert detector.get_kernel_dimension(3.0) == 1
        assert detector.get_kernel_dimension(4.0) == 0  # Not an eigenvalue
    
    def test_hermiticity_requirement(self):
        """Test that detector requires Hermitian operator."""
        # Non-Hermitian matrix
        H_non_hermitian = np.array([[1, 2], [0, 1]])
        
        with pytest.raises(ValueError, match="Hermitian"):
            HorizonDetector(H_non_hermitian)


class TestResolventAnalysis:
    """Test resolvent singularity detection."""
    
    def test_resolvent_norm_at_horizon(self):
        """Test that resolvent norm is infinite at horizons."""
        H = np.diag([1.0, 2.0, 3.0])
        detector = HorizonDetector(H)
        
        # At eigenvalues (horizons), resolvent should be singular
        assert detector.resolvent_norm(1.0) == np.inf
        assert detector.resolvent_norm(2.0) == np.inf
        assert detector.resolvent_norm(3.0) == np.inf
    
    def test_resolvent_norm_away_from_horizon(self):
        """Test resolvent norm is finite away from horizons."""
        H = np.diag([1.0, 2.0, 3.0])
        detector = HorizonDetector(H)
        
        # Away from eigenvalues, resolvent should be finite
        norm_1_5 = detector.resolvent_norm(1.5)
        assert np.isfinite(norm_1_5), "Resolvent should be finite at 1.5"
        assert norm_1_5 > 0, "Resolvent norm should be positive"
        
        norm_0 = detector.resolvent_norm(0.0)
        assert np.isfinite(norm_0), "Resolvent should be finite at 0.0"
    
    def test_singularity_measure(self):
        """Test singularity measure increases near horizons."""
        H = np.diag([1.0, 2.0, 3.0])
        detector = HorizonDetector(H)
        
        # Singularity should be infinite at horizon
        assert detector.resolvent_singularity_measure(1.0) == np.inf
        
        # Singularity should decrease as we move away
        sing_1_1 = detector.resolvent_singularity_measure(1.1)
        sing_1_5 = detector.resolvent_singularity_measure(1.5)
        
        assert sing_1_1 > sing_1_5, "Singularity should be larger closer to horizon"
    
    def test_nearest_horizon(self):
        """Test finding nearest horizon."""
        H = np.diag([1.0, 2.0, 5.0])
        detector = HorizonDetector(H)
        
        # Test various points
        nearest, dist = detector.nearest_horizon(1.2)
        assert nearest == 1.0, "Nearest horizon to 1.2 should be 1.0"
        assert abs(dist - 0.2) < 1e-10
        
        nearest, dist = detector.nearest_horizon(3.5)
        assert nearest == 2.0 or nearest == 5.0  # Could be either
        
        nearest, dist = detector.nearest_horizon(1.0)
        assert nearest == 1.0
        assert dist < 1e-10  # Should be essentially zero


class TestEigenvectorRetrieval:
    """Test eigenvector retrieval for horizons."""
    
    def test_get_horizon_eigenvector(self):
        """Test retrieval of eigenvector at horizon."""
        # Simple 2x2 matrix with known eigenvectors
        H = np.array([[1.0, 0.0], [0.0, 2.0]])
        detector = HorizonDetector(H)
        
        # Get eigenvector for eigenvalue 1.0
        v1 = detector.get_horizon_eigenvector(1.0)
        assert v1 is not None, "Should find eigenvector for eigenvalue 1.0"
        
        # Verify it's an eigenvector: H·v = λ·v
        Hv = H @ v1
        lambda_v = 1.0 * v1
        assert np.allclose(Hv, lambda_v, atol=1e-10), "Should satisfy H·v = λ·v"
    
    def test_non_horizon_returns_none(self):
        """Test that non-horizons return None for eigenvector."""
        H = np.diag([1.0, 2.0, 3.0])
        detector = HorizonDetector(H)
        
        # Non-eigenvalue should return None
        v = detector.get_horizon_eigenvector(1.5)
        assert v is None, "Non-horizon should not have eigenvector"


class TestHorizonStructureAnalysis:
    """Test horizon structure analysis."""
    
    def test_analyze_horizon_structure(self):
        """Test complete horizon structure analysis."""
        H = np.diag([1.0, 2.0, 3.0, 4.0, 5.0])
        detector = HorizonDetector(H)
        
        analysis = detector.analyze_horizon_structure()
        
        # Check all expected fields are present
        assert 'n_horizons' in analysis
        assert 'eigenvalues' in analysis
        assert 'spectral_gaps' in analysis
        assert 'min_gap' in analysis
        assert 'max_gap' in analysis
        assert 'mean_gap' in analysis
        
        # Verify values
        assert analysis['n_horizons'] == 5
        assert np.allclose(analysis['spectral_gaps'], [1.0, 1.0, 1.0, 1.0])
        assert abs(analysis['min_gap'] - 1.0) < 1e-10
        assert abs(analysis['max_gap'] - 1.0) < 1e-10
        assert abs(analysis['mean_gap'] - 1.0) < 1e-10


class TestRiemannZeroCorrespondence:
    """Test correspondence between horizons and Riemann zeros."""
    
    @pytest.fixture
    def riemann_zeros(self):
        """Load first few Riemann zeros."""
        try:
            zeros = load_riemann_zeros(n_zeros=10)
            return zeros
        except FileNotFoundError:
            pytest.skip("Riemann zeros data file not found")
    
    def test_riemann_correspondence_analysis(self, riemann_zeros):
        """Test horizon-Riemann zero correspondence analysis."""
        # Use diagonal matrix with Riemann zeros for perfect match
        H = np.diag(riemann_zeros)
        detector = HorizonDetector(H)
        
        correspondence = detector.riemann_zero_correspondence(riemann_zeros)
        
        # Check structure
        assert 'n_zeros' in correspondence
        assert 'n_horizons' in correspondence
        assert 'max_error' in correspondence
        assert 'mean_error' in correspondence
        assert 'errors' in correspondence
        
        # Perfect match should have zero error
        assert correspondence['max_error'] < 1e-10, "Perfect match should have zero error"
        assert correspondence['mean_error'] < 1e-10
    
    def test_validate_correspondence_function(self, riemann_zeros):
        """Test convenience function for validation."""
        # Perfect match
        H_perfect = np.diag(riemann_zeros)
        assert validate_horizon_riemann_correspondence(
            H_perfect, riemann_zeros, tolerance=1e-8
        ), "Perfect match should validate"
        
        # Imperfect match
        H_imperfect = np.diag(riemann_zeros + 0.1)
        assert not validate_horizon_riemann_correspondence(
            H_imperfect, riemann_zeros, tolerance=1e-8
        ), "Imperfect match should not validate with tight tolerance"


class TestRealOperatorIntegration:
    """Test with actual H_Ψ operator from riemann_operator module."""
    
    @pytest.mark.slow
    def test_with_constructed_H_psi(self):
        """Test horizon detection with constructed H_Ψ operator."""
        try:
            # Construct H_Ψ with a few zeros
            H_psi, gamma_n = construct_H_psi(n_zeros=10)
            
            # Create detector
            detector = HorizonDetector(H_psi)
            
            # Get horizons
            horizons = detector.get_all_horizons()
            
            # Should have 10 horizons (eigenvalues)
            assert len(horizons) == 10, f"Expected 10 horizons, got {len(horizons)}"
            
            # Analyze correspondence
            correspondence = detector.riemann_zero_correspondence(gamma_n)
            
            # Should have reasonable agreement (constructor aims for high precision)
            print(f"\nHorizon-Riemann correspondence:")
            print(f"  Max error: {correspondence['max_error']:.2e}")
            print(f"  Mean error: {correspondence['mean_error']:.2e}")
            
            # The direct spectral construction should give very good agreement
            assert correspondence['max_error'] < 1e-6, "Should have good correspondence"
            
        except FileNotFoundError:
            pytest.skip("Riemann zeros data file not found")
    
    @pytest.mark.slow
    def test_horizon_analysis_comprehensive(self):
        """Comprehensive test of horizon analysis on H_Ψ."""
        try:
            # Construct H_Ψ
            H_psi, gamma_n = construct_H_psi(n_zeros=20)
            
            # Create detector
            detector = HorizonDetector(H_psi)
            
            # Perform full analysis
            structure = detector.analyze_horizon_structure()
            
            print(f"\nHorizon Structure Analysis:")
            print(f"  Number of horizons: {structure['n_horizons']}")
            print(f"  Min spectral gap: {structure['min_gap']:.4f}")
            print(f"  Max spectral gap: {structure['max_gap']:.4f}")
            print(f"  Mean spectral gap: {structure['mean_gap']:.4f}")
            
            # All should be reasonable
            assert structure['n_horizons'] == 20
            assert structure['min_gap'] > 0, "Spectral gaps should be positive"
            assert structure['max_gap'] > structure['min_gap']
            
        except FileNotFoundError:
            pytest.skip("Riemann zeros data file not found")


class TestConvenienceFunctions:
    """Test convenience functions."""
    
    def test_detect_horizons_from_operator(self):
        """Test convenience function for horizon detection."""
        H = np.diag([1.0, 2.0, 3.0])
        horizons = detect_horizons_from_operator(H)
        
        assert len(horizons) == 3
        assert np.allclose(horizons, [1.0, 2.0, 3.0])


if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])
