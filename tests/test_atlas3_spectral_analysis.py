"""
Test Suite for Atlas³ Spectral Analysis Module
==============================================

Tests for the Atlas³ non-Hermitian operator and spectral analysis framework.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
"""

import numpy as np
import pytest
import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from operators.Operator_Atlas3 import (
    OperatorAtlas3, 
    Atlas3Spectrum, 
    create_atlas3_operator
)
from atlas3_spectral_analysis import (
    Atlas3SpectralAnalyzer,
    SpectralStatistics,
    analyze_atlas3
)


class TestOperatorAtlas3:
    """Test suite for Atlas³ operator."""
    
    def test_operator_creation(self):
        """Test basic operator creation."""
        op = create_atlas3_operator(N=50, coupling_strength=0.1)
        
        assert op.N == 50
        assert op.coupling_strength == 0.1
        assert op.H is not None
        assert op.H.shape == (50, 50)
    
    def test_hamiltonian_properties(self):
        """Test Hamiltonian matrix properties."""
        op = create_atlas3_operator(N=30, coupling_strength=0.05)
        H = op.H
        
        # Should be complex
        assert H.dtype == complex or np.iscomplexobj(H)
        
        # Should be square
        assert H.shape[0] == H.shape[1]
        
        # Should not be Hermitian (non-Hermitian operator)
        hermitian_diff = np.max(np.abs(H - H.conj().T))
        assert hermitian_diff > 1e-10  # Should be non-Hermitian
    
    def test_spectrum_computation(self):
        """Test spectrum computation."""
        op = create_atlas3_operator(N=40, coupling_strength=0.05)
        spectrum = op.compute_spectrum()
        
        assert isinstance(spectrum, Atlas3Spectrum)
        assert len(spectrum.eigenvalues) == 40
        assert spectrum.eigenvectors.shape == (40, 40)
        assert hasattr(spectrum, 'is_pt_symmetric')
        assert hasattr(spectrum, 'real_part_mean')
        assert hasattr(spectrum, 'real_part_std')
    
    def test_pt_symmetry_detection(self):
        """Test PT-symmetry detection."""
        # Small coupling should maintain PT-symmetry
        op = create_atlas3_operator(N=30, coupling_strength=0.01)
        spectrum = op.compute_spectrum()
        
        # Check that most eigenvalues are real
        max_imag = np.max(np.abs(spectrum.eigenvalues.imag))
        
        # For small coupling, should be nearly PT-symmetric
        assert max_imag < 1.0  # Reasonable threshold
    
    def test_level_spacings(self):
        """Test level spacing computation."""
        op = create_atlas3_operator(N=50, coupling_strength=0.05)
        spectrum = op.compute_spectrum()
        spacings = op.get_level_spacings(spectrum)
        
        assert len(spacings) == 49  # N-1 spacings for N levels
        assert np.all(spacings >= 0)  # Spacings should be non-negative
        assert np.mean(spacings) > 0  # Mean spacing should be positive
    
    def test_spectral_rigidity(self):
        """Test spectral rigidity computation."""
        op = create_atlas3_operator(N=60, coupling_strength=0.05)
        spectrum = op.compute_spectrum()
        
        L_values, sigma_squared = op.compute_spectral_rigidity(spectrum)
        
        assert len(L_values) > 0
        assert len(sigma_squared) == len(L_values)
        assert np.all(L_values > 0)
        assert np.all(sigma_squared >= 0)


class TestAtlas3SpectralAnalyzer:
    """Test suite for spectral analyzer."""
    
    def test_analyzer_creation(self):
        """Test analyzer initialization."""
        analyzer = Atlas3SpectralAnalyzer(N=40, coupling_strength=0.05)
        
        assert analyzer.operator is not None
        assert analyzer.operator.N == 40
    
    def test_analyzer_with_operator(self):
        """Test analyzer with pre-configured operator."""
        op = create_atlas3_operator(N=35, coupling_strength=0.08)
        analyzer = Atlas3SpectralAnalyzer(operator=op)
        
        assert analyzer.operator == op
    
    def test_full_analysis(self):
        """Test complete spectral analysis."""
        analyzer = Atlas3SpectralAnalyzer(N=50, coupling_strength=0.05)
        stats = analyzer.compute_full_analysis()
        
        assert isinstance(stats, SpectralStatistics)
        assert hasattr(stats, 'critical_line_value')
        assert hasattr(stats, 'mean_real_part')
        assert hasattr(stats, 'alignment_score')
        assert hasattr(stats, 'wigner_dyson_fit')
        assert hasattr(stats, 'mean_spacing_ratio')
        assert hasattr(stats, 'rigidity_slope')
        assert hasattr(stats, 'is_pt_symmetric')
    
    def test_gue_statistics(self):
        """Test GUE statistics computation."""
        analyzer = Atlas3SpectralAnalyzer(N=60, coupling_strength=0.05)
        analyzer.spectrum = analyzer.operator.compute_spectrum()
        
        chi_squared, mean_r = analyzer._compute_gue_statistics()
        
        # Mean spacing ratio should be positive and < 1
        assert 0 < mean_r < 1
        # For GUE, should be near 0.5996
        assert 0.4 < mean_r < 0.8  # Reasonable range
    
    def test_rigidity_slope(self):
        """Test spectral rigidity slope computation."""
        analyzer = Atlas3SpectralAnalyzer(N=70, coupling_strength=0.05)
        analyzer.spectrum = analyzer.operator.compute_spectrum()
        
        slope, intercept = analyzer._compute_rigidity_slope()
        
        # Slope should be positive for rigidity
        assert slope >= 0
        # For GUE, should be near 1.0
        assert 0.3 < slope < 2.0  # Reasonable range
    
    def test_visualization_generation(self):
        """Test that visualization doesn't crash."""
        analyzer = Atlas3SpectralAnalyzer(N=40, coupling_strength=0.05)
        
        # Should not raise exception
        fig = analyzer.plot_panel_de_la_verdad(save_path=None)
        
        assert fig is not None
        # Clean up
        import matplotlib.pyplot as plt
        plt.close(fig)
    
    def test_summary_print(self):
        """Test summary printing."""
        analyzer = Atlas3SpectralAnalyzer(N=40, coupling_strength=0.05)
        
        # Should not raise exception
        analyzer.print_summary()


class TestIntegration:
    """Integration tests for complete workflow."""
    
    def test_complete_pipeline(self):
        """Test complete analysis pipeline."""
        # Use smaller system for faster test
        stats, fig = analyze_atlas3(
            N=40,
            coupling_strength=0.05,
            show_plot=False,
            save_path=None
        )
        
        assert isinstance(stats, SpectralStatistics)
        assert fig is not None
        
        # Clean up
        import matplotlib.pyplot as plt
        plt.close(fig)
    
    def test_different_couplings(self):
        """Test with different coupling strengths."""
        couplings = [0.01, 0.05, 0.1]
        
        for gamma in couplings:
            op = create_atlas3_operator(N=30, coupling_strength=gamma)
            spectrum = op.compute_spectrum()
            
            assert len(spectrum.eigenvalues) == 30
            assert spectrum.real_part_mean > 0
    
    def test_different_sizes(self):
        """Test with different system sizes."""
        sizes = [20, 40, 60]
        
        for N in sizes:
            op = create_atlas3_operator(N=N, coupling_strength=0.05)
            spectrum = op.compute_spectrum()
            
            assert len(spectrum.eigenvalues) == N


class TestNumericalStability:
    """Test numerical stability and edge cases."""
    
    def test_small_system(self):
        """Test with small system size."""
        op = create_atlas3_operator(N=10, coupling_strength=0.05)
        spectrum = op.compute_spectrum()
        
        assert len(spectrum.eigenvalues) == 10
        assert not np.any(np.isnan(spectrum.eigenvalues))
    
    def test_large_system(self):
        """Test with larger system size."""
        op = create_atlas3_operator(N=150, coupling_strength=0.05)
        spectrum = op.compute_spectrum()
        
        assert len(spectrum.eigenvalues) == 150
        assert not np.any(np.isnan(spectrum.eigenvalues))
    
    def test_zero_coupling(self):
        """Test with zero coupling (Hermitian limit)."""
        op = create_atlas3_operator(N=30, coupling_strength=0.0)
        spectrum = op.compute_spectrum()
        
        # Should be nearly PT-symmetric
        max_imag = np.max(np.abs(spectrum.eigenvalues.imag))
        assert max_imag < 1e-6  # Should be essentially real
    
    def test_no_nan_or_inf(self):
        """Test that computations don't produce NaN or Inf."""
        analyzer = Atlas3SpectralAnalyzer(N=50, coupling_strength=0.05)
        stats = analyzer.compute_full_analysis()
        
        # Check all statistics are finite
        assert np.isfinite(stats.mean_real_part)
        assert np.isfinite(stats.std_real_part)
        assert np.isfinite(stats.alignment_score)
        assert np.isfinite(stats.mean_spacing_ratio)
        assert np.isfinite(stats.rigidity_slope)


def test_qcal_constants():
    """Test that QCAL constants are properly defined."""
    from atlas3_spectral_analysis import F0, C_QCAL
    
    assert F0 == 141.7001
    assert C_QCAL == 244.36


def test_signature():
    """Test that Noēsis ∞³ signature is present."""
    import atlas3_spectral_analysis
    
    # Check module docstring contains signature
    assert 'Noēsis ∞³' in atlas3_spectral_analysis.__doc__


if __name__ == "__main__":
    pytest.main([__file__, '-v'])
