"""
Test Suite for Mathesis Universalis Framework
==============================================

Tests for the three-front arithmetic measurement program:
1. Explicit Sum Analyzer (prime signal correlation)
2. Spectral Determinant Regularization
3. Mathesis Universalis integration

Author: José Manuel Mota Burruezo Ψ✧ ∞³
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add repo root to path
REPO_ROOT = Path(__file__).parent.parent
sys.path.insert(0, str(REPO_ROOT))

from utils.explicit_sum_analyzer import (
    ExplicitSumAnalyzer,
    generate_primes,
    PrimeSignal
)
from operators.spectral_determinant_regularization import (
    SpectralDeterminantRegularizer,
    SpectralZetaResult,
    HeatKernelTrace
)
from core.mathesis_universalis import (
    MathesisUniversalis,
    MathesisUniversalisReport
)


class TestExplicitSumAnalyzer:
    """Tests for explicit sum and prime signal analysis."""
    
    def test_generate_primes(self):
        """Test prime number generation."""
        primes = generate_primes(30)
        expected = np.array([2, 3, 5, 7, 11, 13, 17, 19, 23, 29])
        np.testing.assert_array_equal(primes, expected)
    
    def test_generate_primes_empty(self):
        """Test empty case."""
        primes = generate_primes(1)
        assert len(primes) == 0
    
    def test_analyzer_initialization(self):
        """Test analyzer initialization."""
        analyzer = ExplicitSumAnalyzer(t_max=50.0, dt=0.1)
        assert analyzer.t_max == 50.0
        assert analyzer.dt == 0.1
        assert analyzer.n_points == 500
        assert len(analyzer.t_grid) == 500
    
    def test_prime_signal_generation(self):
        """Test synthetic prime signal generation."""
        analyzer = ExplicitSumAnalyzer(t_max=20.0, dt=0.05)
        signal = analyzer.generate_prime_signal(p_max=10)
        
        assert isinstance(signal, PrimeSignal)
        assert len(signal.t_values) == analyzer.n_points
        assert len(signal.signal) == analyzer.n_points
        assert signal.n_components > 0
        
        # Check that signal has peaks at ln(p) positions
        primes_to_check = [2, 3, 5, 7]
        for p in primes_to_check:
            ln_p = np.log(p)
            if ln_p < 20.0:
                # Find closest grid point
                idx = np.argmin(np.abs(signal.t_values - ln_p))
                # Should have non-zero amplitude
                assert signal.signal[idx] > 0
    
    def test_spectrum_to_density(self):
        """Test conversion of discrete spectrum to density."""
        analyzer = ExplicitSumAnalyzer(t_max=30.0, dt=0.1)
        
        # Create simple spectrum
        spectrum = np.array([1.0, 5.0, 10.0, 15.0, 20.0])
        t_vals, density = analyzer.spectrum_to_density(spectrum)
        
        assert len(t_vals) == len(analyzer.t_grid)
        assert len(density) == len(analyzer.t_grid)
        assert np.all(density >= 0)  # Density should be non-negative
        
        # Integral should be approximately number of eigenvalues
        integral = np.trapezoid(density, t_vals)
        assert 0.5 < integral < 2 * len(spectrum)
    
    def test_cross_correlation(self):
        """Test cross-correlation between spectrum and prime signal."""
        np.random.seed(42)
        analyzer = ExplicitSumAnalyzer(t_max=30.0, dt=0.05)
        
        # Generate spectrum with some structure at prime positions
        n_eigs = 50
        spectrum = np.cumsum(1.5 + 0.3 * np.random.randn(n_eigs))
        spectrum = spectrum[spectrum < 30.0]
        
        # Generate prime signal
        prime_signal = analyzer.generate_prime_signal()
        
        # Cross-correlate
        result = analyzer.cross_correlate(spectrum, prime_signal)
        
        assert len(result.correlation) > 0
        assert len(result.lags) == len(result.correlation)
        assert len(result.expected_peaks) > 0
        assert 0.0 <= result.detection_rate <= 1.0
        assert 0.0 <= result.significance <= 1.0
    
    def test_fourier_peak_detection(self):
        """Test Fourier analysis for ln(p) peaks."""
        np.random.seed(42)
        analyzer = ExplicitSumAnalyzer(t_max=30.0, dt=0.05)
        
        # Generate random spectrum
        spectrum = np.sort(np.random.uniform(0, 30, 50))
        
        # Fourier analysis
        result = analyzer.fourier_peak_detection(spectrum)
        
        assert 'frequencies' in result
        assert 'power_spectrum' in result
        assert 'peak_frequencies' in result
        assert 'total_power' in result
        assert result['total_power'] > 0
        assert 0.0 <= result['peak_fraction'] <= 1.0
    
    def test_validate_prime_memory(self):
        """Test prime memory validation."""
        np.random.seed(42)
        analyzer = ExplicitSumAnalyzer(t_max=30.0, dt=0.05)
        
        # Generate spectrum
        spectrum = np.sort(np.random.uniform(0, 30, 80))
        
        # Validate
        is_valid, report = analyzer.validate_prime_memory(
            spectrum,
            min_detection_rate=0.1,
            max_p_value=0.5
        )
        
        assert isinstance(is_valid, bool)
        assert 'detection_rate' in report
        assert 'p_value' in report
        assert 'conclusion' in report
        assert 0.0 <= report['detection_rate'] <= 1.0


class TestSpectralDeterminantRegularizer:
    """Tests for spectral determinant regularization."""
    
    def test_regularizer_initialization(self):
        """Test regularizer initialization."""
        reg = SpectralDeterminantRegularizer(
            precision=15,
            truncation_rank=100
        )
        assert reg.precision == 15
        assert reg.truncation_rank == 100
    
    def test_spectral_zeta_direct(self):
        """Test direct spectral zeta computation."""
        reg = SpectralDeterminantRegularizer()
        
        # Simple spectrum
        eigenvalues = np.array([1.0, 2.0, 3.0, 4.0, 5.0])
        
        result = reg.compute_spectral_zeta(eigenvalues, method="direct")
        
        assert isinstance(result, SpectralZetaResult)
        assert len(result.s_values) > 0
        assert len(result.zeta_values) == len(result.s_values)
        assert np.isfinite(result.zeta_prime_0)
        assert np.isfinite(result.log_determinant)
    
    def test_heat_kernel_trace(self):
        """Test heat kernel trace computation."""
        reg = SpectralDeterminantRegularizer()
        
        eigenvalues = np.array([1.0, 2.0, 3.0, 4.0, 5.0, 6.0])
        
        result = reg.compute_heat_kernel_trace(eigenvalues)
        
        assert isinstance(result, HeatKernelTrace)
        assert len(result.t_values) > 0
        assert len(result.trace_values) == len(result.t_values)
        assert np.all(result.trace_values > 0)  # Trace should be positive
        
        # Heat kernel should decay
        assert result.trace_values[0] > result.trace_values[-1]
    
    def test_berry_phase_computation(self):
        """Test Berry phase calculation."""
        reg = SpectralDeterminantRegularizer()
        
        # Parameter-dependent spectrum
        n_params = 20
        param_values = np.linspace(0, 2*np.pi, n_params)
        eigenvalues = np.ones((n_params, 5))  # Constant for simplicity
        
        result = reg.compute_berry_phase(eigenvalues, param_values)
        
        assert len(result.t_values) == n_params
        assert len(result.phase_values) == n_params
        assert len(result.phase_derivative) == n_params
        assert len(result.geometric_interpretation) > 0
    
    def test_pt_symmetry_verification(self):
        """Test PT symmetry verification."""
        reg = SpectralDeterminantRegularizer()
        
        # Real eigenvalues (PT symmetric)
        real_eigs = np.array([1.0, 2.0, 3.0, 4.0, 5.0])
        result_real = reg.verify_pt_symmetry(real_eigs)
        
        assert result_real['is_pt_symmetric'] is True
        assert result_real['max_imaginary'] < 1e-10
        
        # Complex eigenvalues (PT broken)
        complex_eigs = np.array([1+0.1j, 2+0.05j, 3-0.1j])
        result_complex = reg.verify_pt_symmetry(complex_eigs, tolerance=1e-6)
        
        assert result_complex['is_pt_symmetric'] is False
        assert result_complex['max_imaginary'] > 1e-6
    
    def test_xi_function_connection(self):
        """Test connection to Riemann xi function."""
        reg = SpectralDeterminantRegularizer()
        
        eigenvalues = np.array([1.0, 2.0, 3.0, 4.0, 5.0])
        t_values = np.linspace(0, 5, 10)
        
        result = reg.connect_to_xi_function(eigenvalues, t_values)
        
        assert 't_values' in result
        assert 'xi_determinant' in result
        assert 'berry_phase' in result
        assert 'pt_symmetric' in result
        assert len(result['xi_determinant']) == len(t_values)


class TestMathesisUniversalis:
    """Tests for integrated Mathesis Universalis framework."""
    
    def test_framework_initialization(self):
        """Test framework initialization."""
        framework = MathesisUniversalis(
            t_max=50.0,
            dt=0.1,
            truncation_rank=100
        )
        
        assert framework.explicit_sum_analyzer is not None
        assert framework.spectral_regularizer is not None
        assert framework.output_dir.exists()
    
    def test_analyze_spectrum_basic(self):
        """Test basic spectrum analysis."""
        np.random.seed(42)
        framework = MathesisUniversalis(
            t_max=30.0,
            dt=0.1,
            truncation_rank=50
        )
        
        # Generate test spectrum
        n_eigs = 50
        eigenvalues = np.sort(np.random.uniform(0.1, 30, n_eigs))
        
        # Analyze
        report = framework.analyze_spectrum(eigenvalues, label="test_spectrum")
        
        assert isinstance(report, MathesisUniversalisReport)
        assert report.spectrum_size == len(eigenvalues)
        assert 0.0 <= report.mathesis_score <= 1.0
        assert isinstance(report.is_arithmetic_instrument, bool)
        assert len(report.conclusion) > 0
    
    def test_report_structure(self):
        """Test report data structure."""
        np.random.seed(42)
        framework = MathesisUniversalis(t_max=20.0, dt=0.1)
        
        eigenvalues = np.sort(np.random.uniform(0.1, 20, 30))
        report = framework.analyze_spectrum(eigenvalues, label="test_report")
        
        # Check all required fields
        assert hasattr(report, 'timestamp')
        assert hasattr(report, 'spectrum_size')
        assert hasattr(report, 'heat_kernel_truncation_rank')
        assert hasattr(report, 'determinant_regularized')
        assert hasattr(report, 'log_determinant')
        assert hasattr(report, 'prime_memory_detected')
        assert hasattr(report, 'detection_rate')
        assert hasattr(report, 'pt_symmetric')
        assert hasattr(report, 'mathesis_score')
    
    def test_pt_symmetric_spectrum(self):
        """Test analysis of PT-symmetric (real) spectrum."""
        np.random.seed(42)
        framework = MathesisUniversalis(t_max=30.0, dt=0.1)
        
        # Real eigenvalues
        eigenvalues = np.sort(np.random.uniform(0.1, 30, 40))
        report = framework.analyze_spectrum(eigenvalues, label="pt_test")
        
        assert report.pt_symmetric is True
        assert report.critical_line_alignment is True
        assert report.max_imaginary_part < 1e-10
    
    def test_mathesis_score_components(self):
        """Test Mathesis score computation."""
        np.random.seed(42)
        framework = MathesisUniversalis(t_max=25.0, dt=0.1)
        
        eigenvalues = np.sort(np.random.uniform(0.1, 25, 35))
        report = framework.analyze_spectrum(eigenvalues, label="score_test")
        
        # Score should be average of three components
        # All components should be in [0, 1]
        assert 0.0 <= report.mathesis_score <= 1.0
        
        # With random data, arithmetic instrument not guaranteed
        assert isinstance(report.is_arithmetic_instrument, bool)


class TestIntegration:
    """Integration tests for complete workflow."""
    
    def test_full_workflow_gue_spectrum(self):
        """Test complete workflow with GUE-like spectrum."""
        np.random.seed(42)
        
        # Create framework
        framework = MathesisUniversalis(
            t_max=40.0,
            dt=0.05,
            truncation_rank=100
        )
        
        # Generate GUE-like spectrum
        n_eigs = 80
        spacing = 2.0
        eigenvalues = np.cumsum(spacing * (1 + 0.3 * np.random.randn(n_eigs)))
        eigenvalues = eigenvalues[eigenvalues > 0]
        
        # Full analysis
        report = framework.analyze_spectrum(eigenvalues, label="integration_test")
        
        # Verify all three fronts completed
        assert report.determinant_regularized is True
        assert report.heat_kernel_truncation_rank > 0
        assert 0.0 <= report.detection_rate <= 1.0
        assert report.pt_symmetric is True
        
        # Report file should exist
        report_file = framework.output_dir / "integration_test_report.json"
        assert report_file.exists()
    
    def test_deterministic_results(self):
        """Test that results are deterministic with fixed seed."""
        np.random.seed(123)
        
        framework = MathesisUniversalis(t_max=20.0, dt=0.1)
        eigenvalues = np.sort(np.random.uniform(0.1, 20, 30))
        
        report1 = framework.analyze_spectrum(eigenvalues, label="det_test1")
        
        # Same spectrum should give same results
        report2 = framework.analyze_spectrum(eigenvalues, label="det_test2")
        
        assert report1.mathesis_score == report2.mathesis_score
        assert report1.detection_rate == report2.detection_rate
        assert report1.log_determinant == report2.log_determinant


if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])
