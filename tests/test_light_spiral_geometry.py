"""
Test suite for Light Spiral Geometry Module

Tests the geometric framework where light follows logarithmic spiral paths
modulated by Riemann zeta zeros and prime numbers.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: February 2026

QCAL ∞³ Active · 141.7001 Hz · Ψ = I × A_eff² × C^∞
DOI: 10.5281/zenodo.17379721
"""

import pytest
import numpy as np
import sys
import os

# Import modules directly to avoid utils/__init__.py dependencies
sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(__file__)), 'utils'))

try:
    import light_spiral_geometry as lsg
    GEOMETRY_AVAILABLE = True
except ImportError:
    GEOMETRY_AVAILABLE = False
    pytest.skip("light_spiral_geometry module not available", allow_module_level=True)

try:
    import zeta_interference_pattern as zip_mod
    PATTERN_AVAILABLE = True
except ImportError:
    PATTERN_AVAILABLE = False


class TestPrimeUtilities:
    """Tests for prime number utilities"""
    
    def test_get_nth_prime_first_10(self):
        """Test that first 10 primes are correct"""
        expected_primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
        for i, expected in enumerate(expected_primes):
            assert lsg.get_nth_prime(i) == expected, f"Prime {i} should be {expected}"
    
    def test_get_nth_prime_monotonic(self):
        """Test that primes are strictly increasing"""
        primes = [lsg.get_nth_prime(i) for i in range(20)]
        for i in range(len(primes) - 1):
            assert primes[i] < primes[i+1], "Primes must be strictly increasing"
    
    def test_prime_phase_modulation_positive(self):
        """Test that phase modulation is positive and finite"""
        for p in [2, 3, 5, 7, 11, 13]:
            phase = lsg.prime_phase_modulation(p, mode='logarithmic')
            assert np.isfinite(phase), f"Phase for prime {p} must be finite"
            assert phase >= 0, f"Phase for prime {p} must be non-negative"
    
    def test_prime_phase_modulation_modes(self):
        """Test different phase modulation modes"""
        p = 7
        phase_log = lsg.prime_phase_modulation(p, mode='logarithmic')
        phase_mod = lsg.prime_phase_modulation(p, mode='modular')
        phase_zeta = lsg.prime_phase_modulation(p, mode='zeta')
        
        # All should be finite
        assert np.isfinite(phase_log)
        assert np.isfinite(phase_mod)
        assert np.isfinite(phase_zeta)
        
        # Should be different
        assert not (phase_log == phase_mod == phase_zeta)


class TestSpiralParameters:
    """Tests for SpiralParameters dataclass"""
    
    def test_default_initialization(self):
        """Test default parameter initialization"""
        params = lsg.SpiralParameters()
        
        assert params.r0 > 0, "Initial radius must be positive"
        assert np.isfinite(params.lambda_exp), "Expansion index must be finite"
        assert params.f0 == lsg.F0_HZ, "Base frequency must match f₀"
        assert params.prime_index >= 0, "Prime index must be non-negative"
    
    def test_custom_initialization(self):
        """Test custom parameter initialization"""
        params = lsg.SpiralParameters(
            r0=1e-9,
            lambda_exp=0.01,
            f0=141.7001,
            prime_index=2
        )
        
        assert params.r0 == 1e-9
        assert params.lambda_exp == 0.01
        assert params.f0 == 141.7001
        assert params.prime_index == 2
        assert params.prime == 5  # 3rd prime (0-indexed)
    
    def test_derived_parameters(self):
        """Test that derived parameters are computed correctly"""
        params = lsg.SpiralParameters(prime_index=1)
        
        # Verify omega_0 = 2π * f0
        expected_omega = 2 * np.pi * params.f0
        assert abs(params.omega_0 - expected_omega) < 1e-10
        
        # Verify phi_p is computed
        assert np.isfinite(params.phi_p)


class TestSpiralPathComputation:
    """Tests for spiral path computation functions"""
    
    def test_compute_spiral_path_shape(self):
        """Test that spiral path has correct shape"""
        t = np.linspace(0, 1e-6, 100)  # Short time span
        params = lsg.SpiralParameters()
        
        x, y, z = lsg.compute_spiral_path(t, params)
        
        assert x.shape == t.shape
        assert y.shape == t.shape
        assert z.shape == t.shape
    
    def test_compute_spiral_path_continuity(self):
        """Test that spiral path is continuous (no NaNs or Infs)"""
        t = np.linspace(0, 1e-6, 100)
        params = lsg.SpiralParameters()
        
        x, y, z = lsg.compute_spiral_path(t, params)
        
        assert np.all(np.isfinite(x))
        assert np.all(np.isfinite(y))
        assert np.all(np.isfinite(z))
    
    def test_spiral_radial_expansion(self):
        """Test that spiral radius expands correctly"""
        t = np.linspace(0, 1e-6, 100)
        params = lsg.SpiralParameters(lambda_exp=0.01)
        
        x, y, z = lsg.compute_spiral_path(t, params)
        r = np.sqrt(x**2 + y**2)
        
        # For positive lambda, radius should increase
        assert np.all(np.diff(r) >= 0), "Radius should monotonically increase"
    
    def test_spiral_z_propagation(self):
        """Test that z propagates at speed of light"""
        t = np.linspace(0, 1e-6, 100)
        params = lsg.SpiralParameters()
        
        x, y, z = lsg.compute_spiral_path(t, params)
        
        # z should equal c*t
        expected_z = lsg.C_LIGHT * t
        assert np.allclose(z, expected_z, rtol=1e-10)
    
    def test_logarithmic_spiral_property(self):
        """Test logarithmic spiral property: r = r₀·exp(λt)"""
        t = np.linspace(0, 1e-6, 100)
        params = lsg.SpiralParameters(r0=1e-9, lambda_exp=0.01)
        
        x, y, z = lsg.compute_spiral_path(t, params)
        r = np.sqrt(x**2 + y**2)
        
        expected_r = params.r0 * np.exp(params.lambda_exp * t)
        assert np.allclose(r, expected_r, rtol=1e-10)


class TestZetaModulatedSpiral:
    """Tests for zeta-modulated spiral paths"""
    
    @pytest.mark.skipif(not lsg.SPECTRUM_AVAILABLE, reason="infinite_spectrum not available")
    def test_zeta_modulation_shape(self):
        """Test that zeta-modulated path has correct shape"""
        t = np.linspace(0, 1e-6, 100)
        params = lsg.SpiralParameters()
        
        x, y, z = lsg.compute_spiral_path_zeta_modulated(t, params, n_zeros=5)
        
        assert x.shape == t.shape
        assert y.shape == t.shape
        assert z.shape == t.shape
    
    def test_zeta_modulation_differs_from_basic(self):
        """Test that zeta modulation changes the path"""
        t = np.linspace(0, 1e-5, 100)  # Longer time for more modulation
        params = lsg.SpiralParameters(lambda_exp=0.1)  # Larger expansion
        
        x_basic, y_basic, z_basic = lsg.compute_spiral_path(t, params)
        x_zeta, y_zeta, z_zeta = lsg.compute_spiral_path_zeta_modulated(t, params, n_zeros=10)
        
        # Check that modulation introduces some difference
        # The difference should be small but non-zero
        x_diff = np.max(np.abs(x_basic - x_zeta))
        y_diff = np.max(np.abs(y_basic - y_zeta))
        
        # At least one coordinate should show modulation
        # (may be very small without actual zeta zeros loaded)
        has_modulation = (x_diff > 0) or (y_diff > 0)
        assert has_modulation, "Zeta modulation should produce some path difference"


class TestFrequencyMapping:
    """Tests for spectral frequency mapping"""
    
    def test_spectral_frequency_positive(self):
        """Test that all mapped frequencies are positive"""
        for n in range(10):
            f_n = lsg.spectral_frequency_mapping(n)
            assert f_n > 0, f"Frequency for zero {n} must be positive"
            assert np.isfinite(f_n), f"Frequency for zero {n} must be finite"
    
    def test_spectral_frequency_increasing(self):
        """Test that frequencies increase with zero index"""
        frequencies = [lsg.spectral_frequency_mapping(n) for n in range(10)]
        
        for i in range(len(frequencies) - 1):
            assert frequencies[i] < frequencies[i+1], \
                f"Frequency must increase: f{i} < f{i+1}"
    
    def test_first_frequency_relates_to_f0(self):
        """Test that first frequency relates to base frequency"""
        f_0 = lsg.spectral_frequency_mapping(0)
        
        # Should be of same order of magnitude as f₀
        assert f_0 / lsg.F0_HZ < 100, "First frequency should be comparable to f₀"


class TestInterferometryPredictions:
    """Tests for experimental prediction functions"""
    
    def test_interferometry_prediction_structure(self):
        """Test that interferometry prediction returns correct structure"""
        pred = lsg.predict_interferometry_deviation()
        
        required_keys = ['phase_shift', 'phase_shift_cycles', 'frequency_modulation',
                        'measurability', 'confidence', 'recommended_technique']
        
        for key in required_keys:
            assert key in pred, f"Prediction must contain '{key}'"
    
    def test_interferometry_prediction_physical(self):
        """Test that interferometry predictions are physical"""
        pred = lsg.predict_interferometry_deviation()
        
        assert pred['phase_shift'] >= 0, "Phase shift must be non-negative"
        assert np.isfinite(pred['phase_shift'])
        assert pred['frequency_modulation'] >= 0
        assert np.isfinite(pred['frequency_modulation'])
    
    def test_cavity_resonance_structure(self):
        """Test that cavity resonance prediction returns correct structure"""
        pred = lsg.cavity_resonance_prediction()
        
        required_keys = ['free_spectral_range', 'linewidth', 'nearest_mode',
                        'resonant_frequency', 'f0_deviation', 'modulation_depth']
        
        for key in required_keys:
            assert key in pred, f"Prediction must contain '{key}'"
    
    def test_cavity_resonance_physical(self):
        """Test that cavity predictions are physical"""
        pred = lsg.cavity_resonance_prediction()
        
        assert pred['free_spectral_range'] > 0
        assert pred['linewidth'] > 0
        assert pred['linewidth'] < pred['free_spectral_range']
        assert 0 < pred['modulation_depth'] < 1


@pytest.mark.skipif(not PATTERN_AVAILABLE, reason="zeta_interference_pattern not available")
class TestInterferencePatterns:
    """Tests for interference pattern computation"""
    
    def test_wave_function_parameters_initialization(self):
        """Test WaveFunctionParameters initialization"""
        params = zip_mod.WaveFunctionParameters()
        
        assert params.n_primes > 0
        assert params.n_zeros > 0
        assert params.f0 == zip_mod.F0_HZ
        assert params.wavelength > 0
    
    def test_interference_pattern_shape(self):
        """Test that interference pattern has correct shape"""
        x = np.linspace(-1e-3, 1e-3, 50)
        y = np.linspace(-1e-3, 1e-3, 50)
        X, Y = np.meshgrid(x, y)
        
        params = zip_mod.WaveFunctionParameters(n_primes=3, n_zeros=3)
        intensity = zip_mod.compute_interference_pattern(X, Y, 0.0, params)
        
        assert intensity.shape == X.shape
        assert intensity.shape == Y.shape
    
    def test_interference_pattern_physical(self):
        """Test that interference pattern is physical"""
        x = np.linspace(-1e-3, 1e-3, 50)
        y = np.linspace(-1e-3, 1e-3, 50)
        X, Y = np.meshgrid(x, y)
        
        params = zip_mod.WaveFunctionParameters(n_primes=3, n_zeros=3)
        intensity = zip_mod.compute_interference_pattern(X, Y, 0.0, params)
        
        # Intensity must be real and non-negative
        assert np.all(intensity >= 0), "Intensity must be non-negative"
        assert np.all(np.isreal(intensity)), "Intensity must be real"
        assert np.all(np.isfinite(intensity)), "Intensity must be finite"
    
    def test_spiral_arc_detection(self):
        """Test spiral arc detection algorithm"""
        x = np.linspace(-1e-3, 1e-3, 100)
        y = np.linspace(-1e-3, 1e-3, 100)
        X, Y = np.meshgrid(x, y)
        
        params = zip_mod.WaveFunctionParameters(n_primes=5, n_zeros=5)
        intensity = zip_mod.compute_interference_pattern(X, Y, 0.0, params)
        
        spiral_info = zip_mod.detect_spiral_arcs(intensity, X, Y, threshold=0.5)
        
        # Should return a dictionary with detection results
        assert isinstance(spiral_info, dict)
        assert 'spiral_detected' in spiral_info


class TestCoherenceAtF0:
    """Tests for coherence at fundamental frequency f₀"""
    
    def test_f0_constant_value(self):
        """Test that f₀ equals 141.7001 Hz"""
        assert abs(lsg.F0_HZ - 141.7001) < 1e-10, \
            "f₀ must equal 141.7001 Hz (QCAL fundamental frequency)"
    
    def test_spiral_rotations_at_f0(self):
        """Test correct number of rotations at f₀"""
        # 10 periods
        T = 1.0 / lsg.F0_HZ
        t = np.linspace(0, 10 * T, 1000)
        
        params = lsg.SpiralParameters(prime_index=0)
        x, y, z = lsg.compute_spiral_path(t, params)
        
        # Count rotations by unwrapping angle
        angle = np.arctan2(y, x)
        angle_unwrapped = np.unwrap(angle)
        total_rotations = (angle_unwrapped[-1] - angle_unwrapped[0]) / (2 * np.pi)
        
        # Should be approximately 10 rotations
        assert abs(total_rotations - 10) < 0.1, \
            f"Expected 10 rotations, got {total_rotations}"


class TestModuleInfo:
    """Tests for module information and metadata"""
    
    def test_module_info_structure(self):
        """Test that module info returns correct structure"""
        info = lsg.get_module_info()
        
        required_keys = ['module', 'version', 'date', 'author',
                        'institution', 'doi', 'frequency', 'signature']
        
        for key in required_keys:
            assert key in info, f"Module info must contain '{key}'"
    
    def test_module_info_values(self):
        """Test that module info has correct values"""
        info = lsg.get_module_info()
        
        assert info['frequency'] == lsg.F0_HZ
        assert 'QCAL' in info['signature'] or 'LSG' in info['signature']
        assert '10.5281/zenodo' in info['doi']


if __name__ == '__main__':
    # Run tests with pytest
    pytest.main([__file__, '-v'])
