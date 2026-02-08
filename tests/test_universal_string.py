#!/usr/bin/env python3
"""
Tests for Universal String (La Cuerda Universal) Module

Tests the implementation of the critical line Re(s)=1/2 as a cosmic string
vibrating at f₀ = 141.7001 Hz.

Authors: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
"""

import pytest
import numpy as np
import mpmath as mp
from pathlib import Path
import sys
import json

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from utils.universal_string import UniversalString, load_riemann_zeros


class TestUniversalString:
    """Test suite for UniversalString class."""
    
    def test_initialization(self):
        """Test that UniversalString initializes correctly."""
        string = UniversalString()
        
        assert string.f0 == 141.7001
        assert string.delta_zeta == pytest.approx(0.2787437627, rel=1e-6)
        assert string.euclidean_diagonal == pytest.approx(141.421356237, rel=1e-6)
        assert string.upper_bound == 1.0
        assert string.lower_bound == -1.0
        assert string.coherence_C == 244.36
    
    def test_frequency_validation(self):
        """Test that f₀ = 100√2 + δζ is validated."""
        string = UniversalString()
        
        # Should pass validation
        assert string._validate_frequency_relation() == True
        
        # Check numerical precision
        expected = string.euclidean_diagonal + string.delta_zeta
        assert abs(string.f0 - expected) < 1e-6
    
    def test_frequency_relation_precision(self):
        """Test high-precision validation of f₀ = 100√2 + δζ."""
        mp.dps = 30
        
        # Compute with high precision
        sqrt2 = mp.sqrt(2)
        euclidean = 100 * sqrt2
        delta_zeta = mp.mpf('0.2787437627')
        expected_f0 = euclidean + delta_zeta
        
        # Should be 141.7001 exactly
        assert abs(float(expected_f0) - 141.7001) < 1e-9
    
    def test_fixed_endpoints(self):
        """Test that fixed endpoints are correctly defined."""
        string = UniversalString()
        
        # Upper bound
        assert string.upper_bound == 1.0
        
        # Lower bound
        assert string.lower_bound == -1.0
        
        # Validate ζ(-1) = -1/12
        mp.dps = 30
        zeta_minus_1 = float(mp.zeta(mp.mpc(-1, 0)).real)
        theoretical = -1.0 / 12.0
        
        assert abs(zeta_minus_1 - theoretical) < 1e-10
    
    def test_string_mode_computation(self):
        """Test computation of string vibrational modes."""
        string = UniversalString()
        
        # Use known zeros
        zeros = [14.134725, 21.022040, 25.010858]
        
        # Create height array
        t = np.linspace(0, 30, 100)
        
        # Compute mode at t=0
        amplitude = string.compute_string_mode(t, zeros, time=0.0)
        
        # Check output shape
        assert amplitude.shape == t.shape
        
        # Amplitude should be finite
        assert np.all(np.isfinite(amplitude))
        
        # At nodes (zeros), amplitude should be small
        for gamma in zeros:
            idx = np.argmin(np.abs(t - gamma))
            # Should be close to zero at node
            # (may not be exactly zero due to discretization)
            assert abs(amplitude[idx]) < 0.5
    
    def test_string_tension_calculation(self):
        """Test calculation of string tension properties."""
        string = UniversalString()
        
        # Use some test zeros
        zeros = [14.134725, 21.022040, 25.010858, 30.424876, 32.935062]
        
        tension = string.compute_string_tension(zeros)
        
        # Check all keys present
        required_keys = ['tension_ratio', 'energy_scale_hz2', 
                        'coherence_length', 'mode_density', 'num_modes']
        for key in required_keys:
            assert key in tension
        
        # Validate values
        assert tension['num_modes'] == len(zeros)
        assert tension['tension_ratio'] > 0
        assert tension['energy_scale_hz2'] > 0
        assert tension['coherence_length'] > 0
        assert tension['mode_density'] > 0
        
        # Check specific values
        expected_tension_ratio = (string.delta_zeta / string.f0) ** 2
        assert tension['tension_ratio'] == pytest.approx(expected_tension_ratio, rel=1e-6)
        
        expected_coherence = 1.0 / string.delta_zeta
        assert tension['coherence_length'] == pytest.approx(expected_coherence, rel=1e-6)
    
    def test_mathematical_certificate_generation(self):
        """Test generation of mathematical certificate."""
        string = UniversalString()
        
        zeros = [14.134725, 21.022040, 25.010858]
        
        cert = string.generate_mathematical_certificate(zeros)
        
        # Check structure
        assert 'certificate_type' in cert
        assert cert['certificate_type'] == 'UNIVERSAL_STRING_QCAL'
        
        assert 'frequency' in cert
        assert cert['frequency']['f0_hz'] == 141.7001
        assert cert['frequency']['relation_validated'] == True
        
        assert 'string_properties' in cert
        assert cert['string_properties']['upper_fixed_point'] == 1.0
        assert cert['string_properties']['lower_fixed_point'] == -1.0
        assert cert['string_properties']['lower_point_validation'] == True
        
        assert 'vibrational_modes' in cert
        assert cert['vibrational_modes']['num_nodes'] == len(zeros)
        
        assert 'zeros_as_nodes' in cert
        assert 'qcal_signature' in cert
        assert 'interpretation' in cert
    
    def test_certificate_serialization(self):
        """Test that certificate can be serialized to JSON."""
        string = UniversalString()
        zeros = [14.134725, 21.022040]
        
        cert = string.generate_mathematical_certificate(zeros)
        
        # Should be JSON-serializable
        try:
            json_str = json.dumps(cert)
            recovered = json.loads(json_str)
            
            assert recovered['certificate_type'] == cert['certificate_type']
            assert recovered['frequency']['f0_hz'] == cert['frequency']['f0_hz']
        except (TypeError, ValueError) as e:
            pytest.fail(f"Certificate not JSON-serializable: {e}")


class TestLoadRiemannZeros:
    """Test suite for loading Riemann zeros."""
    
    def test_load_nonexistent_file(self):
        """Test loading from nonexistent file."""
        zeros = load_riemann_zeros("nonexistent_file.txt")
        
        assert zeros == []
    
    def test_load_with_max_zeros(self, tmp_path):
        """Test loading with max_zeros limit."""
        # Create temporary file with test data
        test_file = tmp_path / "test_zeros.txt"
        
        with open(test_file, 'w') as f:
            for i in range(100):
                f.write(f"{10.0 + i}\n")
        
        # Load only first 20
        zeros = load_riemann_zeros(str(test_file), max_zeros=20)
        
        assert len(zeros) == 20
        assert zeros[0] == pytest.approx(10.0)
        assert zeros[19] == pytest.approx(29.0)
    
    def test_load_with_invalid_lines(self, tmp_path):
        """Test that invalid lines are skipped."""
        test_file = tmp_path / "test_zeros_invalid.txt"
        
        with open(test_file, 'w') as f:
            f.write("14.134725\n")
            f.write("invalid_line\n")
            f.write("21.022040\n")
            f.write("# comment\n")
            f.write("25.010858\n")
        
        zeros = load_riemann_zeros(str(test_file))
        
        # Should get 3 valid zeros
        assert len(zeros) == 3
        assert zeros[0] == pytest.approx(14.134725)
        assert zeros[1] == pytest.approx(21.022040)
        assert zeros[2] == pytest.approx(25.010858)


class TestPhysicalInterpretation:
    """Tests for physical interpretation aspects."""
    
    def test_frequency_correspondence(self):
        """Test correspondence between f₀ and first zero."""
        string = UniversalString()
        
        gamma_1 = 14.134725142  # First zero
        
        # f₀/γ₁ should be approximately 10 + δζ/10
        ratio = string.f0 / gamma_1
        expected = 10.0 + string.delta_zeta / 10.0
        
        assert ratio == pytest.approx(expected, rel=1e-6)
    
    def test_energy_scale(self):
        """Test characteristic energy scale."""
        string = UniversalString()
        
        energy = string.delta_zeta * string.f0
        
        # Should be approximately 39.5 Hz²
        assert energy == pytest.approx(39.5, rel=0.02)
    
    def test_coherence_length(self):
        """Test coherence length ℓ_c = 1/δζ."""
        string = UniversalString()
        
        coherence_length = 1.0 / string.delta_zeta
        
        # Should be approximately 3.59
        assert coherence_length == pytest.approx(3.59, rel=0.01)


class TestIntegration:
    """Integration tests with real zero data."""
    
    def test_with_synthetic_zeros(self):
        """Test complete workflow with synthetic zeros."""
        string = UniversalString()
        
        # First 10 known zeros
        zeros = [
            14.134725, 21.022040, 25.010858, 30.424876, 32.935062,
            37.586178, 40.918719, 43.327073, 48.005151, 49.773832
        ]
        
        # Should work without errors
        tension = string.compute_string_tension(zeros)
        assert tension['num_modes'] == 10
        
        cert = string.generate_mathematical_certificate(zeros)
        assert cert['vibrational_modes']['num_nodes'] == 10
    
    def test_certificate_qcal_signature(self):
        """Test that QCAL signature is present in certificate."""
        string = UniversalString()
        zeros = [14.134725]
        
        cert = string.generate_mathematical_certificate(zeros)
        
        assert 'qcal_signature' in cert
        sig = cert['qcal_signature']
        
        assert sig['coherence_C'] == 244.36
        assert sig['equation'] == 'Ψ = I × A_eff² × C^∞'
        assert 'José Manuel Mota Burruezo' in sig['author']
        assert sig['signature'] == '∴𓂀Ω∞³·CUERDA'


if __name__ == "__main__":
    # Run tests with pytest
    pytest.main([__file__, "-v", "--tb=short"])
