#!/usr/bin/env python3
"""
Unit Tests for Reloj Compton Module

This module contains pytest unit tests for reloj_compton.py, validating:
- Compton frequency calculations for fundamental particles
- Cosmic scale factor derivation
- Master equation computation
- Error handling and edge cases
- Integration with QCAL framework

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
QCAL ∞³ Framework
"""

import pytest
import sys
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from reloj_compton import ComptonClock


class TestComptonClock:
    """Test suite for ComptonClock class."""
    
    @pytest.fixture
    def clock_standard(self):
        """Create ComptonClock instance with standard precision."""
        return ComptonClock(precision=50)
    
    @pytest.fixture
    def clock_high_precision(self):
        """Create ComptonClock instance with high precision."""
        return ComptonClock(precision=100)
    
    def test_initialization_standard(self, clock_standard):
        """Test standard initialization of ComptonClock."""
        assert clock_standard.precision == 50
        assert float(clock_standard.f0_theoretical) == 141.7001
        
    def test_initialization_high_precision(self, clock_high_precision):
        """Test high-precision initialization of ComptonClock."""
        assert clock_high_precision.precision == 100
        assert float(clock_high_precision.f0_theoretical) == 141.7001
    
    def test_electron_compton_frequency(self, clock_standard):
        """Test electron Compton frequency calculation."""
        result = clock_standard.compute_compton_frequency(
            clock_standard.m_e, "e⁻"
        )
        
        # Expected: ~1.235590e20 Hz
        assert result["particle"] == "e⁻"
        assert abs(result["frequency_Hz"] - 1.235590e20) / 1.235590e20 < 0.001
        assert result["mass_kg"] > 0
        assert result["wavelength_m"] > 0
        
    def test_proton_compton_frequency(self, clock_standard):
        """Test proton Compton frequency calculation."""
        result = clock_standard.compute_compton_frequency(
            clock_standard.m_p, "p"
        )
        
        # Expected: ~2.268732e23 Hz
        assert result["particle"] == "p"
        assert abs(result["frequency_Hz"] - 2.268732e23) / 2.268732e23 < 0.001
        
    def test_planck_compton_frequency(self, clock_standard):
        """Test Planck mass Compton frequency calculation."""
        result = clock_standard.compute_compton_frequency(
            clock_standard.m_P, "m_P"
        )
        
        # Expected: ~2.952099e42 Hz
        assert result["particle"] == "m_P"
        assert abs(result["frequency_Hz"] - 2.952099e42) / 2.952099e42 < 0.001
    
    def test_analyze_all_particles(self, clock_standard):
        """Test analysis of all fundamental particles."""
        analysis = clock_standard.analyze_particle_compton_frequencies()
        
        # Check all particles present
        assert "electron" in analysis
        assert "proton" in analysis
        assert "neutron" in analysis
        assert "planck" in analysis
        assert "mass_ratios" in analysis
        
        # Check mass ratios
        ratios = analysis["mass_ratios"]
        assert ratios["m_p/m_e"] > 1800  # ~1836
        assert ratios["m_P/m_e"] > 1e22  # ~2.389e22
    
    def test_cosmic_scale_factor(self, clock_standard):
        """Test cosmic scale factor K derivation."""
        scale_factor = clock_standard.derive_cosmic_scale_factor()
        
        # Expected: K ≈ 2.44e8
        K = scale_factor["K"]
        assert abs(K - 2.44e8) / 2.44e8 < 0.01  # Within 1%
        
        # Check components
        assert scale_factor["phi"] > 1.6  # φ ≈ 1.618
        assert scale_factor["phi_cubed"] > 4.0  # φ³ ≈ 4.236
        assert scale_factor["mass_ratio_m_P_over_m_e"] > 1e22
        
    def test_fundamental_frequency_calculation(self, clock_standard):
        """Test fundamental frequency f₀ calculation."""
        results = clock_standard.compute_fundamental_frequency(verbose=False)
        
        # Check calculated frequency
        f0_calc = results["f0_calculated_Hz"]
        assert abs(f0_calc - 141.5459) < 0.001  # Within 0.001 Hz
        
        # Check error is within tolerance
        error = results["error_percent"]
        assert error < 1.0  # Less than 1% error
        assert abs(error - 0.1088) < 0.001  # Close to expected 0.1088%
        
        # Check validation status
        assert results["validation_status"] == "PASSED"
    
    def test_master_equation_components(self, clock_standard):
        """Test individual master equation components."""
        results = clock_standard.compute_fundamental_frequency(verbose=False)
        comp = results["master_equation_components"]
        
        # All components should be positive
        assert comp["c_over_2pi_m_per_s"] > 0
        assert comp["sqrt_mass_ratio"] > 0
        assert comp["alpha"] > 0
        assert comp["phi"] > 0
        assert comp["length_ratio_l_P_over_lambda_C"] > 0
        assert comp["K_cosmic_scale_factor"] > 0
        
        # Check specific values
        assert abs(comp["alpha"] - 0.00729735) < 0.0001  # Fine structure constant
        assert abs(comp["phi"] - 1.618034) < 0.0001  # Golden ratio
    
    def test_high_precision_calculation(self, clock_high_precision):
        """Test that high precision calculation works correctly."""
        results = clock_high_precision.compute_fundamental_frequency(verbose=False)
        
        f0_calc = results["f0_calculated_Hz"]
        error = results["error_percent"]
        
        # Should still match expected values
        assert abs(f0_calc - 141.5459) < 0.001
        assert error < 1.0
        assert results["validation_status"] == "PASSED"
    
    def test_complete_analysis(self, clock_standard):
        """Test complete analysis workflow."""
        results = clock_standard.run_complete_analysis(
            verbose=False,
            save_results=False
        )
        
        # Check all required sections present
        assert "title" in results
        assert "frequency_fundamental_Hz" in results
        assert "compton_frequencies" in results
        assert "cosmic_scale_factor" in results
        assert "master_equation" in results
        assert "validation_status" in results
        
        # Check validation
        assert results["validation_status"] == "PASSED"
        assert results["error_percent"] < 1.0
    
    def test_qcal_integration(self, clock_standard):
        """Test integration with QCAL framework constants."""
        results = clock_standard.compute_fundamental_frequency(verbose=False)
        
        # Theoretical frequency should match .qcal_beacon
        assert results["f0_theoretical_Hz"] == 141.7001
        
        # Calculated frequency should be close
        f0_calc = results["f0_calculated_Hz"]
        assert abs(f0_calc - 141.7001) < 1.0  # Within 1 Hz
    
    def test_physical_constants_consistency(self, clock_standard):
        """Test that physical constants are consistent."""
        # Speed of light
        assert abs(float(clock_standard.c) - 299792458) < 1
        
        # Planck constant (exact value since 2019)
        assert abs(float(clock_standard.h) - 6.62607015e-34) < 1e-42
        
        # Electron mass (CODATA 2018)
        assert abs(float(clock_standard.m_e) - 9.1093837015e-31) < 1e-40
        
        # Golden ratio
        phi_expected = (1 + 5**0.5) / 2
        assert abs(float(clock_standard.phi) - phi_expected) < 1e-10


class TestEdgeCases:
    """Test edge cases and error handling."""
    
    @pytest.fixture
    def clock_standard(self):
        """Create ComptonClock instance with standard precision."""
        return ComptonClock(precision=50)
    
    def test_low_precision(self):
        """Test with low precision."""
        clock = ComptonClock(precision=10)
        results = clock.compute_fundamental_frequency(verbose=False)
        
        # Should still work with lower precision
        assert results["validation_status"] == "PASSED"
    
    def test_very_high_precision(self):
        """Test with very high precision."""
        clock = ComptonClock(precision=200)
        results = clock.compute_fundamental_frequency(verbose=False)
        
        # Should work with very high precision
        assert results["validation_status"] == "PASSED"
    
    def test_compton_frequency_zero_mass(self, clock_standard):
        """Test Compton frequency with zero mass (should handle gracefully)."""
        # This should either raise an error or return infinity
        # Depending on implementation, adjust the assertion
        try:
            result = clock_standard.compute_compton_frequency(0.0, "zero")
            # If it doesn't raise an error, frequency should be 0 or inf
            assert result["frequency_Hz"] == 0 or result["frequency_Hz"] == float('inf')
        except (ZeroDivisionError, ValueError):
            # Expected behavior for zero mass
            pass


class TestResultFormats:
    """Test result formats and data structures."""
    
    @pytest.fixture
    def results(self):
        """Get standard results."""
        clock = ComptonClock(precision=50)
        return clock.compute_fundamental_frequency(verbose=False)
    
    def test_result_structure(self, results):
        """Test that result dictionary has correct structure."""
        required_keys = [
            "f0_calculated_Hz",
            "f0_theoretical_Hz",
            "error_absolute_Hz",
            "error_percent",
            "master_equation_components",
            "scale_factor_derivation",
            "validation_status",
            "precision_dps",
            "timestamp"
        ]
        
        for key in required_keys:
            assert key in results, f"Missing required key: {key}"
    
    def test_component_structure(self, results):
        """Test master equation components structure."""
        comp = results["master_equation_components"]
        
        required_comp_keys = [
            "c_over_2pi_m_per_s",
            "sqrt_mass_ratio",
            "alpha",
            "phi",
            "length_ratio_l_P_over_lambda_C",
            "K_cosmic_scale_factor"
        ]
        
        for key in required_comp_keys:
            assert key in comp, f"Missing component key: {key}"
    
    def test_numeric_types(self, results):
        """Test that numeric values are proper types."""
        assert isinstance(results["f0_calculated_Hz"], float)
        assert isinstance(results["error_percent"], float)
        assert isinstance(results["precision_dps"], int)
    
    def test_timestamp_format(self, results):
        """Test that timestamp is in ISO format."""
        timestamp = results["timestamp"]
        assert isinstance(timestamp, str)
        assert "T" in timestamp  # ISO format contains 'T'
        assert timestamp.endswith("Z")  # UTC indicator


# Parametrized tests for different precision levels
@pytest.mark.parametrize("precision", [25, 50, 100, 150])
def test_precision_levels(precision):
    """Test calculation works correctly at different precision levels."""
    clock = ComptonClock(precision=precision)
    results = clock.compute_fundamental_frequency(verbose=False)
    
    # All precision levels should pass validation
    assert results["validation_status"] == "PASSED"
    assert results["error_percent"] < 1.0


# Integration test
def test_end_to_end_workflow():
    """Test complete end-to-end workflow."""
    # Create clock
    clock = ComptonClock(precision=50)
    
    # Analyze particles
    compton = clock.analyze_particle_compton_frequencies()
    assert len(compton) >= 4  # At least 4 particles + mass_ratios
    
    # Derive scale factor
    scale = clock.derive_cosmic_scale_factor()
    assert scale["K"] > 0
    
    # Compute frequency
    freq = clock.compute_fundamental_frequency(verbose=False)
    assert freq["validation_status"] == "PASSED"
    
    # Run complete analysis
    full = clock.run_complete_analysis(verbose=False, save_results=False)
    assert full["validation_status"] == "PASSED"


if __name__ == "__main__":
    # Run tests with pytest
    pytest.main([__file__, "-v", "--tb=short"])
