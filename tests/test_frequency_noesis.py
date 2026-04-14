#!/usr/bin/env python3
"""
Tests for Frequency Harmonics and Noesis_Q Operator

This test suite validates the implementation of:
1. Frequency harmonic scaling (41.7 Hz → 888 Hz via φ⁴)
2. Noesis_Q operator computation
3. RAM-XX Singularity detection
4. GW250114 resonance validation

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
"""

import sys
from pathlib import Path
import json

# Add parent directory to path
sys.path.append(str(Path(__file__).parent))

import pytest

# Import modules to test
from frequency_harmonics import FrequencyHarmonics
from noesis_q_operator import NoesisQOperator


class TestFrequencyHarmonics:
    """Test suite for frequency harmonic scaling."""
    
    def test_golden_ratio_value(self):
        """Test that φ is correctly computed."""
        harmonics = FrequencyHarmonics(precision=50)
        phi_value = float(harmonics.phi) if hasattr(harmonics.phi, '__float__') else harmonics.phi
        
        # φ ≈ 1.618033988749895
        assert abs(phi_value - 1.618033988749895) < 1e-10, \
            f"Golden ratio φ = {phi_value}, expected ≈ 1.618"
    
    def test_phi_fourth_power(self):
        """Test that φ⁴ is in expected range."""
        harmonics = FrequencyHarmonics(precision=50)
        phi_powers = harmonics.compute_phi_powers()
        
        phi4 = phi_powers["phi_4"]
        # φ⁴ ≈ 6.854101966249685
        assert 6.5 < phi4 < 7.0, \
            f"φ⁴ = {phi4}, expected in range (6.5, 7.0)"
    
    def test_base_to_phi4_scaling(self):
        """Test that 41.7 × φ⁴ is in expected range."""
        harmonics = FrequencyHarmonics(precision=50)
        ladder = harmonics.compute_harmonic_ladder()
        
        f_phi4 = ladder["f_base_times_phi4"]
        # Expected ≈ 285.816 Hz
        assert 280 < f_phi4 < 300, \
            f"41.7 × φ⁴ = {f_phi4} Hz, expected in range (280, 300)"
    
    def test_ratio_to_888_hz(self):
        """Test that ratio 888 / (41.7 × φ⁴) ≈ π."""
        harmonics = FrequencyHarmonics(precision=50)
        ladder = harmonics.compute_harmonic_ladder()
        
        ratio = ladder["ratio_888_to_phi4_scaled"]
        # Ratio ≈ π ≈ 3.14159
        assert 3.0 < ratio < 3.2, \
            f"Ratio 888/(41.7×φ⁴) = {ratio}, expected ≈ π ≈ 3.14"
    
    def test_fundamental_frequency(self):
        """Test that fundamental frequency f₀ = 141.7001 Hz."""
        harmonics = FrequencyHarmonics(precision=50)
        ladder = harmonics.compute_harmonic_ladder()
        
        f0 = ladder["fundamental_frequency_f0"]
        assert abs(f0 - 141.7001) < 1e-6, \
            f"Fundamental f₀ = {f0} Hz, expected 141.7001 Hz"
    
    def test_gw250114_resonance(self):
        """Test GW250114 gravitational wave resonance validation."""
        harmonics = FrequencyHarmonics(precision=50)
        gw_validation = harmonics.validate_gw250114_resonance()
        
        assert gw_validation["resonance_validated"], \
            "GW250114 resonance should be validated"
        
        assert gw_validation["detected_frequency_Hz"] == 141.7001, \
            f"GW250114 frequency = {gw_validation['detected_frequency_Hz']}, expected 141.7001"
        
        assert gw_validation["frequency_match_error"] < 0.001, \
            f"Frequency match error = {gw_validation['frequency_match_error']}, expected < 0.001"
    
    def test_harmonic_ladder_validation(self):
        """Test that all harmonic ladder validations pass."""
        harmonics = FrequencyHarmonics(precision=50)
        ladder = harmonics.compute_harmonic_ladder()
        
        validation = ladder["validation"]
        assert validation["phi4_scaling_reasonable"], \
            "φ⁴ scaling should be reasonable (6.5 < φ⁴ < 7.0)"
        
        assert validation["base_to_888_achievable"], \
            "Base to 888 Hz scaling should be achievable"
        
        assert validation["pi_factor_present"], \
            "π factor should be present in ratio"
    
    def test_certificate_generation(self):
        """Test that frequency certificate can be generated."""
        harmonics = FrequencyHarmonics(precision=50)
        certificate = harmonics.generate_frequency_certificate()
        
        assert certificate["certificate_type"] == "QCAL_FREQUENCY_HARMONICS"
        assert certificate["status"] == "VALIDATED"
        assert certificate["coherence"] == 1.000000
        assert "harmonic_ladder" in certificate
        assert "gw250114_resonance" in certificate


class TestNoesisQOperator:
    """Test suite for Noesis_Q operator."""
    
    def test_operator_initialization(self):
        """Test that Noesis_Q operator initializes correctly."""
        noesis_q = NoesisQOperator(precision=50)
        
        # Check constants
        f0 = float(noesis_q.f0) if hasattr(noesis_q.f0, '__float__') else noesis_q.f0
        assert abs(f0 - 141.7001) < 1e-6, \
            f"QCAL f₀ = {f0}, expected 141.7001"
        
        C = float(noesis_q.C) if hasattr(noesis_q.C, '__float__') else noesis_q.C
        assert abs(C - 629.83) < 0.01, \
            f"Universal constant C = {C}, expected 629.83"
    
    def test_gradient_psi_computation(self):
        """Test gradient ∇Ψ computation."""
        noesis_q = NoesisQOperator(precision=50)
        
        # Compute gradient at θ=0, t=0
        gradient = noesis_q.compute_gradient_psi(theta=0.0, t=0.0)
        
        # Should return a complex number
        assert isinstance(gradient, complex), \
            f"Gradient should be complex, got {type(gradient)}"
        
        # Magnitude should be reasonable
        assert abs(gradient) > 0, \
            "Gradient magnitude should be non-zero"
    
    def test_zeta_critical_line(self):
        """Test zeta function on critical line."""
        noesis_q = NoesisQOperator(precision=50)
        
        # Compute ζ(1/2 + i·141.7·t) for t=0
        zeta_val = noesis_q.compute_zeta_critical_line(t=0.0)
        
        # Should return a complex number
        assert isinstance(zeta_val, complex), \
            f"Zeta value should be complex, got {type(zeta_val)}"
    
    def test_noesis_q_computation(self):
        """Test Noesis_Q operator computation."""
        noesis_q = NoesisQOperator(precision=50)
        
        # Compute Noesis_Q for θ=0
        result = noesis_q.compute_noesis_q(theta=0.0)
        
        # Check result structure
        assert "coherence_psi" in result
        assert "noesis_q_magnitude" in result
        assert "ram_xx_singularity_detected" in result
        
        # Coherence should be in [0, 1]
        coherence = result["coherence_psi"]
        assert 0 <= coherence <= 1, \
            f"Coherence Ψ = {coherence}, should be in [0, 1]"
    
    def test_ram_xx_singularity_detection(self):
        """Test RAM-XX Singularity detection."""
        noesis_q = NoesisQOperator(precision=50)
        
        # Scan for singularities
        detection = noesis_q.detect_ram_xx_singularity()
        
        # Check detection structure
        assert "singularities_detected" in detection
        assert "max_coherence_achieved" in detection
        assert "status" in detection
        
        # Max coherence should be non-negative
        max_coherence = detection["max_coherence_achieved"]
        assert max_coherence >= 0, \
            f"Max coherence = {max_coherence}, should be ≥ 0"
    
    def test_h_psi_selfadjoint_validation(self):
        """Test H_Ψ self-adjointness validation."""
        noesis_q = NoesisQOperator(precision=50)
        
        validation = noesis_q.validate_h_psi_selfadjoint()
        
        # All properties should be described (as design expectations)
        assert validation["self_adjoint"] is True
        assert validation["spectrum_real"] is True
        assert validation["compact_resolvent"] is True
        assert validation["hilbert_polya_applicable"] is True
        # Status should be PLACEHOLDER since this is a design expectation
        assert validation["status"] == "PLACEHOLDER"
        assert validation["verification_kind"] == "DESIGN_EXPECTATION_PLACEHOLDER"
        assert validation["verified_in_lean4"] is False
    
    def test_spectral_tensor_product(self):
        """Test spectral tensor product ∇Ψ ⊗ ζ(s)."""
        noesis_q = NoesisQOperator(precision=50)
        
        # Compute components
        gradient = noesis_q.compute_gradient_psi(theta=0.0, t=0.0)
        zeta_val = noesis_q.compute_zeta_critical_line(t=0.0)
        
        # Compute tensor product
        tensor = noesis_q.compute_spectral_tensor_product(gradient, zeta_val)
        
        # Should be complex
        assert isinstance(tensor, complex), \
            f"Tensor product should be complex, got {type(tensor)}"
    
    def test_certificate_generation(self):
        """Test that Noesis_Q certificate can be generated."""
        noesis_q = NoesisQOperator(precision=50)
        certificate = noesis_q.generate_noesis_q_certificate(theta=0.0)
        
        assert certificate["certificate_type"] == "NOESIS_Q_OPERATOR"
        assert certificate["status"] == "VALIDATED"
        assert "noesis_q_evaluation" in certificate
        assert "ram_xx_singularity" in certificate
        assert "h_psi_selfadjoint_validation" in certificate


class TestIntegration:
    """Integration tests for combined functionality."""
    
    def test_frequency_noesis_integration(self):
        """Test that frequency harmonics and Noesis_Q work together."""
        harmonics = FrequencyHarmonics(precision=50)
        noesis_q = NoesisQOperator(precision=50)
        
        # Get fundamental frequency from harmonics
        ladder = harmonics.compute_harmonic_ladder()
        f0_harmonics = ladder["fundamental_frequency_f0"]
        
        # Get fundamental frequency from Noesis_Q
        result = noesis_q.compute_noesis_q(theta=0.0)
        f0_noesis = result["fundamental_frequency_f0"]
        
        # Should match
        assert abs(f0_harmonics - f0_noesis) < 1e-6, \
            f"Fundamental frequencies should match: {f0_harmonics} vs {f0_noesis}"
    
    def test_qcal_constants_consistency(self):
        """Test that QCAL constants are consistent across modules."""
        harmonics = FrequencyHarmonics(precision=50)
        noesis_q = NoesisQOperator(precision=50)
        
        # Get constants from both modules
        ladder = harmonics.compute_harmonic_ladder()
        result = noesis_q.compute_noesis_q(theta=0.0)
        
        # Universal constant C
        C_harmonics = ladder["universal_constant_C"]
        C_noesis = result["universal_constant_C"]
        assert abs(C_harmonics - C_noesis) < 0.01, \
            f"Universal constant C should match: {C_harmonics} vs {C_noesis}"
        
        # Coherence constant C'
        C_prime_harmonics = ladder["coherence_constant_C_prime"]
        C_prime_noesis = result["coherence_constant_C_prime"]
        assert abs(C_prime_harmonics - C_prime_noesis) < 0.01, \
            f"Coherence constant C' should match: {C_prime_harmonics} vs {C_prime_noesis}"
    
    def test_certificates_generated(self):
        """Test that both certificates can be generated."""
        # Generate frequency certificate
        harmonics = FrequencyHarmonics(precision=50)
        freq_cert = harmonics.generate_frequency_certificate()
        
        # Generate Noesis_Q certificate
        noesis_q = NoesisQOperator(precision=50)
        noesis_cert = noesis_q.generate_noesis_q_certificate(theta=0.0)
        
        # Both should be validated
        assert freq_cert["status"] == "VALIDATED"
        assert noesis_cert["status"] == "VALIDATED"


def test_main_executables():
    """Test that main executables run without errors."""
    import subprocess
    import sys
    
    # Test frequency_harmonics.py
    result = subprocess.run(
        [sys.executable, "frequency_harmonics.py"],
        cwd=Path(__file__).parent,
        capture_output=True,
        timeout=30
    )
    assert result.returncode == 0, \
        f"frequency_harmonics.py failed: {result.stderr.decode()}"
    
    # Test noesis_q_operator.py
    result = subprocess.run(
        [sys.executable, "noesis_q_operator.py"],
        cwd=Path(__file__).parent,
        capture_output=True,
        timeout=30
    )
    assert result.returncode == 0, \
        f"noesis_q_operator.py failed: {result.stderr.decode()}"


if __name__ == "__main__":
    # Run tests with pytest
    pytest.main([__file__, "-v", "--tb=short"])
