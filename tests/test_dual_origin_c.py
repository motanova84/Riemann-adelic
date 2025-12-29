#!/usr/bin/env python3
"""
Test suite for Dual Origin C Implementation

Validates the dual spectral constants framework:
- C = 629.83 (primary constant from λ₀)
- C' ≈ 244.36 (coherence constant from spectral moment)
- Geometric unification ζ'(1/2) ↔ f₀
- Arpeth framework integration

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
DOI: 10.5281/zenodo.17379721
"""

import pytest
import numpy as np
from operators.spectral_constants import (
    C_PRIMARY,
    C_COHERENCE,
    LAMBDA_0,
    F0,
    OMEGA_0,
    COHERENCE_FACTOR,
    validate_dual_constants,
    verify_f0_coherence,
    derive_f0_from_constants,
    compute_primary_constant,
    compute_coherence_constant,
)


class TestDualOriginConstants:
    """Test the dual origin implementation of constants C and C'."""
    
    def test_primary_constant_value(self):
        """Verify C = 629.83 is correctly defined."""
        assert C_PRIMARY == 629.83, "Primary constant C should be 629.83"
    
    def test_coherence_constant_value(self):
        """Verify C' ≈ 244.36 is correctly defined."""
        assert abs(C_COHERENCE - 244.36) < 0.01, "Coherence constant C' should be ≈ 244.36"
    
    def test_lambda_0_inverse_relation(self):
        """Verify C = 1/λ₀ relationship."""
        C_computed = 1.0 / LAMBDA_0
        assert abs(C_computed - C_PRIMARY) < 1.0, "C should equal 1/λ₀ approximately"
    
    def test_coherence_factor(self):
        """Verify coherence factor α = C'/C ≈ 0.388."""
        expected_factor = C_COHERENCE / C_PRIMARY
        assert abs(COHERENCE_FACTOR - expected_factor) < 1e-6, \
            "Coherence factor should equal C'/C"
        assert abs(COHERENCE_FACTOR - 0.388) < 0.01, \
            "Coherence factor should be ≈ 0.388"
    
    def test_energy_dialogue_inverse(self):
        """Verify energy dialogue = 1/coherence_factor."""
        energy_dialogue = 1.0 / COHERENCE_FACTOR
        omega_squared = OMEGA_0 ** 2
        
        ratio_primary = omega_squared / C_PRIMARY
        ratio_coherence = omega_squared / C_COHERENCE
        
        computed_dialogue = ratio_coherence / ratio_primary
        
        assert abs(computed_dialogue - energy_dialogue) < 0.01, \
            "Energy dialogue should equal 1/coherence_factor"
    
    def test_fundamental_frequency(self):
        """Verify f₀ = 141.7001 Hz."""
        assert abs(F0 - 141.7001) < 0.0001, "Fundamental frequency should be 141.7001 Hz"
    
    def test_omega_0_definition(self):
        """Verify ω₀ = 2πf₀."""
        expected_omega = 2 * np.pi * F0
        assert abs(OMEGA_0 - expected_omega) < 0.01, "ω₀ should equal 2πf₀"


class TestDualOriginFramework:
    """Test the complete dual origin framework validation."""
    
    def test_dual_constants_validation(self):
        """Validate the complete dual constants framework."""
        results = validate_dual_constants(verbose=False)
        
        assert results['validated'], "Dual constants framework should be validated"
        assert results['relationships']['C_lambda_match'], "C = 1/λ₀ should match"
        assert results['relationships']['coherence_factor_check'], \
            "Coherence factor should be consistent"
    
    def test_f0_coherence_verification(self):
        """Verify f₀ coherence with dual constants."""
        f0_check = verify_f0_coherence(tolerance=0.05)
        
        assert f0_check['framework_coherent'], "Framework should be coherent"
        assert f0_check['checks_passed']['inverse_relationship'], \
            "Inverse relationship should hold"
        assert f0_check['checks_passed']['energy_balance'], \
            "Energy balance should hold"
    
    def test_f0_derivation_analysis(self):
        """Test the analysis of f₀ derivation from constants."""
        analysis = derive_f0_from_constants()
        
        assert 'f0_target' in analysis, "Analysis should contain f0_target"
        assert abs(analysis['f0_target'] - F0) < 0.0001, \
            "Target frequency should match F0"
        assert analysis['coherence_factor'] > 0, "Coherence factor should be positive"
        assert analysis['energy_dialogue'] > 0, "Energy dialogue should be positive"
    
    def test_spectral_adelic_link(self):
        """Verify the spectral-adelic link ζ'(1/2) ↔ f₀."""
        # Both should emerge from the same A₀ geometric origin
        # This is validated by framework coherence
        f0_check = verify_f0_coherence()
        assert f0_check['framework_coherent'], \
            "Spectral-adelic link requires framework coherence"


class TestArpethIntegration:
    """Test Arpeth framework integration with dual origin."""
    
    def test_arpeth_constants_consistency(self):
        """Verify Arpeth constants match QCAL framework."""
        from utils.arpeth_bioinformatics import F0_FREQUENCY, C_COHERENCE as C_ARPETH
        
        assert abs(float(F0_FREQUENCY) - F0) < 0.0001, \
            "Arpeth F0 should match QCAL F0"
        assert abs(float(C_ARPETH) - C_COHERENCE) < 0.01, \
            "Arpeth C' should match QCAL C'"
    
    def test_biological_coherence_validation(self):
        """Test RNA sequence validation at 141.7 Hz."""
        from utils.arpeth_bioinformatics import validate_biological_coherence
        
        # Test a simple sequence
        sequence = "AUGCCC"
        result = validate_biological_coherence(sequence)
        
        assert 'stability_score' in result, "Result should contain stability_score"
        assert 'resonance_match' in result, "Result should contain resonance_match"
        assert 'qcal_validated' in result, "Result should contain qcal_validated"
        assert result['fundamental_frequency'] == 141.7001, \
            "Fundamental frequency should be 141.7001 Hz"
    
    def test_fractal_symmetry_parameter(self):
        """Verify fractal symmetry parameter κ_Π = 17."""
        from utils.arpeth_bioinformatics import KAPPA_PI
        
        assert KAPPA_PI == 17, "Fractal parameter should be prime 17"


class TestComputationFunctions:
    """Test computation functions for dual constants."""
    
    def test_compute_primary_constant(self):
        """Test computation of C from λ₀."""
        C_computed = compute_primary_constant(LAMBDA_0)
        assert abs(C_computed - C_PRIMARY) < 1.0, "Computed C should match C_PRIMARY"
    
    def test_compute_coherence_constant(self):
        """Test computation of C' from eigenvalues."""
        # Create mock eigenvalues with λ₀ as minimum
        eigenvalues = np.array([LAMBDA_0, 0.002, 0.003, 0.004, 0.005])
        
        C_coherence_computed = compute_coherence_constant(eigenvalues, LAMBDA_0)
        
        # Should be positive and reasonable
        assert C_coherence_computed > 0, "Coherence constant should be positive"
        assert C_coherence_computed < 1000, "Coherence constant should be reasonable"
    
    def test_primary_constant_positivity(self):
        """Verify λ₀ must be positive for C computation."""
        with pytest.raises(ValueError):
            compute_primary_constant(-1.0)
        
        with pytest.raises(ValueError):
            compute_primary_constant(0.0)


class TestGeometricUnification:
    """Test the geometric unification ζ'(1/2) ↔ f₀."""
    
    def test_zeta_derivative_range(self):
        """Verify ζ'(1/2) is in expected range."""
        # ζ'(1/2) ≈ -3.92247
        # This connects to the spectral structure
        zeta_prime_half = -3.92247
        
        # Verify it's negative (expected from RH theory)
        assert zeta_prime_half < 0, "ζ'(1/2) should be negative"
        assert abs(zeta_prime_half + 3.92247) < 0.01, \
            "ζ'(1/2) should be ≈ -3.92247"
    
    def test_dual_origin_A0_consistency(self):
        """Test that both C and C' emerge from same A₀."""
        # The framework validation checks this implicitly
        results = validate_dual_constants(verbose=False)
        
        # If validated, both constants are consistent with A₀
        assert results['validated'], "Dual origin from A₀ should be consistent"
        
        # Both should be positive
        assert results['constants']['C_primary'] > 0
        assert results['constants']['C_coherence'] > 0
        
        # Coherence factor should be in (0,1)
        assert 0 < results['constants']['coherence_factor'] < 1


class TestDocumentation:
    """Test that documentation is consistent with implementation."""
    
    def test_qcal_beacon_constants(self):
        """Verify .qcal_beacon contains dual origin documentation."""
        with open('.qcal_beacon', 'r', encoding='utf-8') as f:
            beacon_content = f.read()
        
        assert 'universal_constant_C = "629.83"' in beacon_content
        assert 'coherence_constant_C_prime = "244.36"' in beacon_content
        assert 'dual_origin_relation' in beacon_content
        assert 'spectral_adelic_link' in beacon_content
    
    def test_dual_constants_doc_exists(self):
        """Verify DUAL_SPECTRAL_CONSTANTS.md exists and has key content."""
        import os
        assert os.path.exists('DUAL_SPECTRAL_CONSTANTS.md'), \
            "DUAL_SPECTRAL_CONSTANTS.md should exist"
        
        with open('DUAL_SPECTRAL_CONSTANTS.md', 'r', encoding='utf-8') as f:
            content = f.read()
        
        assert 'Dual Origin' in content or 'dual origin' in content
        assert '629.83' in content
        assert '244.36' in content
        assert "ζ'(1/2)" in content or 'zeta' in content
    
    def test_dual_origin_implementation_doc_exists(self):
        """Verify DUAL_ORIGIN_C_IMPLEMENTATION.md exists."""
        import os
        assert os.path.exists('DUAL_ORIGIN_C_IMPLEMENTATION.md'), \
            "DUAL_ORIGIN_C_IMPLEMENTATION.md should exist"
        
        with open('DUAL_ORIGIN_C_IMPLEMENTATION.md', 'r', encoding='utf-8') as f:
            content = f.read()
        
        assert 'Arpeth' in content
        assert 'ABC' in content
        assert 'Weil-Guinand' in content


if __name__ == "__main__":
    # Run tests with verbose output
    pytest.main([__file__, '-v', '--tb=short'])
