#!/usr/bin/env python3
"""
Test suite for QCAL constants module (single source of truth).

This tests the fundamental constants and their mathematical relationships.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
"""

import pytest
import numpy as np
from qcal.constants import (
    # Fundamental constants
    F0, OMEGA_0, DELTA_ZETA, EUCLIDEAN_DIAGONAL, GAMMA_1,
    C_PRIMARY, C_COHERENCE, LAMBDA_0, COHERENCE_FACTOR,
    PHI, EULER_GAMMA, PI,
    PSI_EQUATION, QCAL_SIGNATURE, PICODE_888,
    AUTHOR, INSTITUTION, ORCID,
    DOI_MAIN, DOI_INFINITO, DOI_PNP, DOI_GOLDBACH, DOI_BSD,
    # Validation functions
    validate_constants_coherence,
    get_all_constants,
    get_constant,
    # Tolerances
    TOLERANCE_STRICT, TOLERANCE_NORMAL, TOLERANCE_RELAXED,
    PSI_THRESHOLD_EXCELLENT, PSI_THRESHOLD_GOOD, PSI_THRESHOLD_ACCEPTABLE,
)


class TestFundamentalConstants:
    """Test fundamental QCAL constants."""
    
    def test_f0_value(self):
        """Test that f₀ = 141.7001 Hz is defined correctly."""
        assert F0 == 141.7001
        assert isinstance(F0, (int, float))
    
    def test_omega_0_value(self):
        """Test that ω₀ = 2πf₀."""
        expected_omega = 2 * np.pi * F0
        assert np.isclose(OMEGA_0, expected_omega, rtol=1e-10)
    
    def test_euclidean_diagonal(self):
        """Test that Euclidean diagonal = 100√2."""
        expected = 100 * np.sqrt(2)
        assert np.isclose(EUCLIDEAN_DIAGONAL, expected, rtol=1e-10)
    
    def test_delta_zeta_value(self):
        """Test that δζ vibrational curvature constant is defined."""
        assert DELTA_ZETA == 0.2787437627
        assert isinstance(DELTA_ZETA, float)
    
    def test_f0_decomposition(self):
        """Test that f₀ = 100√2 + δζ."""
        f0_computed = EUCLIDEAN_DIAGONAL + DELTA_ZETA
        assert np.isclose(f0_computed, F0, rtol=1e-6)
    
    def test_gamma_1_value(self):
        """Test first Riemann zero imaginary part."""
        assert GAMMA_1 == 14.13472514
    
    def test_harmonic_modulation(self):
        """Test harmonic modulation f₀/γ₁ ≈ 10 + δζ/10."""
        harmonic = F0 / GAMMA_1
        expected = 10.0 + DELTA_ZETA / 10.0
        # Use relaxed tolerance as this involves gamma_1 approximation
        assert np.isclose(harmonic, expected, rtol=1e-3)


class TestSpectralConstants:
    """Test spectral constants for the dual framework."""
    
    def test_c_primary_value(self):
        """Test primary spectral constant C = 629.83."""
        assert C_PRIMARY == 629.83
    
    def test_c_coherence_value(self):
        """Test coherence constant C' = 244.36."""
        assert C_COHERENCE == 244.36
    
    def test_lambda_0_inverse(self):
        """Test that λ₀ = 1/C."""
        expected_lambda = 1.0 / C_PRIMARY
        assert np.isclose(LAMBDA_0, expected_lambda, rtol=1e-10)
    
    def test_coherence_factor(self):
        """Test coherence factor = C'/C."""
        expected_cf = C_COHERENCE / C_PRIMARY
        assert np.isclose(COHERENCE_FACTOR, expected_cf, rtol=1e-10)
    
    def test_energy_dialogue(self):
        """Test energy dialogue: (ω₀²/C')/(ω₀²/C) = 1/CF."""
        omega_sq = OMEGA_0 ** 2
        ratio_primary = omega_sq / C_PRIMARY
        ratio_coherence = omega_sq / C_COHERENCE
        energy_dialogue = ratio_coherence / ratio_primary
        inverse_cf = 1.0 / COHERENCE_FACTOR
        
        assert np.isclose(energy_dialogue, inverse_cf, rtol=1e-6)


class TestMathematicalConstants:
    """Test mathematical constants."""
    
    def test_phi_golden_ratio(self):
        """Test golden ratio φ = (1 + √5)/2."""
        expected_phi = (1 + np.sqrt(5)) / 2
        assert np.isclose(PHI, expected_phi, rtol=1e-10)
    
    def test_euler_gamma(self):
        """Test Euler-Mascheroni constant γ."""
        assert EULER_GAMMA == 0.5772156649015329
    
    def test_pi_value(self):
        """Test π value."""
        assert np.isclose(PI, np.pi, rtol=1e-15)


class TestQCALFramework:
    """Test QCAL framework constants."""
    
    def test_psi_equation(self):
        """Test Ψ equation string."""
        assert PSI_EQUATION == "Ψ = I × A_eff² × C^∞"
        assert isinstance(PSI_EQUATION, str)
    
    def test_qcal_signature(self):
        """Test QCAL signature."""
        assert QCAL_SIGNATURE == "∴𓂀Ω∞³"
        assert isinstance(QCAL_SIGNATURE, str)
    
    def test_picode_888(self):
        """Test πCODE identification."""
        assert PICODE_888 == "πCODE-888-QCAL2"
    
    def test_author_metadata(self):
        """Test author metadata."""
        assert AUTHOR == "José Manuel Mota Burruezo Ψ ✧ ∞³"
        assert INSTITUTION == "Instituto de Conciencia Cuántica (ICQ)"
        assert ORCID == "0009-0002-1923-0773"
    
    def test_doi_references(self):
        """Test DOI references are defined."""
        assert DOI_MAIN.startswith("10.5281/zenodo.")
        assert DOI_INFINITO.startswith("10.5281/zenodo.")
        assert DOI_PNP.startswith("10.5281/zenodo.")
        assert DOI_GOLDBACH.startswith("10.5281/zenodo.")
        assert DOI_BSD.startswith("10.5281/zenodo.")


class TestTolerances:
    """Test validation tolerances."""
    
    def test_tolerance_hierarchy(self):
        """Test that tolerances follow strict < normal < relaxed."""
        assert TOLERANCE_STRICT < TOLERANCE_NORMAL
        assert TOLERANCE_NORMAL < TOLERANCE_RELAXED
    
    def test_psi_threshold_hierarchy(self):
        """Test that Ψ thresholds follow acceptable < good < excellent."""
        assert PSI_THRESHOLD_ACCEPTABLE < PSI_THRESHOLD_GOOD
        assert PSI_THRESHOLD_GOOD < PSI_THRESHOLD_EXCELLENT


class TestConstantsCoherence:
    """Test constants coherence validation."""
    
    def test_validate_constants_coherence(self):
        """Test that constants coherence validation runs."""
        result = validate_constants_coherence(verbose=False)
        
        assert isinstance(result, dict)
        assert 'all_checks_passed' in result
        assert 'coherence_psi' in result
        assert 'coherence_level' in result
        assert 'checks' in result
        assert 'constants' in result
        assert 'relationships' in result
    
    def test_constants_all_checks(self):
        """Test that all constants checks are present."""
        result = validate_constants_coherence(verbose=False)
        
        expected_checks = [
            'f0_decomposition',
            'spectral_identity',
            'coherence_factor',
            'harmonic_modulation',
            'energy_dialogue'
        ]
        
        for check_name in expected_checks:
            assert check_name in result['checks']
    
    def test_constants_coherence_excellent(self):
        """Test that constants coherence is EXCELLENT."""
        result = validate_constants_coherence(verbose=False)
        
        assert result['coherence_psi'] > PSI_THRESHOLD_EXCELLENT
        assert result['coherence_level'] == 'EXCELLENT'
    
    def test_all_checks_passed(self):
        """Test that all coherence checks pass."""
        result = validate_constants_coherence(verbose=False)
        
        assert result['all_checks_passed'] is True


class TestGetAllConstants:
    """Test get_all_constants function."""
    
    def test_get_all_constants_structure(self):
        """Test that get_all_constants returns proper structure."""
        all_constants = get_all_constants()
        
        assert isinstance(all_constants, dict)
        
        expected_categories = [
            'frequency', 'spectral', 'mathematical',
            'qcal', 'doi', 'tolerances'
        ]
        
        for category in expected_categories:
            assert category in all_constants
            assert isinstance(all_constants[category], dict)
    
    def test_frequency_constants_present(self):
        """Test that frequency constants are present."""
        all_constants = get_all_constants()
        freq_constants = all_constants['frequency']
        
        assert 'F0' in freq_constants
        assert 'OMEGA_0' in freq_constants
        assert 'DELTA_ZETA' in freq_constants
        assert freq_constants['F0'] == F0
    
    def test_spectral_constants_present(self):
        """Test that spectral constants are present."""
        all_constants = get_all_constants()
        spectral = all_constants['spectral']
        
        assert 'C_PRIMARY' in spectral
        assert 'C_COHERENCE' in spectral
        assert spectral['C_PRIMARY'] == C_PRIMARY
        assert spectral['C_COHERENCE'] == C_COHERENCE


class TestGetConstant:
    """Test get_constant function."""
    
    def test_get_constant_by_name(self):
        """Test retrieving constant by name."""
        assert get_constant('F0') == F0
        assert get_constant('C_PRIMARY') == C_PRIMARY
        assert get_constant('C_COHERENCE') == C_COHERENCE
    
    def test_get_constant_default(self):
        """Test get_constant with default value."""
        assert get_constant('NONEXISTENT', default=42) == 42
        assert get_constant('NONEXISTENT') is None
    
    def test_get_constant_from_nested(self):
        """Test retrieving constant from nested categories."""
        assert get_constant('PHI') == PHI
        assert get_constant('QCAL_SIGNATURE') == QCAL_SIGNATURE


class TestConstantsImmutability:
    """Test that constants are properly defined (not accidentally mutable)."""
    
    def test_constants_are_numbers_or_strings(self):
        """Test that constants are immutable types."""
        for name in ['F0', 'C_PRIMARY', 'C_COHERENCE', 'LAMBDA_0']:
            value = get_constant(name)
            assert isinstance(value, (int, float))
        
        for name in ['PSI_EQUATION', 'QCAL_SIGNATURE', 'AUTHOR']:
            value = get_constant(name)
            assert isinstance(value, str)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
