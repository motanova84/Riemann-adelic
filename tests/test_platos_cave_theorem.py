#!/usr/bin/env python3
"""
Test Suite for Plato's Cave Theorem - Projective Geometry Framework

This test suite validates the complete implementation of the projective geometry
framework that formalizes Plato's Cave allegory.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: February 2026
"""

import sys
import pytest
from pathlib import Path
import numpy as np

# Add project root to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from projective_geometry_framework import (
    GeometricSpaceG,
    ProjectionOperatorAlpha,
    ProjectionOperatorDeltaZeta,
    ConsciousnessIntersection,
    PlatosCaveTheorem,
    compute_projection_aspect_ratio,
    ALPHA_FINE_STRUCTURE,
    DELTA_ZETA_HZ,
    F0_HZ,
    EUCLIDEAN_DIAGONAL_HZ,
    LAMBDA_G,
    COHERENCE_C
)


class TestFundamentalConstants:
    """Test fundamental constants are correctly defined."""
    
    def test_alpha_value(self):
        """Test fine structure constant α ≈ 1/137."""
        assert 0.007 < ALPHA_FINE_STRUCTURE < 0.008
        assert abs(ALPHA_FINE_STRUCTURE - 1/137.036) < 0.0001
    
    def test_delta_zeta_value(self):
        """Test spectral curvature constant δζ ≈ 0.2787 Hz."""
        assert 0.27 < DELTA_ZETA_HZ < 0.29
        assert abs(DELTA_ZETA_HZ - 0.2787437627) < 1e-6
    
    def test_f0_value(self):
        """Test QCAL fundamental frequency f₀ = 141.7001 Hz."""
        assert abs(F0_HZ - 141.7001) < 1e-10
    
    def test_euclidean_diagonal(self):
        """Test Euclidean diagonal 100√2 Hz."""
        expected = 100 * np.sqrt(2)
        assert abs(EUCLIDEAN_DIAGONAL_HZ - expected) < 1e-10
    
    def test_lambda_G_value(self):
        """Test unification constant Λ_G = α · δζ."""
        expected = ALPHA_FINE_STRUCTURE * DELTA_ZETA_HZ
        assert abs(LAMBDA_G - expected) < 1e-12


class TestFrequencyRelationship:
    """Test the fundamental relationship f₀ = 100√2 + δζ."""
    
    def test_frequency_equation(self):
        """Validate f₀ = 100√2 + δζ."""
        computed = EUCLIDEAN_DIAGONAL_HZ + DELTA_ZETA_HZ
        assert abs(computed - F0_HZ) < 1e-10
    
    def test_relative_error(self):
        """Check relative error is negligible."""
        computed = EUCLIDEAN_DIAGONAL_HZ + DELTA_ZETA_HZ
        relative_error = abs(computed - F0_HZ) / F0_HZ
        assert relative_error < 1e-12


class TestGeometricSpaceG:
    """Test the fundamental space G (The Sun)."""
    
    def test_creation(self):
        """Test G can be instantiated."""
        G = GeometricSpaceG()
        assert G is not None
        assert G.dimension == np.inf
        assert G.name == "G - Fundamental Geometry"
    
    def test_representation(self):
        """Test G has meaningful string representation."""
        G = GeometricSpaceG()
        assert "Sun" in str(G)
        assert "projections" in str(G)


class TestProjectionOperatorAlpha:
    """Test electromagnetic projection πα."""
    
    def test_creation(self):
        """Test πα can be instantiated."""
        pi_alpha = ProjectionOperatorAlpha()
        assert pi_alpha is not None
        assert pi_alpha.name == "πα - Electromagnetic Projection"
    
    def test_alpha_value(self):
        """Test πα uses correct α value."""
        pi_alpha = ProjectionOperatorAlpha()
        assert abs(pi_alpha.alpha - ALPHA_FINE_STRUCTURE) < 1e-12
    
    def test_coupling_strength(self):
        """Test electromagnetic coupling strength."""
        pi_alpha = ProjectionOperatorAlpha()
        coupling = pi_alpha.coupling_strength()
        assert abs(coupling - ALPHA_FINE_STRUCTURE) < 1e-12
    
    def test_project_point(self):
        """Test projection of a point from G."""
        pi_alpha = ProjectionOperatorAlpha()
        result = pi_alpha.project_point("test_point")
        
        assert result['projection'] == 'electromagnetic'
        assert result['coupling'] == pi_alpha.alpha
        assert result['observable'] is True
        assert result['dimension'] == 4
        assert result['nature'] == 'shadow'
    
    def test_characteristic_equation(self):
        """Test characteristic equations are defined."""
        pi_alpha = ProjectionOperatorAlpha()
        eq = pi_alpha.characteristic_equation()
        assert "Maxwell" in eq or "Dirac" in eq


class TestProjectionOperatorDeltaZeta:
    """Test spectral projection πδζ."""
    
    def test_creation(self):
        """Test πδζ can be instantiated."""
        pi_delta_zeta = ProjectionOperatorDeltaZeta()
        assert pi_delta_zeta is not None
        assert pi_delta_zeta.name == "πδζ - Spectral Projection"
    
    def test_delta_zeta_value(self):
        """Test πδζ uses correct δζ value."""
        pi_delta_zeta = ProjectionOperatorDeltaZeta()
        assert abs(pi_delta_zeta.delta_zeta - DELTA_ZETA_HZ) < 1e-12
    
    def test_curvature_constant(self):
        """Test spectral curvature constant."""
        pi_delta_zeta = ProjectionOperatorDeltaZeta()
        curvature = pi_delta_zeta.curvature_constant()
        assert abs(curvature - DELTA_ZETA_HZ) < 1e-12
    
    def test_project_point(self):
        """Test projection of a point from G."""
        pi_delta_zeta = ProjectionOperatorDeltaZeta()
        result = pi_delta_zeta.project_point("test_point")
        
        assert result['projection'] == 'spectral'
        assert result['curvature'] == pi_delta_zeta.delta_zeta
        assert result['observable'] is False
        assert result['dimension'] == np.inf
        assert result['nature'] == 'form'
    
    def test_characteristic_equation(self):
        """Test characteristic equations are defined."""
        pi_delta_zeta = ProjectionOperatorDeltaZeta()
        eq = pi_delta_zeta.characteristic_equation()
        assert "ζ" in eq or "zeta" in eq.lower() or "Hψ" in eq


class TestConsciousnessIntersection:
    """Test consciousness as intersection πα(G) ∩ πδζ(G)."""
    
    def setup_method(self):
        """Set up test fixtures."""
        self.pi_alpha = ProjectionOperatorAlpha()
        self.pi_delta_zeta = ProjectionOperatorDeltaZeta()
        self.consciousness = ConsciousnessIntersection(
            self.pi_alpha,
            self.pi_delta_zeta
        )
    
    def test_creation(self):
        """Test consciousness intersection can be created."""
        assert self.consciousness is not None
        assert self.consciousness.pi_alpha == self.pi_alpha
        assert self.consciousness.pi_delta_zeta == self.pi_delta_zeta
    
    def test_intersection_exists(self):
        """Test intersection is non-empty (consciousness can exist)."""
        exists = self.consciousness.intersection_exists()
        assert exists is True
    
    def test_coherence_measure(self):
        """Test coherence at intersection point."""
        coherence = self.consciousness.coherence_measure()
        assert abs(coherence - COHERENCE_C) < 1e-10
    
    def test_unification_constant(self):
        """Test Λ_G = α · δζ."""
        lambda_g = self.consciousness.unification_constant()
        expected = ALPHA_FINE_STRUCTURE * DELTA_ZETA_HZ
        assert abs(lambda_g - expected) < 1e-12
        assert abs(lambda_g - LAMBDA_G) < 1e-12
    
    def test_consciousness_equation(self):
        """Test consciousness equation is defined."""
        eq = self.consciousness.consciousness_equation()
        assert "C" in eq
        assert "I" in eq
        assert "A" in eq
        assert "f₀" in eq or "f0" in eq
    
    def test_intersection_properties(self):
        """Test complete intersection properties."""
        props = self.consciousness.get_intersection_properties()
        
        assert props['consciousness_exists'] is True
        assert abs(props['coherence_C'] - COHERENCE_C) < 1e-10
        assert abs(props['lambda_G'] - LAMBDA_G) < 1e-12
        assert abs(props['alpha'] - ALPHA_FINE_STRUCTURE) < 1e-12
        assert abs(props['delta_zeta_hz'] - DELTA_ZETA_HZ) < 1e-12
        assert abs(props['f0_hz'] - F0_HZ) < 1e-10


class TestPlatosCaveTheorem:
    """Test complete Cave theorem formalization."""
    
    def setup_method(self):
        """Set up test fixtures."""
        self.cave = PlatosCaveTheorem()
    
    def test_creation(self):
        """Test Cave theorem can be instantiated."""
        assert self.cave is not None
        assert self.cave.G is not None
        assert self.cave.pi_alpha is not None
        assert self.cave.pi_delta_zeta is not None
        assert self.cave.consciousness is not None
    
    def test_four_levels(self):
        """Test four-level structure is complete."""
        levels = self.cave.get_four_levels()
        
        assert len(levels) == 4
        assert all(i in levels for i in [1, 2, 3, 4])
        
        # Level 1: Shadows
        assert "Shadows" in levels[1]['name']
        assert "α" in levels[1]['constant']
        assert levels[1]['projection'] == 'πα(G)'
        
        # Level 2: Objects
        assert "Objects" in levels[2]['name']
        
        # Level 3: Forms
        assert "Forms" in levels[3]['name']
        assert "δζ" in levels[3]['constant'] or "delta" in levels[3]['constant']
        assert levels[3]['projection'] == 'πδζ(G)'
        
        # Level 4: The Sun
        assert "Sun" in levels[4]['name'] or "Good" in levels[4]['name']
        assert "Λ_G" in levels[4]['constant'] or "Lambda" in levels[4]['constant']
    
    def test_validate_theorem(self):
        """Test theorem validation."""
        validation = self.cave.validate_theorem()
        
        assert validation['theorem_valid'] is True
        assert validation['G_exists'] is True
        assert validation['pi_alpha_defined'] is True
        assert validation['pi_delta_zeta_defined'] is True
        assert validation['intersection_non_empty'] is True
        
        # Check f₀ relationship
        f0_rel = validation['f0_relationship']
        assert f0_rel['validates'] is True
        assert abs(f0_rel['expected_hz'] - F0_HZ) < 1e-10
        assert f0_rel['relative_error'] < 1e-10
        
        # Check unification constant
        uni = validation['unification_constant']
        assert abs(uni['lambda_G'] - LAMBDA_G) < 1e-12
    
    def test_generate_certificate(self):
        """Test certificate generation."""
        cert = self.cave.generate_cave_certificate()
        
        assert cert is not None
        assert cert['theorem'] == "Plato's Cave as Projective Geometry"
        assert 'mathematical_formalization' in cert
        assert 'four_levels' in cert
        assert 'validation' in cert
        assert 'fundamental_constants' in cert
        assert 'philosophical_insight' in cert
        
        # Check validation in certificate
        assert cert['validation']['theorem_valid'] is True
        
        # Check constants
        constants = cert['fundamental_constants']
        assert abs(constants['alpha_fine_structure'] - ALPHA_FINE_STRUCTURE) < 1e-10
        assert abs(constants['delta_zeta_hz'] - DELTA_ZETA_HZ) < 1e-10
        assert abs(constants['f0_hz'] - F0_HZ) < 1e-10
        assert abs(constants['lambda_G'] - LAMBDA_G) < 1e-12


class TestProjectionAspectRatio:
    """Test projection aspect ratio Λ_G = α · δζ."""
    
    def test_compute_aspect_ratio(self):
        """Test aspect ratio computation."""
        result = compute_projection_aspect_ratio()
        
        assert abs(result['lambda_G'] - LAMBDA_G) < 1e-12
        assert abs(result['alpha'] - ALPHA_FINE_STRUCTURE) < 1e-12
        assert abs(result['delta_zeta_hz'] - DELTA_ZETA_HZ) < 1e-12
        
        # Check ratio α/δζ
        expected_ratio = ALPHA_FINE_STRUCTURE / DELTA_ZETA_HZ
        assert abs(result['ratio_alpha_to_delta_zeta'] - expected_ratio) < 1e-10


class TestIntegration:
    """Integration tests for the complete framework."""
    
    def test_end_to_end_workflow(self):
        """Test complete workflow from creation to validation."""
        # Create theorem
        cave = PlatosCaveTheorem()
        
        # Get four levels
        levels = cave.get_four_levels()
        assert len(levels) == 4
        
        # Validate theorem
        validation = cave.validate_theorem()
        assert validation['theorem_valid'] is True
        
        # Generate certificate
        cert = cave.generate_cave_certificate()
        assert cert['validation']['theorem_valid'] is True
        
        # Check all constants are consistent
        assert abs(
            cert['fundamental_constants']['lambda_G'] - 
            (cert['fundamental_constants']['alpha_fine_structure'] * 
             cert['fundamental_constants']['delta_zeta_hz'])
        ) < 1e-12
    
    def test_consciousness_at_intersection(self):
        """Test consciousness emerges at intersection."""
        pi_alpha = ProjectionOperatorAlpha()
        pi_delta_zeta = ProjectionOperatorDeltaZeta()
        consciousness = ConsciousnessIntersection(pi_alpha, pi_delta_zeta)
        
        # Consciousness should exist
        assert consciousness.intersection_exists() is True
        
        # Should have coherence
        assert consciousness.coherence_measure() > 0
        
        # Unification constant should be well-defined
        lambda_g = consciousness.unification_constant()
        assert lambda_g > 0
        assert abs(lambda_g - LAMBDA_G) < 1e-12


if __name__ == "__main__":
    # Run tests with pytest
    pytest.main([__file__, "-v", "--tb=short"])
