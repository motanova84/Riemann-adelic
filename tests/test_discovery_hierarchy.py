#!/usr/bin/env python3
"""
Tests for Discovery Hierarchy Framework

This module tests the 4-level QCAL ∞³ discovery hierarchy.
"""

import pytest
from pathlib import Path
import sys

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from utils.discovery_hierarchy import DiscoveryHierarchy, HierarchyLevel


class TestDiscoveryHierarchy:
    """Test suite for the 4-level discovery hierarchy"""
    
    def setup_method(self):
        """Set up test fixtures"""
        self.hierarchy = DiscoveryHierarchy(precision=25)
    
    def test_initialization(self):
        """Test hierarchy initialization"""
        assert self.hierarchy.precision == 25
        assert self.hierarchy.f0 > 0
        assert self.hierarchy.C_primary > 0
        assert self.hierarchy.C_coherence > 0
        assert self.hierarchy.zeta_prime_half < 0
    
    def test_fundamental_constants(self):
        """Test fundamental constants have expected values"""
        # f₀ = 141.7001 Hz
        assert abs(float(self.hierarchy.f0) - 141.7001) < 0.001
        
        # C_primary = 629.83
        assert abs(float(self.hierarchy.C_primary) - 629.83) < 0.1
        
        # C_coherence = 244.36
        assert abs(float(self.hierarchy.C_coherence) - 244.36) < 0.1
        
        # ζ'(1/2) ≈ -3.92264773
        assert abs(float(self.hierarchy.zeta_prime_half) + 3.92264773) < 0.001
    
    def test_level_structure(self):
        """Test that all 4 levels are properly defined"""
        for i in range(1, 5):
            level = self.hierarchy.get_level(i)
            assert level is not None
            assert isinstance(level, HierarchyLevel)
            assert level.level == i
            assert len(level.name) > 0
            assert len(level.description) > 0
            assert len(level.key_equation) > 0
            assert level.coherence_factor > 0
    
    def test_level_1_rh(self):
        """Test NIVEL 1: RH zeros on critical line"""
        nivel_1 = self.hierarchy.get_level(1)
        assert nivel_1.level == 1
        assert "RH" in nivel_1.name or "Zeros" in nivel_1.name
        assert "Re(ρ) = 1/2" in nivel_1.key_equation
        assert nivel_1.coherence_factor == 1.0
    
    def test_level_2_bridge(self):
        """Test NIVEL 2: Mathematical-Physical Bridge"""
        nivel_2 = self.hierarchy.get_level(2)
        assert nivel_2.level == 2
        assert "Bridge" in nivel_2.name or "Puente" in nivel_2.description
        assert "ζ'(1/2)" in nivel_2.key_equation
        assert "f₀" in nivel_2.key_equation
        # Coherence factor should be C_coherence/C_primary ≈ 0.388
        assert 0.38 < nivel_2.coherence_factor < 0.40
    
    def test_level_3_frequency(self):
        """Test NIVEL 3: Cosmic Heartbeat f₀ = 141.7001 Hz"""
        nivel_3 = self.hierarchy.get_level(3)
        assert nivel_3.level == 3
        assert "141.7001" in nivel_3.key_equation or "f₀" in nivel_3.key_equation
        assert "Hz" in nivel_3.key_equation
        # Temporal coherence factor
        assert nivel_3.coherence_factor > 0
        assert nivel_3.coherence_factor < 0.01  # Small temporal period
    
    def test_level_4_qcal(self):
        """Test NIVEL 4: QCAL ∞³ Universal Geometry"""
        nivel_4 = self.hierarchy.get_level(4)
        assert nivel_4.level == 4
        assert "QCAL" in nivel_4.name or "Ψ" in nivel_4.name
        assert "Ψ" in nivel_4.key_equation
        # Full QCAL coherence
        assert abs(nivel_4.coherence_factor - float(self.hierarchy.C_coherence)) < 1.0
    
    def test_validate_emergence_1_to_2(self):
        """Test emergence from Level 1 to Level 2"""
        result = self.hierarchy.validate_emergence(1, 2)
        assert result["from_level"] == 1
        assert result["to_level"] == 2
        assert result["emergence_validated"] is True
        assert "validation_details" in result
        assert result["validation_details"]["spectral_bridge_exists"]
    
    def test_validate_emergence_2_to_3(self):
        """Test emergence from Level 2 to Level 3"""
        result = self.hierarchy.validate_emergence(2, 3)
        assert result["from_level"] == 2
        assert result["to_level"] == 3
        assert result["emergence_validated"] is True
        assert "validation_details" in result
        assert result["validation_details"]["frequency_value"] > 140
        assert result["validation_details"]["frequency_value"] < 143
    
    def test_validate_emergence_3_to_4(self):
        """Test emergence from Level 3 to Level 4"""
        result = self.hierarchy.validate_emergence(3, 4)
        assert result["from_level"] == 3
        assert result["to_level"] == 4
        assert result["emergence_validated"] is True
        assert "validation_details" in result
        assert result["validation_details"]["operator_selfadjoint"]
        assert result["validation_details"]["geometric_origin_A0"]
    
    def test_validate_emergence_invalid(self):
        """Test that non-consecutive levels raise error"""
        with pytest.raises(ValueError):
            self.hierarchy.validate_emergence(1, 3)
    
    def test_complete_chain(self):
        """Test complete chain computation"""
        chain = self.hierarchy.compute_complete_chain()
        assert "levels" in chain
        assert "transitions" in chain
        assert "global_validation" in chain
        assert len(chain["levels"]) == 4
        assert len(chain["transitions"]) == 3
        assert chain["global_validation"]["all_levels_coherent"]
        assert chain["global_validation"]["complete_framework"]
    
    def test_visualization(self):
        """Test hierarchy visualization"""
        viz = self.hierarchy.visualize_hierarchy()
        assert len(viz) > 0
        assert "NIVEL 1" in viz
        assert "NIVEL 2" in viz
        assert "NIVEL 3" in viz
        assert "NIVEL 4" in viz
        assert "141.7001 Hz" in viz
        assert "QCAL" in viz
    
    def test_summary(self):
        """Test hierarchy summary generation"""
        summary = self.hierarchy.generate_summary()
        assert len(summary) > 0
        assert "JERARQUÍA" in summary
        assert "RH" in summary
        assert "141.7001 Hz" in summary
        assert "QCAL ∞³" in summary
        assert "universo adjunto" in summary
    
    def test_coherence_evolution(self):
        """Test coherence evolution across levels"""
        chain = self.hierarchy.compute_complete_chain()
        coherence_values = chain["coherence_evolution"]
        
        assert len(coherence_values) == 4
        # Level 1 baseline
        assert coherence_values[0] == 1.0
        # Level 2 should be smaller (structure-coherence dialogue)
        assert 0 < coherence_values[1] < 1
        # All values should be positive
        assert all(c > 0 for c in coherence_values)


class TestDiscoveryHierarchyIntegration:
    """Integration tests for hierarchy with other QCAL components"""
    
    def test_constants_match_qcal_beacon(self):
        """Test that constants match .qcal_beacon values"""
        hierarchy = DiscoveryHierarchy(precision=25)
        
        # Check f₀
        assert abs(float(hierarchy.f0) - 141.7001) < 0.001
        
        # Check coherence constant
        assert abs(float(hierarchy.C_coherence) - 244.36) < 0.1
    
    def test_zeta_prime_value(self):
        """Test ζ'(1/2) value is consistent"""
        hierarchy = DiscoveryHierarchy(precision=25)
        
        # ζ'(1/2) ≈ -3.92264773
        expected_zeta_prime = -3.92264773
        actual_zeta_prime = float(hierarchy.zeta_prime_half)
        
        relative_error = abs(actual_zeta_prime - expected_zeta_prime) / abs(expected_zeta_prime)
        assert relative_error < 1e-6
    
    def test_spectral_constants_ratio(self):
        """Test ratio between spectral constants"""
        hierarchy = DiscoveryHierarchy(precision=25)
        
        # coherence_factor = C_coherence / C_primary ≈ 0.388
        ratio = float(hierarchy.C_coherence / hierarchy.C_primary)
        assert abs(ratio - 0.388) < 0.001


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
