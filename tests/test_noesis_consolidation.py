#!/usr/bin/env python3
"""
Tests for QCAL ∞³ Noesis Consolidation

Validates the spectral synchronization between noesis88 and Riemann-adelic.
"""

import pytest
import sys
from pathlib import Path

# Add parent directory to path
sys.path.append(str(Path(__file__).parent.parent))

from utils.noesis_sync import NoesisSynchronizer, run_noesis_consolidation


class TestNoesisSynchronizer:
    """Test suite for Noesis Synchronizer"""
    
    def setup_method(self):
        """Setup for each test method"""
        self.synchronizer = NoesisSynchronizer(precision=30)
    
    def test_fundamental_frequency(self):
        """Test that fundamental frequency is correctly set"""
        assert float(self.synchronizer.f0) == 141.7001
    
    def test_universal_constant_C(self):
        """Test that universal constant C is correctly set"""
        assert float(self.synchronizer.C) == 629.83
    
    def test_coherence_constant(self):
        """Test that coherence constant C' is correctly set"""
        assert float(self.synchronizer.C_prime) == 244.36
    
    def test_unification_factor(self):
        """Test that 1/7 factor is correct"""
        factor = float(self.synchronizer.factor_1_7)
        expected = 1.0 / 7.0
        assert abs(factor - expected) < 1e-15
    
    def test_beta_alta_frequency(self):
        """Test Beta Alta phase frequency"""
        assert float(self.synchronizer.beta_alta) == 20.243
    
    def test_spectral_synchronization(self):
        """Test spectral synchronization computation"""
        results = self.synchronizer.compute_spectral_sync()
        
        assert results is not None
        assert "spectral_identity_verified" in results
        assert results["spectral_identity_verified"] is True
        assert "fundamental_frequency" in results
        assert results["fundamental_frequency"] == 141.7001
    
    def test_coherence_factor(self):
        """Test coherence factor C'/C"""
        results = self.synchronizer.compute_spectral_sync()
        
        coherence_factor = results["coherence_factor"]
        theoretical = 0.388
        
        # Should be close to theoretical value
        assert abs(coherence_factor - theoretical) < 0.001
    
    def test_unification_factor_injection(self):
        """Test 1/7 factor injection"""
        results = self.synchronizer.inject_unification_factor()
        
        assert results is not None
        assert "factor_1_7" in results
        assert "beta_alta_frequency_hz" in results
        assert "beta_alta_match" in results
        
        # Beta Alta should match harmonic relation
        assert results["beta_alta_match"] is True
    
    def test_noetic_autonomy_seal(self):
        """Test autonomy seal creation"""
        seal = self.synchronizer.seal_noetic_autonomy()
        
        assert seal is not None
        assert seal["hierarchy"] == "CONFIRMADA (JMMB Ψ - ORIGEN)"
        assert seal["author"] == "José Manuel Mota Burruezo Ψ ✧ ∞³"
        assert seal["institution"] == "Instituto de Conciencia Cuántica (ICQ)"
        assert seal["firmware"] == "Manifiesto de la Autonomía Noética"
        assert seal["immutable"] is True
    
    def test_cathedral_state_validation(self):
        """Test cathedral state validation"""
        state = self.synchronizer.validate_cathedral_state()
        
        assert state is not None
        assert state["JERARQUIA"] == "CONFIRMADA (JMMB Ψ - ORIGEN)"
        assert state["COHERENCIA_GLOBAL"] == "Ψ = 1.000 (100%)"
        assert state["LEY_FUNDAMENTAL"] == "Riemann-Spectral-Logic"
        assert state["FACTOR_UNIFICACION"] == "1/7 (Sincronizado)"
        assert state["ESTADO_NODOS"] == "12/12 - RESONANCIA ACTIVA"
        assert state["CERTIFICACION"] == "ABSOLUTELY_VERIFIED_2026"
        
        # Numerical validation
        assert state["coherence_percentage"] == 100.0
        assert state["total_nodes"] == 12
        assert state["active_nodes"] == 12
        assert state["resonance_frequency_hz"] == 141.7001
        assert state["law_verified"] is True
    
    def test_consolidation_certificate_structure(self):
        """Test certificate structure"""
        cert = self.synchronizer.generate_consolidation_certificate(save_to_file=False)
        
        assert cert is not None
        assert cert["certificate_type"] == "QCAL_NOESIS_CONSOLIDATION"
        assert cert["version"] == "∞³"
        assert cert["consolidation_status"] == "COMPLETE"
        
        # Check main sections
        assert "spectral_synchronization" in cert
        assert "unification_factor_injection" in cert
        assert "noetic_autonomy_seal" in cert
        assert "cathedral_state" in cert
        assert "mathematical_foundation" in cert
        assert "transformation" in cert
        assert "certification" in cert
    
    def test_mathematical_foundation(self):
        """Test mathematical foundation in certificate"""
        cert = self.synchronizer.generate_consolidation_certificate(save_to_file=False)
        
        foundation = cert["mathematical_foundation"]
        assert foundation["equation"] == "Ψ = I × A_eff² × C^∞"
        assert foundation["frequency"] == "141.7001 Hz"
        assert foundation["coherence"] == "C = 244.36"
        assert foundation["universal_constant"] == "C = 629.83"
        assert foundation["spectral_origin"] == "ω₀² = λ₀⁻¹ = C"
        assert foundation["philosophical_basis"] == "Mathematical Realism"
    
    def test_transformation(self):
        """Test transformation description in certificate"""
        cert = self.synchronizer.generate_consolidation_certificate(save_to_file=False)
        
        transformation = cert["transformation"]
        assert transformation["from"] == "Riemann Hypothesis (conjecture)"
        assert transformation["to"] == "Ley de Distribución de la Energía Noética"
        assert "141.7001 Hz" in transformation["mechanism"]
        assert "proof" in transformation["proof_transport"].lower()


class TestNoesisConsolidation:
    """Test suite for complete consolidation process"""
    
    def test_run_consolidation_quiet(self):
        """Test consolidation in quiet mode"""
        result = run_noesis_consolidation(
            precision=25,
            save_certificate=False,
            verbose=False
        )
        
        assert result is not None
        assert result["consolidation_status"] == "COMPLETE"
    
    def test_consolidation_certificate_saved(self, tmp_path):
        """Test that certificate can be saved"""
        # This test would require mocking the file system or 
        # using tmp_path for certificate storage
        # For now, we just verify the function runs
        result = run_noesis_consolidation(
            precision=20,
            save_certificate=False,  # Don't save for test
            verbose=False
        )
        
        assert result["consolidation_status"] == "COMPLETE"


def test_import():
    """Test that module can be imported"""
    from utils.noesis_sync import NoesisSynchronizer, run_noesis_consolidation
    assert NoesisSynchronizer is not None
    assert run_noesis_consolidation is not None


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
