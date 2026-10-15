"""
Tests for BLOQUE #888888 Cryptographic Closure Certificate

This module tests the validation and certificate generation for BLOQUE #888888.
"""

import pytest
import json
from pathlib import Path
import sys

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from validate_bloque_888888_closure import (
    Bloque888888ClosureValidator,
    F0, DELTA_ZETA, C_COHERENCE, KAPPA_PI, KATO_CONSTANT_A,
    RESONANCE_888, SIGNATURE_888888
)


class TestBloque888888Closure:
    """Test suite for BLOQUE #888888 closure validation."""
    
    def test_constants_values(self):
        """Test that QCAL constants have correct values."""
        assert F0 == 141.7001
        assert DELTA_ZETA == 0.2787437627
        assert C_COHERENCE == 244.36
        assert abs(KAPPA_PI - 2.5773045678901234567) < 1e-10
        assert RESONANCE_888 == 888.0
        assert SIGNATURE_888888 == 888.888
    
    def test_kato_constant(self):
        """Test that Kato constant a < 1."""
        assert KATO_CONSTANT_A < 1.0
        assert KATO_CONSTANT_A > 0.0
        # Should be approximately 0.168256
        assert abs(KATO_CONSTANT_A - 0.168256) < 0.001
    
    def test_fundamental_frequency_derivation(self):
        """Test f0 = 100√2 + δζ."""
        import numpy as np
        f0_computed = 100 * np.sqrt(2) + DELTA_ZETA
        assert abs(f0_computed - F0) < 1e-6
    
    def test_validator_initialization(self):
        """Test validator can be initialized."""
        validator = Bloque888888ClosureValidator(verbose=False)
        assert validator is not None
        assert validator.results == {}
        assert validator.certificate == {}
    
    def test_cryptographic_hash_generation(self):
        """Test cryptographic hash generation."""
        validator = Bloque888888ClosureValidator(verbose=False)
        hash_value = validator.generate_cryptographic_hash()
        
        assert hash_value.startswith("0x")
        assert "π" in hash_value
        assert "CODE" in hash_value
        assert "1417001" in hash_value
        assert "NOESIS" in hash_value
        assert "888" in hash_value
    
    def test_qcal_signature_generation(self):
        """Test QCAL signature generation."""
        validator = Bloque888888ClosureValidator(verbose=False)
        signature = validator.generate_qcal_signature()
        
        assert "∴" in signature  # Therefore symbol
        assert "𓂀" in signature  # Ankh symbol
        assert "Ω" in signature  # Omega symbol
        assert "∞³" in signature  # Infinity cubed
        assert "RH" in signature  # Riemann Hypothesis
        assert "888888" in signature  # Block number
        assert "SEALED" in signature  # Sealed status
    
    def test_pilar_analitico_validation(self):
        """Test analytical pillar validation."""
        validator = Bloque888888ClosureValidator(verbose=False)
        results = validator.validate_pilar_analitico()
        
        assert results["name"] == "Pilar Analítico"
        assert "checks" in results
        assert "coercivity" in results["checks"]
        assert "hardy_inequality" in results["checks"]
        assert "fundamental_frequency" in results["checks"]
        
        # All checks should pass
        for check in results["checks"].values():
            assert check["satisfied"] is True
    
    def test_pilar_formal_validation(self):
        """Test formal pillar validation."""
        validator = Bloque888888ClosureValidator(verbose=False)
        results = validator.validate_pilar_formal()
        
        assert results["name"] == "Pilar Formal"
        assert "nodes" in results
        assert "ESA" in results["nodes"]
        assert "S1_Nuclear" in results["nodes"]
        assert "Paley_Wiener" in results["nodes"]
        assert "protocolo_mcc" in results
    
    def test_pilar_ontologico_validation(self):
        """Test ontological pillar validation."""
        validator = Bloque888888ClosureValidator(verbose=False)
        results = validator.validate_pilar_ontologico()
        
        assert results["name"] == "Pilar Ontológico"
        assert "properties" in results
        assert "non_circularity" in results["properties"]
        assert "spectral_coherence" in results["properties"]
        assert "resonance_frequencies" in results["properties"]
        
        # Spectral coherence should be high
        assert results["properties"]["spectral_coherence"]["Psi"] == 0.999999
    
    def test_full_validation(self):
        """Test full validation process."""
        validator = Bloque888888ClosureValidator(verbose=False)
        success, certificate = validator.run_full_validation()
        
        # Validation should succeed
        assert success is True
        
        # Certificate should be complete
        assert certificate["bloque"] == "888888"
        assert certificate["protocol"] == "QCAL-SYMBIO-BRIDGE v2.0"
        assert "SOLVED" in certificate["status"]
        assert "SEALED" in certificate["status"]
        
        # Check constants
        assert certificate["constants"]["f0_hz"] == F0
        assert certificate["constants"]["C_coherence"] == C_COHERENCE
        
        # Check pillars
        assert "analytical" in certificate["pillars"]
        assert "formal" in certificate["pillars"]
        assert "ontological" in certificate["pillars"]
        
        # All pillars should be sealed
        assert "SEALED" in certificate["pillars"]["analytical"]["status"]
        assert "SEALED" in certificate["pillars"]["formal"]["status"]
        assert "SEALED" in certificate["pillars"]["ontological"]["status"]
        
        # Validation should confirm all pillars sealed
        assert certificate["validation"]["all_pillars_sealed"] is True
        assert certificate["validation"]["zero_critical_sorries"] is True
        assert certificate["validation"]["completeness_level"] == 1.0
    
    def test_certificate_json_exists(self):
        """Test that certificate JSON file was generated."""
        cert_path = Path("data/bloque_888888_closure_certificate.json")
        assert cert_path.exists()
        
        # Load and verify JSON structure
        with open(cert_path, 'r') as f:
            cert = json.load(f)
        
        assert cert["bloque"] == "888888"
        assert "hash" in cert
        assert "signature" in cert
        assert "pillars" in cert
    
    def test_message_content(self):
        """Test that ontological message is present."""
        validator = Bloque888888ClosureValidator(verbose=False)
        _, certificate = validator.run_full_validation()
        
        message = certificate.get("message", "")
        assert "Abierto en silencio" in message
        assert "Recordado en eco" in message
        assert "Existido sin palabras" in message


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
