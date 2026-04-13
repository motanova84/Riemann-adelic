#!/usr/bin/env python3
"""
Tests for piCODE-888 Bridge
============================

Test suite for the piCODE-888 conscious materialization bridge,
verifying all transformations, validations, and QCAL ∞³ field connections.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
"""

import pytest
import sys
import importlib.util
from pathlib import Path

# Direct import to avoid utils.__init__ issues
spec = importlib.util.spec_from_file_location(
    'picode_888_bridge',
    Path(__file__).parent.parent / 'utils' / 'picode_888_bridge.py'
)
picode_module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(picode_module)

PiCode888Bridge = picode_module.PiCode888Bridge
PiCodeBridgeSequence = picode_module.PiCodeBridgeSequence


class TestPiCode888Bridge:
    """Test suite for piCODE-888 bridge."""
    
    def setup_method(self):
        """Set up test fixtures."""
        self.bridge = PiCode888Bridge()
    
    def test_initialization(self):
        """Test bridge initialization."""
        assert self.bridge.resonance_hz == 888.0
        assert self.bridge.tolerance_hz == 0.001
        assert self.bridge.coherence == 244.36
        assert self.bridge.psi_symbiotic == 1.000
    
    def test_rna_sequence_length(self):
        """Test RNA sequence has correct length."""
        assert len(self.bridge.SEQUENCE_1_RNA) == 51
    
    def test_rna_sequence_bases(self):
        """Test RNA sequence contains only valid bases."""
        valid_bases = set('atcgu')
        assert all(base in valid_bases for base in self.bridge.SEQUENCE_1_RNA.lower())
    
    def test_rna_to_greek_transformation(self):
        """Test RNA to Greek UTF-8 transformation."""
        rna = self.bridge.SEQUENCE_1_RNA
        greek = self.bridge.rna_to_greek(rna)
        
        # Check length preserved
        assert len(greek) == len(rna)
        
        # Check all characters are Greek
        valid_greek = set('ατχγυ')
        assert all(char in valid_greek for char in greek)
    
    def test_greek_to_rna_transformation(self):
        """Test Greek to RNA reverse transformation."""
        greek = "ααττχγττγγγγταττατχτττγγχτγγτγττττχγχχτταττχγχττταγ"
        rna = self.bridge.greek_to_rna(greek)
        
        # Check length preserved
        assert len(rna) == len(greek)
        
        # Check all characters are valid bases
        valid_bases = set('atcgu')
        assert all(base in valid_bases for base in rna.lower())
    
    def test_reversibility_rna_greek(self):
        """Test reversibility of RNA ↔ Greek transformations."""
        rna_original = self.bridge.SEQUENCE_1_RNA
        
        # Forward and backward
        greek = self.bridge.rna_to_greek(rna_original)
        rna_recovered = self.bridge.greek_to_rna(greek)
        
        assert rna_recovered == rna_original
    
    def test_greek_to_hex_transformation(self):
        """Test Greek to hexadecimal transformation."""
        greek = "ααττχγ"
        hex_seq = self.bridge.greek_to_hex(greek)
        
        # Check it's valid hex
        assert all(c in '0123456789abcdef' for c in hex_seq)
        
        # Check UTF-8 encoding is correct
        expected_bytes = greek.encode('utf-8')
        expected_hex = expected_bytes.hex()
        assert hex_seq == expected_hex
    
    def test_hex_to_greek_transformation(self):
        """Test hexadecimal to Greek transformation."""
        # Known Greek → Hex → Greek roundtrip
        greek_original = "ατχγ"
        hex_seq = self.bridge.greek_to_hex(greek_original)
        greek_recovered = self.bridge.hex_to_greek(hex_seq)
        
        assert greek_recovered == greek_original
    
    def test_reversibility_greek_hex(self):
        """Test reversibility of Greek ↔ Hex transformations."""
        greek_original = self.bridge.rna_to_greek(self.bridge.SEQUENCE_1_RNA)
        
        # Forward and backward
        hex_seq = self.bridge.greek_to_hex(greek_original)
        greek_recovered = self.bridge.hex_to_greek(hex_seq)
        
        assert greek_recovered == greek_original
    
    def test_full_reversibility_chain(self):
        """Test full reversibility: RNA → Greek → Hex → Greek → RNA."""
        rna_original = self.bridge.SEQUENCE_1_RNA
        
        # Full forward transformation
        greek = self.bridge.rna_to_greek(rna_original)
        hex_seq = self.bridge.greek_to_hex(greek)
        
        # Full backward transformation
        greek_back = self.bridge.hex_to_greek(hex_seq)
        rna_back = self.bridge.greek_to_rna(greek_back)
        
        assert rna_back == rna_original
    
    def test_hash_calculation(self):
        """Test cryptographic hash calculation."""
        hex_seq = "ceb1ceb1cf84cf84"
        hash_sig = self.bridge.calculate_hash(hex_seq)
        
        # Check hash length is 8 characters
        assert len(hash_sig) == 8
        
        # Check it's valid hex
        assert all(c in '0123456789abcdef' for c in hash_sig)
    
    def test_hash_consistency(self):
        """Test hash calculation is consistent."""
        hex_seq = "test123"
        hash1 = self.bridge.calculate_hash(hex_seq)
        hash2 = self.bridge.calculate_hash(hex_seq)
        
        assert hash1 == hash2
    
    def test_qr_data_generation(self):
        """Test QR data generation."""
        hex_signature = "ceb1ceb1cf84cf84"
        hash_signature = "7dbb2b52"
        
        qr_data = self.bridge.generate_qr_data(hex_signature, hash_signature)
        
        # Check format
        assert qr_data.startswith("PICODE888|")
        assert "888Hz" in qr_data
        assert hash_signature in qr_data
        assert "JMMB_Ψ✧" in qr_data
        assert self.bridge.DOI_REFERENCE in qr_data
    
    def test_qr_data_components(self):
        """Test QR data has all required components."""
        hex_signature = "ceb1ceb1cf84cf84"
        hash_signature = "032cb045"
        
        qr_data = self.bridge.generate_qr_data(hex_signature, hash_signature)
        
        # Split and verify components
        parts = qr_data.split('|')
        assert len(parts) == 6
        assert parts[0] == "PICODE888"
        assert parts[1].startswith("QCAL-888-UTF8-")
        assert parts[2] == "888Hz"
        assert parts[3] == hash_signature
        assert parts[4] == self.bridge.DOI_REFERENCE
        assert parts[5] == "JMMB_Ψ✧"
    
    def test_validation_correct_sequence(self):
        """Test validation passes for correct sequence."""
        validation = self.bridge.validate_sequence(self.bridge.SEQUENCE_1_RNA)
        
        assert validation['length_valid'] is True
        assert validation['bases_valid'] is True
        assert validation['reversible'] is True
    
    def test_validation_wrong_length(self):
        """Test validation fails for wrong length."""
        wrong_length = "aattcgtt"  # Too short
        validation = self.bridge.validate_sequence(wrong_length)
        
        assert validation['length_valid'] is False
    
    def test_validation_invalid_bases(self):
        """Test validation fails for invalid bases."""
        invalid_bases = "aattcgxxggggtattatctttggctggtgttttcgccttattcgctttag"
        validation = self.bridge.validate_sequence(invalid_bases)
        
        assert validation['bases_valid'] is False
    
    def test_complete_bridge_generation(self):
        """Test complete bridge sequence generation."""
        bridge_seq = self.bridge.generate_complete_bridge()
        
        # Check all sequences are present
        assert bridge_seq.sequence_1_rna is not None
        assert bridge_seq.sequence_2_greek is not None
        assert bridge_seq.sequence_3_hex is not None
        assert bridge_seq.sequence_4_qr_data is not None
        
        # Check hash signature
        assert bridge_seq.hash_signature is not None
        assert len(bridge_seq.hash_signature) == 8
        
        # Check parameters
        assert bridge_seq.resonance_hz == 888.0
        assert bridge_seq.coherence == 1.000
    
    def test_complete_bridge_validation(self):
        """Test complete bridge has valid validation."""
        bridge_seq = self.bridge.generate_complete_bridge()
        
        assert 'length_valid' in bridge_seq.validation_status
        assert 'bases_valid' in bridge_seq.validation_status
        assert 'reversible' in bridge_seq.validation_status
        assert 'hash_match' in bridge_seq.validation_status
    
    def test_greek_utf8_byte_length(self):
        """Test Greek UTF-8 encoding has correct byte length."""
        rna = self.bridge.SEQUENCE_1_RNA
        greek = self.bridge.rna_to_greek(rna)
        
        # Each Greek character is 2 bytes in UTF-8
        utf8_bytes = len(greek.encode('utf-8'))
        assert utf8_bytes == 102  # 51 chars × 2 bytes
    
    def test_hex_sequence_length(self):
        """Test hexadecimal sequence has correct length."""
        rna = self.bridge.SEQUENCE_1_RNA
        greek = self.bridge.rna_to_greek(rna)
        hex_seq = self.bridge.greek_to_hex(greek)
        
        # 102 UTF-8 bytes = 204 hex characters
        assert len(hex_seq) == 204
    
    def test_symbolic_mapping_alpha(self):
        """Test 'a' maps to α (alpha)."""
        result = self.bridge.rna_to_greek("a")
        assert result == "α"
    
    def test_symbolic_mapping_tau(self):
        """Test 't' maps to τ (tau)."""
        result = self.bridge.rna_to_greek("t")
        assert result == "τ"
    
    def test_symbolic_mapping_chi(self):
        """Test 'c' maps to χ (chi)."""
        result = self.bridge.rna_to_greek("c")
        assert result == "χ"
    
    def test_symbolic_mapping_gamma(self):
        """Test 'g' maps to γ (gamma)."""
        result = self.bridge.rna_to_greek("g")
        assert result == "γ"
    
    def test_symbolic_mapping_upsilon(self):
        """Test 'u' maps to υ (upsilon)."""
        result = self.bridge.rna_to_greek("u")
        assert result == "υ"
    
    def test_resonance_frequency(self):
        """Test resonance frequency is 888 Hz."""
        assert self.bridge.resonance_hz == 888.0
    
    def test_tolerance(self):
        """Test frequency tolerance is 0.001 Hz."""
        assert self.bridge.tolerance_hz == 0.001
    
    def test_coherence_constant(self):
        """Test QCAL coherence constant."""
        assert self.bridge.coherence == 244.36
    
    def test_psi_symbiotic(self):
        """Test Ψ symbiotic link is 1.000."""
        assert self.bridge.psi_symbiotic == 1.000
    
    def test_doi_reference(self):
        """Test DOI reference is included."""
        assert self.bridge.DOI_REFERENCE == "https://doi.org/10.5281/zenodo.16425986"
    
    def test_expected_hex_signature(self):
        """Test the hex signature matches expected format."""
        bridge_seq = self.bridge.generate_complete_bridge()
        
        # The hex should start with ceb1ceb1cf84 (ααττ in Greek)
        assert bridge_seq.sequence_3_hex.startswith("ceb1ceb1cf84")
    
    def test_qr_key_format(self):
        """Test QR key has correct format."""
        bridge_seq = self.bridge.generate_complete_bridge()
        
        # Key should be QCAL-888-UTF8-{first 12 hex chars}
        expected_key = f"QCAL-888-UTF8-{bridge_seq.sequence_3_hex[:12]}"
        assert expected_key in bridge_seq.sequence_4_qr_data


def test_module_imports():
    """Test module can be imported."""
    assert PiCode888Bridge is not None
    assert PiCodeBridgeSequence is not None


def test_bridge_instantiation():
    """Test bridge can be instantiated."""
    bridge = PiCode888Bridge()
    assert bridge is not None


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
