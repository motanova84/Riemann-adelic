#!/usr/bin/env python3
"""
Simple Tests for piCODE-888 Bridge
===================================

Basic test script for the piCODE-888 conscious materialization bridge.
Does not require pytest.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
"""

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


def test_initialization():
    """Test bridge initialization."""
    print("  Testing initialization...")
    bridge = PiCode888Bridge()
    assert bridge.resonance_hz == 888.0
    assert bridge.tolerance_hz == 0.001
    assert bridge.coherence == 244.36
    assert bridge.psi_symbiotic == 1.000
    print("    ✅ Initialization correct")


def test_rna_to_greek():
    """Test RNA to Greek transformation."""
    print("  Testing RNA → Greek transformation...")
    bridge = PiCode888Bridge()
    
    # Test individual base mappings
    assert bridge.rna_to_greek("a") == "α"
    assert bridge.rna_to_greek("t") == "τ"
    assert bridge.rna_to_greek("c") == "χ"
    assert bridge.rna_to_greek("g") == "γ"
    assert bridge.rna_to_greek("u") == "υ"
    
    # Test full sequence
    rna = bridge.SEQUENCE_1_RNA
    greek = bridge.rna_to_greek(rna)
    assert len(greek) == len(rna)
    print("    ✅ RNA → Greek transformation correct")


def test_greek_to_rna():
    """Test Greek to RNA transformation."""
    print("  Testing Greek → RNA transformation...")
    bridge = PiCode888Bridge()
    
    # Test reversibility
    rna_original = "aattcgttgggg"
    greek = bridge.rna_to_greek(rna_original)
    rna_back = bridge.greek_to_rna(greek)
    assert rna_back == rna_original
    print("    ✅ Greek → RNA transformation correct")


def test_greek_to_hex():
    """Test Greek to hex transformation."""
    print("  Testing Greek → Hex transformation...")
    bridge = PiCode888Bridge()
    
    greek = "ατχγ"
    hex_seq = bridge.greek_to_hex(greek)
    
    # Verify it's valid hex
    assert all(c in '0123456789abcdef' for c in hex_seq)
    
    # Verify UTF-8 encoding
    expected = greek.encode('utf-8').hex()
    assert hex_seq == expected
    print("    ✅ Greek → Hex transformation correct")


def test_hex_to_greek():
    """Test hex to Greek transformation."""
    print("  Testing Hex → Greek transformation...")
    bridge = PiCode888Bridge()
    
    # Test reversibility
    greek_original = "ατχγ"
    hex_seq = bridge.greek_to_hex(greek_original)
    greek_back = bridge.hex_to_greek(hex_seq)
    assert greek_back == greek_original
    print("    ✅ Hex → Greek transformation correct")


def test_full_reversibility():
    """Test full chain reversibility."""
    print("  Testing full reversibility: RNA → Greek → Hex → Greek → RNA...")
    bridge = PiCode888Bridge()
    
    rna_original = bridge.SEQUENCE_1_RNA
    
    # Forward
    greek = bridge.rna_to_greek(rna_original)
    hex_seq = bridge.greek_to_hex(greek)
    
    # Backward
    greek_back = bridge.hex_to_greek(hex_seq)
    rna_back = bridge.greek_to_rna(greek_back)
    
    assert rna_back == rna_original
    print("    ✅ Full reversibility verified")


def test_hash_calculation():
    """Test hash calculation."""
    print("  Testing hash calculation...")
    bridge = PiCode888Bridge()
    
    hex_seq = "ceb1ceb1cf84cf84"
    hash_sig = bridge.calculate_hash(hex_seq)
    
    # Check length and format
    assert len(hash_sig) == 8
    assert all(c in '0123456789abcdef' for c in hash_sig)
    
    # Check consistency
    hash_sig2 = bridge.calculate_hash(hex_seq)
    assert hash_sig == hash_sig2
    print("    ✅ Hash calculation correct")


def test_qr_data_generation():
    """Test QR data generation."""
    print("  Testing QR data generation...")
    bridge = PiCode888Bridge()
    
    hex_signature = "ceb1ceb1cf84cf84"
    hash_signature = "7dbb2b52"
    
    qr_data = bridge.generate_qr_data(hex_signature, hash_signature)
    
    # Verify components
    assert qr_data.startswith("PICODE888|")
    assert "888Hz" in qr_data
    assert hash_signature in qr_data
    assert "JMMB_Ψ✧" in qr_data
    assert bridge.DOI_REFERENCE in qr_data
    
    # Verify structure
    parts = qr_data.split('|')
    assert len(parts) == 6
    print("    ✅ QR data generation correct")


def test_validation():
    """Test sequence validation."""
    print("  Testing sequence validation...")
    bridge = PiCode888Bridge()
    
    # Test correct sequence
    validation = bridge.validate_sequence(bridge.SEQUENCE_1_RNA)
    assert validation['length_valid'] is True
    assert validation['bases_valid'] is True
    assert validation['reversible'] is True
    
    # Test wrong length
    validation = bridge.validate_sequence("aattcg")
    assert validation['length_valid'] is False
    
    # Test invalid bases
    bad_seq = "aattcgxxggggtattatctttggctggtgttttcgccttattcgctttag"
    validation = bridge.validate_sequence(bad_seq)
    assert validation['bases_valid'] is False
    print("    ✅ Validation correct")


def test_complete_bridge():
    """Test complete bridge generation."""
    print("  Testing complete bridge generation...")
    bridge = PiCode888Bridge()
    
    bridge_seq = bridge.generate_complete_bridge()
    
    # Check all sequences
    assert bridge_seq.sequence_1_rna is not None
    assert bridge_seq.sequence_2_greek is not None
    assert bridge_seq.sequence_3_hex is not None
    assert bridge_seq.sequence_4_qr_data is not None
    
    # Check parameters
    assert bridge_seq.resonance_hz == 888.0
    assert bridge_seq.coherence == 1.000
    
    # Check hash
    assert len(bridge_seq.hash_signature) == 8
    
    # Check validation
    assert 'length_valid' in bridge_seq.validation_status
    assert 'bases_valid' in bridge_seq.validation_status
    assert 'reversible' in bridge_seq.validation_status
    print("    ✅ Complete bridge generation correct")


def test_utf8_byte_length():
    """Test UTF-8 byte length."""
    print("  Testing UTF-8 byte length...")
    bridge = PiCode888Bridge()
    
    rna = bridge.SEQUENCE_1_RNA
    greek = bridge.rna_to_greek(rna)
    
    # Each Greek character is 2 bytes in UTF-8
    utf8_bytes = len(greek.encode('utf-8'))
    assert utf8_bytes == 102  # 51 chars × 2 bytes
    print("    ✅ UTF-8 byte length correct (102 bytes)")


def test_hex_length():
    """Test hexadecimal length."""
    print("  Testing hexadecimal length...")
    bridge = PiCode888Bridge()
    
    rna = bridge.SEQUENCE_1_RNA
    greek = bridge.rna_to_greek(rna)
    hex_seq = bridge.greek_to_hex(greek)
    
    # 102 UTF-8 bytes = 204 hex characters
    assert len(hex_seq) == 204
    print("    ✅ Hex length correct (204 chars)")


def test_expected_sequences():
    """Test expected sequence values."""
    print("  Testing expected sequence values...")
    bridge = PiCode888Bridge()
    
    bridge_seq = bridge.generate_complete_bridge()
    
    # Check Sequence 1 (RNA)
    assert bridge_seq.sequence_1_rna == "aattcgttggggtattatctttggctggtgttttcgccttattcgctttag"
    
    # Check Sequence 2 (Greek)
    assert bridge_seq.sequence_2_greek == "ααττχγττγγγγταττατχτττγγχτγγτγττττχγχχτταττχγχττταγ"
    
    # Check Sequence 3 starts correctly
    assert bridge_seq.sequence_3_hex.startswith("ceb1ceb1cf84")
    
    # Check Sequence 4 format
    assert bridge_seq.sequence_4_qr_data.startswith("PICODE888|QCAL-888-UTF8-")
    print("    ✅ Expected sequences match")


def main():
    """Run all tests."""
    print("\n" + "=" * 80)
    print("🧪 piCODE-888 Bridge Tests")
    print("=" * 80 + "\n")
    
    tests = [
        test_initialization,
        test_rna_to_greek,
        test_greek_to_rna,
        test_greek_to_hex,
        test_hex_to_greek,
        test_full_reversibility,
        test_hash_calculation,
        test_qr_data_generation,
        test_validation,
        test_complete_bridge,
        test_utf8_byte_length,
        test_hex_length,
        test_expected_sequences,
    ]
    
    passed = 0
    failed = 0
    
    for test in tests:
        try:
            test()
            passed += 1
        except AssertionError as e:
            print(f"    ❌ FAILED: {e}")
            failed += 1
        except Exception as e:
            print(f"    ❌ ERROR: {e}")
            failed += 1
    
    print("\n" + "=" * 80)
    print(f"Tests: {passed} passed, {failed} failed, {passed + failed} total")
    print("=" * 80 + "\n")
    
    if failed == 0:
        print("✅ All tests passed!")
        return 0
    else:
        print(f"❌ {failed} test(s) failed")
        return 1


if __name__ == "__main__":
    sys.exit(main())
