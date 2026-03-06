"""
Tests for QCAL Economic Node
=============================

Test suite for the QCAL economia_nodo_semilla module.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Signature: ∴𓂀Ω∞³
"""

import pytest
import json
import sys
from pathlib import Path

# Add the module to path
sys.path.insert(0, str(Path(__file__).parent.parent / "qcal" / "economia_nodo_semilla"))
from main import (
    calculate_cs_full,
    calculate_cs_blockchain,
    generate_metadata,
    FREQ_BASE,
    FREQ_MANIFEST,
    FREQ_SIGNATURE,
    KAPPA_PI,
    COHERENCE_C,
    BLOCK_888888
)


class TestQCALConstants:
    """Test QCAL constants are properly defined."""
    
    def test_freq_base(self):
        """Test base frequency matches QCAL beacon."""
        assert FREQ_BASE == 141.7001
        assert isinstance(FREQ_BASE, float)
    
    def test_freq_manifest(self):
        """Test manifest frequency."""
        assert FREQ_MANIFEST == 888
        assert isinstance(FREQ_MANIFEST, int)
    
    def test_freq_signature(self):
        """Test signature frequency."""
        assert FREQ_SIGNATURE == 888.888
        assert isinstance(FREQ_SIGNATURE, float)
    
    def test_kappa_pi(self):
        """Test golden ratio φ."""
        assert abs(KAPPA_PI - 1.618033988749895) < 1e-10
        assert isinstance(KAPPA_PI, float)
    
    def test_coherence_c(self):
        """Test coherence constant from .qcal_beacon."""
        assert COHERENCE_C == 244.36
        assert isinstance(COHERENCE_C, float)
    
    def test_block_888888(self):
        """Test Bitcoin block 888888 reference."""
        assert BLOCK_888888["block_number"] == 888888
        assert "coinbase" in BLOCK_888888
        assert "fees_btc" in BLOCK_888888
        assert "timestamp" in BLOCK_888888


class TestCoherenceCalculations:
    """Test coherence score calculations."""
    
    def test_cs_full_one_btc(self):
        """Test full coherence score for 1 BTC."""
        satoshis = 100_000_000
        cs = calculate_cs_full(satoshis)
        
        # Verify it's a positive number
        assert cs > 0
        assert isinstance(cs, float)
        
        # Verify expected magnitude (approximately 10k)
        assert 10000 < cs < 11000
    
    def test_cs_full_zero(self):
        """Test full coherence score for 0 BTC."""
        cs = calculate_cs_full(0)
        assert cs == 0.0
    
    def test_cs_full_linearity(self):
        """Test that coherence score scales linearly with BTC amount."""
        cs_1btc = calculate_cs_full(100_000_000)
        cs_2btc = calculate_cs_full(200_000_000)
        
        # Should be approximately double
        assert abs(cs_2btc - 2 * cs_1btc) < 1e-6
    
    def test_cs_blockchain_one_btc(self):
        """Test blockchain coherence score for 1 BTC."""
        satoshis = 100_000_000
        cs_bc = calculate_cs_blockchain(satoshis)
        
        # Verify exact value for 1 BTC
        assert cs_bc == 626675633.0
    
    def test_cs_blockchain_half_btc(self):
        """Test blockchain coherence score for 0.5 BTC."""
        satoshis = 50_000_000
        cs_bc = calculate_cs_blockchain(satoshis)
        
        # Should be exactly half
        assert cs_bc == 313337816.5
    
    def test_cs_blockchain_linearity(self):
        """Test blockchain score linearity."""
        cs_1 = calculate_cs_blockchain(100_000_000)
        cs_3 = calculate_cs_blockchain(300_000_000)
        
        # Should be exactly 3x
        assert cs_3 == 3 * cs_1


class TestMetadataGeneration:
    """Test metadata generation."""
    
    def test_metadata_structure_one_btc(self):
        """Test metadata structure for 1 BTC."""
        metadata = generate_metadata(1.0)
        
        # Verify all required keys
        required_keys = [
            "token_id",
            "btc_value_satoshis",
            "btc_value_btc",
            "cs_value_full",
            "cs_value_blockchain",
            "coherence_score",
            "certified",
            "quantum_constants",
            "bitcoin_reference",
            "formula",
            "signature",
            "timestamp"
        ]
        
        for key in required_keys:
            assert key in metadata, f"Missing key: {key}"
    
    def test_metadata_quantum_constants(self):
        """Test quantum constants in metadata."""
        metadata = generate_metadata(1.0)
        qc = metadata["quantum_constants"]
        
        assert qc["freq_base"] == FREQ_BASE
        assert qc["freq_manifest"] == FREQ_MANIFEST
        assert qc["freq_signature"] == FREQ_SIGNATURE
        assert qc["kappa_pi"] == KAPPA_PI
        assert qc["coherence_c"] == COHERENCE_C
    
    def test_metadata_bitcoin_reference(self):
        """Test Bitcoin reference in metadata."""
        metadata = generate_metadata(1.0)
        btc_ref = metadata["bitcoin_reference"]
        
        assert btc_ref == BLOCK_888888
        assert btc_ref["block_number"] == 888888
    
    def test_metadata_formula_signature(self):
        """Test QCAL formula and signature."""
        metadata = generate_metadata(1.0)
        
        assert metadata["formula"] == "Ψ = I × A²_eff × C^∞"
        assert "JMMB Ψ" in metadata["signature"]
        assert "888.888 Hz" in metadata["signature"]
    
    def test_metadata_certified(self):
        """Test certification flag."""
        metadata = generate_metadata(1.0)
        assert metadata["certified"] is True
    
    def test_metadata_timestamp_format(self):
        """Test timestamp is ISO format with timezone."""
        metadata = generate_metadata(1.0)
        timestamp = metadata["timestamp"]
        
        # Verify it's a string
        assert isinstance(timestamp, str)
        
        # Verify it contains timezone info
        assert "+" in timestamp or "Z" in timestamp
    
    def test_metadata_half_btc(self):
        """Test metadata for 0.5 BTC."""
        metadata = generate_metadata(0.5)
        
        assert metadata["btc_value_btc"] == 0.5
        assert metadata["btc_value_satoshis"] == 50_000_000
        assert metadata["cs_value_full"] > 0
        assert metadata["cs_value_blockchain"] == 313337816.5
    
    def test_metadata_multiple_btc(self):
        """Test metadata for 2.5 BTC."""
        metadata = generate_metadata(2.5)
        
        assert metadata["btc_value_btc"] == 2.5
        assert metadata["btc_value_satoshis"] == 250_000_000
        
        # Verify coherence scales properly
        metadata_1 = generate_metadata(1.0)
        assert abs(metadata["cs_value_full"] - 2.5 * metadata_1["cs_value_full"]) < 1e-6


class TestQCALFormula:
    """Test the QCAL formula components."""
    
    def test_formula_components(self):
        """Test that the formula components combine correctly."""
        import math
        
        # For 1 BTC
        I = 1.0
        A_eff = math.sqrt(KAPPA_PI) * math.log(FREQ_MANIFEST)
        C_inf = FREQ_BASE * FREQ_SIGNATURE / FREQ_MANIFEST
        
        expected_cs = I * (A_eff ** 2) * C_inf
        actual_cs = calculate_cs_full(100_000_000)
        
        assert abs(expected_cs - actual_cs) < 1e-6
    
    def test_golden_ratio_in_formula(self):
        """Test golden ratio φ is used correctly."""
        import math
        
        # A_eff should contain √φ
        A_eff = math.sqrt(KAPPA_PI) * math.log(FREQ_MANIFEST)
        
        # Verify it's using the golden ratio
        assert math.sqrt(KAPPA_PI) == math.sqrt(1.618033988749895)
        
        # Verify the log component
        assert math.log(FREQ_MANIFEST) == math.log(888)


class TestCoherenceScore:
    """Test coherence score calculations."""
    
    def test_coherence_score_calibration(self):
        """Test coherence score is calibrated correctly."""
        metadata = generate_metadata(1.0)
        
        # Coherence score should be cs_blockchain / 1000
        expected_coherence = metadata["cs_value_blockchain"] / 1000
        assert metadata["coherence_score"] == expected_coherence
    
    def test_coherence_score_range(self):
        """Test coherence score is in expected range."""
        for btc_amount in [0.1, 0.5, 1.0, 2.0, 5.0]:
            metadata = generate_metadata(btc_amount)
            coherence = metadata["coherence_score"]
            
            # Should be positive
            assert coherence > 0
            
            # Should scale with BTC amount
            assert coherence == pytest.approx(btc_amount * 626675.633, rel=1e-6)


class TestJSONSerialization:
    """Test JSON serialization of metadata."""
    
    def test_metadata_json_serializable(self):
        """Test metadata can be serialized to JSON."""
        metadata = generate_metadata(1.0)
        
        # Should not raise an exception
        json_str = json.dumps(metadata, indent=4)
        assert isinstance(json_str, str)
        assert len(json_str) > 0
    
    def test_metadata_json_roundtrip(self):
        """Test metadata can be serialized and deserialized."""
        metadata = generate_metadata(1.0)
        
        # Serialize and deserialize
        json_str = json.dumps(metadata)
        recovered = json.loads(json_str)
        
        # Verify key fields are preserved
        assert recovered["btc_value_btc"] == metadata["btc_value_btc"]
        assert recovered["formula"] == metadata["formula"]
        assert recovered["signature"] == metadata["signature"]


class TestEdgeCases:
    """Test edge cases and error handling."""
    
    def test_very_small_amount(self):
        """Test with very small BTC amount."""
        metadata = generate_metadata(0.00000001)  # 1 satoshi
        
        assert metadata["btc_value_satoshis"] == 1
        assert metadata["cs_value_full"] > 0
        assert metadata["cs_value_blockchain"] > 0
    
    def test_very_large_amount(self):
        """Test with very large BTC amount."""
        metadata = generate_metadata(21_000_000)  # Max BTC supply
        
        assert metadata["btc_value_satoshis"] == 2_100_000_000_000_000
        assert metadata["cs_value_full"] > 0
        assert metadata["cs_value_blockchain"] > 0
    
    def test_zero_amount(self):
        """Test with zero BTC amount."""
        metadata = generate_metadata(0.0)
        
        assert metadata["btc_value_satoshis"] == 0
        assert metadata["cs_value_full"] == 0.0
        assert metadata["cs_value_blockchain"] == 0.0
        assert metadata["coherence_score"] == 0.0


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
