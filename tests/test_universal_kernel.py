"""
Tests for the Universal Kernel verification system.
"""

import pytest
import json
import os
import sys
from pathlib import Path

# Add tools directory to path
sys.path.insert(0, str(Path(__file__).parent.parent / "tools"))

import universal_kernel


class TestUniversalKernel:
    """Test suite for universal_kernel module."""
    
    def test_verify_universal_api_with_valid_files(self, tmp_path):
        """Test verification with valid files."""
        # Create test JSON-LD file
        jsonld_file = tmp_path / "test_metadata.jsonld"
        metadata = {
            "@context": "https://schema.org/",
            "@type": "SoftwareSourceCode",
            "name": "Test"
        }
        with open(jsonld_file, 'w') as f:
            json.dump(metadata, f)
        
        # Create test proof file
        proof_file = tmp_path / "test_proof.lean"
        with open(proof_file, 'w') as f:
            f.write("-- Test proof\ntheorem test : True := trivial\n")
        
        # Test verification
        result = universal_kernel.verify_universal_api(str(jsonld_file), str(proof_file))
        assert result is True
    
    def test_verify_universal_api_with_missing_jsonld(self, tmp_path):
        """Test verification with missing JSON-LD file."""
        jsonld_file = tmp_path / "nonexistent.jsonld"
        proof_file = tmp_path / "test_proof.lean"
        
        # Create proof file
        with open(proof_file, 'w') as f:
            f.write("-- Test proof\n")
        
        result = universal_kernel.verify_universal_api(str(jsonld_file), str(proof_file))
        assert result is False
    
    def test_verify_universal_api_with_missing_proof(self, tmp_path):
        """Test verification with missing proof file."""
        jsonld_file = tmp_path / "test_metadata.jsonld"
        proof_file = tmp_path / "nonexistent.lean"
        
        # Create JSON-LD file
        metadata = {
            "@context": "https://schema.org/",
            "@type": "SoftwareSourceCode"
        }
        with open(jsonld_file, 'w') as f:
            json.dump(metadata, f)
        
        result = universal_kernel.verify_universal_api(str(jsonld_file), str(proof_file))
        assert result is False
    
    def test_verify_universal_api_with_invalid_json(self, tmp_path):
        """Test verification with invalid JSON file."""
        jsonld_file = tmp_path / "invalid.jsonld"
        proof_file = tmp_path / "test_proof.lean"
        
        # Create invalid JSON file
        with open(jsonld_file, 'w') as f:
            f.write("{ invalid json }")
        
        # Create proof file
        with open(proof_file, 'w') as f:
            f.write("-- Test proof\n")
        
        result = universal_kernel.verify_universal_api(str(jsonld_file), str(proof_file))
        assert result is False
    
    def test_verify_universal_api_with_missing_required_fields(self, tmp_path):
        """Test verification with JSON-LD missing required fields."""
        jsonld_file = tmp_path / "incomplete.jsonld"
        proof_file = tmp_path / "test_proof.lean"
        
        # Create JSON-LD with missing @type field
        metadata = {
            "@context": "https://schema.org/"
        }
        with open(jsonld_file, 'w') as f:
            json.dump(metadata, f)
        
        # Create proof file
        with open(proof_file, 'w') as f:
            f.write("-- Test proof\n")
        
        result = universal_kernel.verify_universal_api(str(jsonld_file), str(proof_file))
        assert result is False
    
    def test_verify_universal_api_with_empty_files(self, tmp_path):
        """Test verification with empty files."""
        jsonld_file = tmp_path / "empty.jsonld"
        proof_file = tmp_path / "empty_proof.lean"
        
        # Create empty files
        jsonld_file.touch()
        proof_file.touch()
        
        result = universal_kernel.verify_universal_api(str(jsonld_file), str(proof_file))
        assert result is False
    
    def test_register_verification(self, tmp_path):
        """Test verification registration."""
        output_file = tmp_path / "qcal_state.json"
        
        result = universal_kernel.register_verification(
            "test.jsonld",
            "test.lean",
            True,
            str(output_file)
        )
        
        assert result is True
        assert output_file.exists()
        
        # Check content
        with open(output_file, 'r') as f:
            state = json.load(f)
        
        assert "verifications" in state
        assert len(state["verifications"]) == 1
        assert state["verifications"][0]["file"] == "test.jsonld"
        assert state["verifications"][0]["verified"] is True
    
    def test_verify_universal_with_example_schema(self):
        """Test verification with the actual example schema."""
        repo_root = Path(__file__).parent.parent
        jsonld_path = repo_root / "schema" / "metadatos_ejemplo.jsonld"
        
        # Create a temporary proof file
        import tempfile
        with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', delete=False) as f:
            f.write("-- Example proof\ntheorem example : True := trivial\n")
            proof_path = f.name
        
        try:
            if jsonld_path.exists():
                result = universal_kernel.verify_universal_api(str(jsonld_path), proof_path)
                assert result is True
        finally:
            # Clean up
            if os.path.exists(proof_path):
                os.unlink(proof_path)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
