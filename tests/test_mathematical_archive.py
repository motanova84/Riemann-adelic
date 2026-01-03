"""
Tests for mathematical archive tools (metadata validation and conversion).
"""

import json
import sys
import tempfile
from pathlib import Path

import pytest

# Import the tools we're testing
sys.path.insert(0, str(Path(__file__).parent.parent))

from tools.convert_example import compute_sha256, extract_lean_metadata  # noqa: E402
from tools.verify_metadata import (  # noqa: E402
    validate_checksum,
    validate_context,
    validate_dependencies,
    validate_required_fields,
)


class TestMetadataValidation:
    """Test metadata validation functions."""

    def test_validate_required_fields_complete(self):
        """Test validation passes with all required fields."""
        data = {
            "@context": {},
            "@id": "test:id",
            "@type": "theorem",
            "dc:title": "Test Theorem",
            "dc:creator": "Test Author",
            "dc:date": "2025-10-19",
        }
        errors = validate_required_fields(data)
        assert len(errors) == 0

    def test_validate_required_fields_missing(self):
        """Test validation fails with missing fields."""
        data = {"@context": {}, "@id": "test:id"}
        errors = validate_required_fields(data)
        assert len(errors) > 0
        assert any("@type" in err for err in errors)
        assert any("dc:title" in err for err in errors)

    def test_validate_checksum_valid(self):
        """Test checksum validation with valid SHA-256."""
        data = {
            "checksum": {
                "@type": "jmmotaburr:SHA256",
                "schema:value": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
            }
        }
        errors = validate_checksum(data)
        assert len(errors) == 0

    def test_validate_checksum_invalid_length(self):
        """Test checksum validation with invalid length."""
        data = {"checksum": {"schema:value": "abc123"}}
        errors = validate_checksum(data)
        assert len(errors) > 0
        assert any("Invalid SHA-256" in err for err in errors)

    def test_validate_checksum_not_hex(self):
        """Test checksum validation with non-hexadecimal."""
        data = {"checksum": {"schema:value": "g" * 64}}
        errors = validate_checksum(data)
        assert len(errors) > 0
        assert any("not valid hexadecimal" in err for err in errors)

    def test_validate_dependencies_valid(self):
        """Test dependency validation with valid structure."""
        data = {"dependencies": [{"@id": "test:dep1", "@type": "axiom"}, {"@id": "test:dep2", "@type": "lemma"}]}
        errors = validate_dependencies(data)
        assert len(errors) == 0

    def test_validate_dependencies_missing_id(self):
        """Test dependency validation with missing @id."""
        data = {"dependencies": [{"@type": "axiom"}]}
        errors = validate_dependencies(data)
        assert len(errors) > 0
        assert any("missing @id" in err for err in errors)

    def test_validate_context_valid(self):
        """Test context validation with valid structure."""
        data = {"@context": {"dc": "http://purl.org/dc/elements/1.1/"}}
        errors = validate_context(data)
        assert len(errors) == 0


class TestConverter:
    """Test Lean converter functions."""

    def test_compute_sha256(self):
        """Test SHA-256 computation."""
        content = "test content"
        hash_result = compute_sha256(content)
        assert len(hash_result) == 64
        assert hash_result == "6ae8a75555209fd6c44157c0aed8016e763ff435a19cf186f76863140143ff72"

    def test_extract_lean_metadata_nonexistent_file(self):
        """Test extraction fails for non-existent file."""
        with pytest.raises(FileNotFoundError):
            extract_lean_metadata(Path("/nonexistent/file.lean"))

    def test_extract_lean_metadata_basic(self):
        """Test basic metadata extraction from Lean file."""
        # Create temporary Lean file
        with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", delete=False) as f:
            f.write("theorem test_theorem : True := trivial\n")
            f.write("lemma test_lemma : 1 + 1 = 2 := rfl\n")
            temp_path = Path(f.name)

        try:
            metadata = extract_lean_metadata(temp_path)

            assert "source_file" in metadata
            assert "checksum" in metadata
            assert "theorems" in metadata
            assert metadata["source_type"] == "Lean 4"
            assert "test_theorem" in metadata["theorems"]
            assert metadata["theorem_count"] == 1  # Only counts 'theorem', not 'lemma'
        finally:
            temp_path.unlink()

    def test_extract_lean_metadata_multiple_theorems(self):
        """Test extraction with multiple theorems."""
        content = """
theorem theorem_one : True := trivial
theorem theorem_two : False → False := id
theorem theorem_three (x : Nat) : x = x := rfl
"""
        with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", delete=False) as f:
            f.write(content)
            temp_path = Path(f.name)

        try:
            metadata = extract_lean_metadata(temp_path)

            assert metadata["theorem_count"] == 3
            assert "theorem_one" in metadata["theorems"]
            assert "theorem_two" in metadata["theorems"]
            assert "theorem_three" in metadata["theorems"]
        finally:
            temp_path.unlink()


class TestMetadataExample:
    """Test the example metadata file."""

    def test_example_metadata_loads(self):
        """Test that example metadata file loads correctly."""
        metadata_path = Path(__file__).parent.parent / "schema" / "metadata_example.jsonld"

        if metadata_path.exists():
            with open(metadata_path) as f:
                data = json.load(f)

            assert "@context" in data
            assert "@id" in data
            assert "@type" in data
            assert data["@type"] == "theorem"


class TestIntegration:
    """Integration tests for the full pipeline."""

    def test_example_lean_file_exists(self):
        """Test that example Lean file exists for CI."""
        example_path = Path(__file__).parent / "examples" / "example_lean.lean"
        assert example_path.exists()

    def test_schema_directory_exists(self):
        """Test that schema directory exists."""
        schema_dir = Path(__file__).parent.parent / "schema"
        assert schema_dir.exists()
        assert schema_dir.is_dir()

    def test_tools_directory_exists(self):
        """Test that tools directory exists."""
        tools_dir = Path(__file__).parent.parent / "tools"
        assert tools_dir.exists()
        assert tools_dir.is_dir()
