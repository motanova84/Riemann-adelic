#!/usr/bin/env python3
"""
Verify JSON-LD metadata schema files.

This script validates mathematical archive metadata files to ensure:
- Valid JSON-LD structure
- Required fields are present
- Checksums are in correct format
- Dependencies are properly referenced

Usage:
    python tools/verify_metadata.py schema/metadata_example.jsonld
    python tools/verify_metadata.py schema/*.jsonld
"""

import json
import sys
from pathlib import Path
from typing import Any, Dict, List


def validate_required_fields(data: Dict[str, Any]) -> List[str]:
    """Validate that required fields are present in the metadata."""
    required_fields = ["@context", "@id", "@type", "dc:title", "dc:creator", "dc:date"]

    errors = []
    for field in required_fields:
        if field not in data:
            errors.append(f"Missing required field: {field}")

    return errors


def validate_checksum(data: Dict[str, Any]) -> List[str]:
    """Validate checksum format if present."""
    errors = []

    if "checksum" in data:
        checksum = data["checksum"]
        if not isinstance(checksum, dict):
            errors.append("Checksum must be an object")
        elif "schema:value" in checksum:
            value = checksum["schema:value"]
            # SHA-256 should be 64 hex characters
            if not isinstance(value, str) or len(value) != 64:
                errors.append(f"Invalid SHA-256 checksum format: {value}")
            try:
                int(value, 16)  # Verify it's hexadecimal
            except ValueError:
                errors.append(f"Checksum is not valid hexadecimal: {value}")

    return errors


def validate_dependencies(data: Dict[str, Any]) -> List[str]:
    """Validate dependencies structure if present."""
    errors = []

    if "dependencies" in data:
        deps = data["dependencies"]
        if not isinstance(deps, list):
            errors.append("Dependencies must be an array")
        else:
            for i, dep in enumerate(deps):
                if not isinstance(dep, dict):
                    errors.append(f"Dependency {i} must be an object")
                elif "@id" not in dep:
                    errors.append(f"Dependency {i} missing @id field")

    return errors


def validate_context(data: Dict[str, Any]) -> List[str]:
    """Validate JSON-LD @context structure."""
    errors = []

    if "@context" in data:
        context = data["@context"]
        if not isinstance(context, dict):
            errors.append("@context must be an object")

    return errors


def validate_metadata_file(filepath: Path) -> bool:
    """
    Validate a single metadata JSON-LD file.

    Args:
        filepath: Path to the JSON-LD file

    Returns:
        True if validation passes, False otherwise
    """
    print(f"\n{'='*70}")
    print(f"Validating: {filepath}")
    print(f"{'='*70}")

    # Check file exists
    if not filepath.exists():
        print(f"❌ ERROR: File not found: {filepath}")
        return False

    # Load and parse JSON
    try:
        with open(filepath, "r", encoding="utf-8") as f:
            data = json.load(f)
    except json.JSONDecodeError as e:
        print(f"❌ ERROR: Invalid JSON: {e}")
        return False
    except Exception as e:
        print(f"❌ ERROR: Failed to read file: {e}")
        return False

    # Collect all validation errors
    all_errors = []
    all_errors.extend(validate_context(data))
    all_errors.extend(validate_required_fields(data))
    all_errors.extend(validate_checksum(data))
    all_errors.extend(validate_dependencies(data))

    # Report results
    if all_errors:
        print(f"\n❌ Validation FAILED with {len(all_errors)} error(s):")
        for i, error in enumerate(all_errors, 1):
            print(f"  {i}. {error}")
        return False
    else:
        print("✅ Validation PASSED")
        print(f"   - @id: {data.get('@id', 'N/A')}")
        print(f"   - @type: {data.get('@type', 'N/A')}")
        print(f"   - title: {data.get('dc:title', 'N/A')}")
        if "dependencies" in data:
            print(f"   - dependencies: {len(data['dependencies'])} items")
        return True


def main():
    """Main entry point."""
    if len(sys.argv) < 2:
        print("Usage: python tools/verify_metadata.py <metadata_file.jsonld> [...]")
        print("\nExample:")
        print("  python tools/verify_metadata.py schema/metadata_example.jsonld")
        sys.exit(1)

    # Process all files provided
    filepaths = [Path(arg) for arg in sys.argv[1:]]
    results = []

    for filepath in filepaths:
        is_valid = validate_metadata_file(filepath)
        results.append((filepath, is_valid))

    # Summary
    print(f"\n{'='*70}")
    print("SUMMARY")
    print(f"{'='*70}")

    total = len(results)
    passed = sum(1 for _, valid in results if valid)
    failed = total - passed

    print(f"Total files: {total}")
    print(f"✅ Passed: {passed}")
    print(f"❌ Failed: {failed}")

    if failed > 0:
        print("\nFailed files:")
        for filepath, valid in results:
            if not valid:
                print(f"  - {filepath}")
        sys.exit(1)
    else:
        print("\n🎉 All metadata files are valid!")
        sys.exit(0)


def validate_jsonld(filepath):
    """
    Validate a JSON-LD metadata file.

    Args:
        filepath: Path to the JSON-LD file to validate

    Returns:
        bool: True if valid, False otherwise
    """
    try:
        with open(filepath, "r", encoding="utf-8") as f:
            data = json.load(f)

        # Check for @context (required in JSON-LD)
        if "@context" not in data:
            print(f"❌ Error: Missing '@context' in {filepath}")
            return False

        # Check for @type (commonly required)
        if "@type" not in data:
            print(f"⚠️  Warning: Missing '@type' in {filepath}")

        # Verify it's a valid dict
        if not isinstance(data, dict):
            print(
                f"❌ Error: JSON-LD root must be an object, not {type(data).__name__}"
            )
            return False

        print(f"✅ {filepath} is valid JSON-LD")
        return True

    except json.JSONDecodeError as e:
        print(f"❌ JSON parsing error in {filepath}: {e}")
        return False
    except FileNotFoundError:
        print(f"❌ File not found: {filepath}")
        return False
    except Exception as e:
        print(f"❌ Unexpected error validating {filepath}: {e}")
        return False


if __name__ == "__main__":
    main()
