#!/usr/bin/env python3
"""
Verify JSON-LD metadata schema files.
This script validates that a JSON-LD file is well-formed and contains required fields.
"""

import json
import sys
from pathlib import Path


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


def main():
    """Main entry point for the metadata validator."""
    if len(sys.argv) < 2:
        print("Usage: python verify_metadata.py <jsonld_file>")
        sys.exit(1)

    filepath = Path(sys.argv[1])

    if not filepath.exists():
        print(f"❌ Error: File does not exist: {filepath}")
        sys.exit(1)

    if validate_jsonld(filepath):
        print(f"\n✅ Metadata validation passed for {filepath}")
        sys.exit(0)
    else:
        print(f"\n❌ Metadata validation failed for {filepath}")
        sys.exit(1)


if __name__ == "__main__":
    main()
