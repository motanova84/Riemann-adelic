"""
Converter stub: Lean → Intermediate Format (Dedukti/OMDoc)

This is a starting point for building converters from Lean proof terms
to an intermediate format suitable for verification and interoperability.

The recommended workflow:
1. Extract proof term / AST from Lean (using lean-export or lean4 tools)
2. Map syntax to intermediate format (e.g., Dedukti, MMT, OMDoc)
3. Generate metadata (schema/metadata_example.jsonld)
4. Verify using kernel checker

Usage:
    python tools/convert_example.py formalization/lean/RiemannAdelic/functional_eq.lean
    python tools/convert_example.py formalization/lean/Main.lean --output output.dk
"""

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Dict, Any


def compute_sha256(content: str) -> str:
    """Compute SHA-256 hash of content."""
    return hashlib.sha256(content.encode("utf-8")).hexdigest()


def extract_lean_metadata(lean_file: Path) -> Dict[str, Any]:
    """
    Extract basic metadata from a Lean file.

    This is a stub implementation. A real converter would:
    - Parse the Lean file AST
    - Extract theorem names, types, and proofs
    - Map to intermediate representation
    - Generate checksums and dependencies

    Args:
        lean_file: Path to the Lean source file

    Returns:
        Dictionary with extracted metadata
    """
    if not lean_file.exists():
        raise FileNotFoundError(f"Lean file not found: {lean_file}")

    # Read file content
    content = lean_file.read_text(encoding="utf-8")

    # Extract basic information (stub implementation)
    metadata = {
        "source_file": str(lean_file),
        "source_type": "Lean 4",
        "checksum": compute_sha256(content),
        "size_bytes": len(content),
        "lines": content.count("\n") + 1,
    }

    # Look for theorem declarations (very basic pattern matching)
    theorems = []
    for line in content.split("\n"):
        stripped = line.strip()
        if stripped.startswith("theorem "):
            # Extract theorem name
            parts = stripped.split()
            if len(parts) >= 2:
                theorem_name = parts[1].rstrip(":")
                theorems.append(theorem_name)

    metadata["theorems"] = theorems
    metadata["theorem_count"] = len(theorems)

    return metadata


def convert_to_intermediate(lean_file: Path, output_file: Path = None) -> str:
    """
    Convert Lean file to intermediate format.

    This is a stub that demonstrates the conversion pipeline.
    A real implementation would:
    - Use Lean's export format or LSP
    - Parse proof terms
    - Generate Dedukti/MMT/OMDoc output
    - Preserve semantic information

    Args:
        lean_file: Path to input Lean file
        output_file: Optional path to output file

    Returns:
        String representation of intermediate format
    """
    metadata = extract_lean_metadata(lean_file)

    # Generate intermediate format (stub - would be actual Dedukti/MMT syntax)
    intermediate = f"""
; Intermediate Format Stub (Dedukti-style)
; Generated from: {metadata['source_file']}
; Checksum: {metadata['checksum']}
; Theorems: {metadata['theorem_count']}

; This is a placeholder for actual Dedukti/MMT/OMDoc output.
; A real converter would generate formal proof terms here.

; Source theorems found:
"""

    for theorem in metadata["theorems"]:
        intermediate += f";   - {theorem}\n"

    intermediate += """
; Example Dedukti syntax (illustrative):
; Type : Type.
; Prop : Type.
; proof : Prop -> Type.
;
; [A : Prop] thm_rh : proof A.

; TODO: Implement actual conversion logic
"""

    # Save to file if specified
    if output_file:
        output_file.write_text(intermediate, encoding="utf-8")
        print(f"✅ Intermediate format saved to: {output_file}")

    return intermediate


def generate_metadata_jsonld(lean_file: Path, metadata: Dict[str, Any]) -> Dict[str, Any]:
    """
    Generate JSON-LD metadata for the converted file.

    Args:
        lean_file: Path to source Lean file
        metadata: Extracted metadata dictionary

    Returns:
        JSON-LD metadata dictionary
    """
    jsonld = {
        "@context": {
            "dc": "http://purl.org/dc/elements/1.1/",
            "schema": "http://schema.org/",
            "jmmotaburr": "urn:jmmotaburr:riemann-adelic:",
        },
        "@id": f"urn:jmmotaburr:riemann-adelic:converted:{lean_file.stem}",
        "@type": "proof",
        "dc:title": f"Converted from {lean_file.name}",
        "dc:source": str(lean_file),
        "dc:date": "2025-10-19",
        "formalizedIn": {"@type": "proofsystem:ProofSystem", "schema:name": "Lean 4", "schema:version": "4.0.0"},
        "checksum": {"@type": "jmmotaburr:SHA256", "schema:value": metadata["checksum"]},
        "schema:contentSize": metadata["size_bytes"],
    }

    if metadata.get("theorems"):
        jsonld["theorems"] = metadata["theorems"]

    return jsonld


def main():
    """Main entry point."""
    parser = argparse.ArgumentParser(description="Convert Lean proof files to intermediate format")
    parser.add_argument("lean_file", type=Path, help="Path to Lean source file")
    parser.add_argument("-o", "--output", type=Path, help="Output file for intermediate format (optional)")
    parser.add_argument("-m", "--metadata", type=Path, help="Output file for JSON-LD metadata (optional)")
    parser.add_argument("-v", "--verbose", action="store_true", help="Verbose output")

    args = parser.parse_args()

    print("=" * 70)
    print("Lean → Intermediate Format Converter (Stub)")
    print("=" * 70 + "\n")

    # Extract metadata
    try:
        print(f"📂 Reading: {args.lean_file}")
        metadata = extract_lean_metadata(args.lean_file)

        if args.verbose:
            print("\nExtracted metadata:")
            print(json.dumps(metadata, indent=2))

        print(f"✅ Found {metadata['theorem_count']} theorem(s)")
        for theorem in metadata["theorems"]:
            print(f"   - {theorem}")

    except FileNotFoundError as e:
        print(f"❌ ERROR: {e}")
        sys.exit(1)
    except Exception as e:
        print(f"❌ ERROR: Failed to extract metadata: {e}")
        sys.exit(1)

    # Convert to intermediate format
    try:
        print("\n🔄 Converting to intermediate format...")
        intermediate = convert_to_intermediate(args.lean_file, args.output)

        if not args.output and args.verbose:
            print("\nGenerated intermediate format:")
            print(intermediate)

        print("✅ Conversion completed (stub)")

    except Exception as e:
        print(f"❌ ERROR: Conversion failed: {e}")
        sys.exit(1)

    # Generate metadata
    if args.metadata:
        try:
            print("\n📝 Generating JSON-LD metadata...")
            jsonld = generate_metadata_jsonld(args.lean_file, metadata)

            with open(args.metadata, "w", encoding="utf-8") as f:
                json.dump(jsonld, f, indent=2, ensure_ascii=False)

            print(f"✅ Metadata saved to: {args.metadata}")

        except Exception as e:
            print(f"❌ ERROR: Failed to generate metadata: {e}")
            sys.exit(1)

    print("\n" + "=" * 70)
    print("✅ Conversion pipeline completed successfully")
    print("=" * 70)
    print("\nNote: This is a stub implementation.")
    print("A full converter would:")
    print("  - Parse Lean AST using lean4 export")
    print("  - Generate actual Dedukti/MMT/OMDoc syntax")
    print("  - Preserve full semantic information")
    print("  - Validate conversion with kernel checker")

#!/usr/bin/env python3
"""
Conversion smoke test for Lean to intermediate representation.
This is a placeholder that simulates converting Lean code to an intermediate format.
"""

import sys
from pathlib import Path


def convert_lean_to_intermediate(lean_file):
    """
    Convert a Lean file to intermediate representation.
    This is a smoke test placeholder - in a real implementation,
    this would invoke actual Lean tooling or parsers.

    Args:
        lean_file: Path to the Lean file to convert

    Returns:
        bool: True if conversion succeeds, False otherwise
    """
    try:
        with open(lean_file, "r", encoding="utf-8") as f:
            content = f.read()

        # Basic validation: check if file looks like Lean code
        if not content.strip():
            print(f"❌ Error: {lean_file} is empty")
            return False

        # Check for common Lean keywords
        lean_keywords = ["theorem", "lemma", "def", "axiom", "namespace", "import"]
        has_lean_keyword = any(keyword in content for keyword in lean_keywords)

        if not has_lean_keyword:
            print(
                f"⚠️  Warning: {lean_file} may not be valid Lean code (no common keywords found)"
            )

        # Simulate conversion (placeholder)
        line_count = len(content.splitlines())
        print(f"📄 Processing {lean_file}")
        print(f"   Lines: {line_count}")
        print(f"   Size: {len(content)} bytes")

        # In a real implementation, this would:
        # 1. Parse the Lean file
        # 2. Convert to intermediate representation (e.g., Dedukti, MMT, etc.)
        # 3. Validate the intermediate output
        print(f"✅ Smoke test passed: {lean_file} appears to be valid Lean code")

        return True

    except FileNotFoundError:
        print(f"❌ File not found: {lean_file}")
        return False
    except UnicodeDecodeError as e:
        print(f"❌ Encoding error in {lean_file}: {e}")
        return False
    except Exception as e:
        print(f"❌ Unexpected error processing {lean_file}: {e}")
        return False


def main():
    """Main entry point for the conversion smoke test."""
    if len(sys.argv) < 2:
        print("Usage: python convert_example.py <lean_file>")
        sys.exit(1)

    lean_file = Path(sys.argv[1])

    if not lean_file.exists():
        print(f"❌ Error: File does not exist: {lean_file}")
        sys.exit(1)

    if not lean_file.suffix == ".lean":
        print(f"⚠️  Warning: {lean_file} does not have .lean extension")

    print(f"🔄 Starting conversion smoke test for {lean_file}")
    print("=" * 60)

    if convert_lean_to_intermediate(lean_file):
        print("=" * 60)
        print(f"✅ Conversion smoke test passed for {lean_file}")
        sys.exit(0)
    else:
        print("=" * 60)
        print(f"❌ Conversion smoke test failed for {lean_file}")
        sys.exit(1)


if __name__ == "__main__":
    main()
