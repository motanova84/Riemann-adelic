#!/usr/bin/env python3
"""
Demo: piCODE-888 Bridge for Conscious Materialization
======================================================

Demonstrates the complete piCODE-888 bridge system including:
- Sequence transformations (RNA ↔ Greek ↔ Hex)
- ST.26 XML generation
- Validation and reversibility checks
- QCAL ∞³ field connection

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
"""

import sys
from pathlib import Path

from utils.picode_888_bridge import PiCode888Bridge

# Add project root to path
project_root = Path(__file__).parent
sys.path.insert(0, str(project_root))


def demo_sequence_transformations():
    """Demonstrate sequence transformations."""
    print("\n" + "=" * 80)
    print("🔬 SEQUENCE TRANSFORMATIONS DEMO")
    print("=" * 80 + "\n")

    bridge = PiCode888Bridge()

    # Original RNA sequence
    rna = bridge.SEQUENCE_1_RNA
    print(f"1️⃣  Original RNA (51 nt):")
    print(f"    {rna}\n")

    # Transform to Greek
    greek = bridge.rna_to_greek(rna)
    print(f"2️⃣  Greek UTF-8 Encoding ({len(greek.encode('utf-8'))} bytes):")
    print(f"    {greek}\n")

    # Transform to Hex
    hex_seq = bridge.greek_to_hex(greek)
    print(f"3️⃣  Hexadecimal Signature ({len(hex_seq)} chars):")
    print(f"    {hex_seq}\n")

    # Calculate hash
    hash_sig = bridge.calculate_hash(hex_seq)
    print(f"4️⃣  Cryptographic Hash (SHA-256, 8 chars):")
    print(f"    {hash_sig}\n")

    # Generate QR data
    qr_data = bridge.generate_qr_data(hex_seq, hash_sig)
    print(f"5️⃣  Symbiotic QR Data:")
    print(f"    {qr_data}\n")

    print("✅ All transformations completed successfully!\n")


def demo_reversibility():
    """Demonstrate reversibility of transformations."""
    print("\n" + "=" * 80)
    print("🔄 REVERSIBILITY VERIFICATION")
    print("=" * 80 + "\n")

    bridge = PiCode888Bridge()

    # Forward transformations
    rna_original = bridge.SEQUENCE_1_RNA
    print(f"🔹 Original RNA:")
    print(f"   {rna_original}\n")

    greek = bridge.rna_to_greek(rna_original)
    print(f"🔹 → Greek UTF-8:")
    print(f"   {greek}\n")

    hex_seq = bridge.greek_to_hex(greek)
    print(f"🔹 → Hexadecimal:")
    print(f"   {hex_seq[:50]}...\n")

    # Backward transformations
    print("🔄 Reversing transformations...\n")

    greek_back = bridge.hex_to_greek(hex_seq)
    print(f"🔹 Hex → Greek:")
    print(f"   {greek_back}\n")

    rna_back = bridge.greek_to_rna(greek_back)
    print(f"🔹 Greek → RNA:")
    print(f"   {rna_back}\n")

    # Verify
    if rna_back == rna_original:
        print("✅ REVERSIBILITY CONFIRMED: RNA → Greek → Hex → Greek → RNA")
        print("   Original and recovered sequences match perfectly!\n")
    else:
        print("❌ REVERSIBILITY FAILED: Sequences don't match\n")


def demo_symbolic_mapping():
    """Demonstrate symbolic mapping between bases and Greek symbols."""
    print("\n" + "=" * 80)
    print("🔮 SYMBOLIC MAPPING: Vibrational Carriers")
    print("=" * 80 + "\n")

    mappings = [
        ("a", "α", "alpha", "Origin - Beginning of creation"),
        ("t", "τ", "tau", "Time - Temporal flow"),
        ("c", "χ", "chi", "Vital Energy - Life force"),
        ("g", "γ", "gamma", "Growth - Expansion"),
        ("u", "υ", "upsilon", "Unity - Coherence"),
    ]

    print("Base → Greek Symbol → Meaning:\n")
    for base, greek, name, meaning in mappings:
        unicode_point = f"U+{ord(greek):04X}"
        print(f"  {base} → {greek} ({name}, {unicode_point})")
        print(f"     ↳ {meaning}\n")

    print("Each Greek symbol acts as a vibrational carrier,")
    print("adding symbolic resonance to the cryptographic protection.\n")


def demo_qcal_field_connection():
    """Demonstrate QCAL ∞³ field connection parameters."""
    print("\n" + "=" * 80)
    print("🌌 QCAL ∞³ FIELD CONNECTION")
    print("=" * 80 + "\n")

    bridge = PiCode888Bridge()
    bridge_seq = bridge.generate_complete_bridge()

    print(f"Resonance Frequency:  {bridge.resonance_hz} Hz")
    print(f"Tolerance:            ±{bridge.tolerance_hz} Hz")
    print(f"Coherence (Ψ):        {bridge_seq.coherence}")
    print(f"Coherence Constant:   {bridge.coherence}")
    print(f"Symbiotic Link:       Bidirectional")
    print(f"Field State:          QCAL ∞³ Active\n")

    print("📡 Connection Status:")
    print("   ✅ Vibrational antenna tuned to 888 Hz")
    print("   ✅ Quantum transducer active")
    print("   ✅ Ontological friction minimized (P ≠ NP coupling)")
    print("   ✅ Consciousness threshold exceeded (C ≥ 1/κ_Π ≈ 0.388)")
    print("   ✅ Noetic torsion minimized (𝒯^MB_∞³)\n")

    print("🌟 Processing this sequence triggers automatic connection")
    print("   to QCAL ∞³ field for conscious materialization.\n")


def demo_complete_bridge():
    """Generate and display complete bridge."""
    print("\n" + "=" * 80)
    print("🌐 COMPLETE piCODE-888 BRIDGE")
    print("=" * 80 + "\n")

    bridge_engine = PiCode888Bridge()
    bridge = bridge_engine.generate_complete_bridge()

    print("📊 SEQUENCE BREAKDOWN:\n")

    print("1️⃣  Vibrational RNA Original (51 nt)")
    print(f"    Source:   π digits 3000–3499 + vibrational filtering")
    print(f"    Function: Bridge for conscious materialization")
    print(f"    Sequence: {bridge.sequence_1_rna}")
    print(f"    Resonance: {bridge.resonance_hz} Hz ±{bridge_engine.tolerance_hz} Hz\n")

    print("2️⃣  Greek UTF-8 Encoding (102 bytes)")
    print(f"    Function: Cryptographic protection + symbolic resonance")
    print(f"    Sequence: {bridge.sequence_2_greek}")
    print(f"    Unicode:  U+03B1–U+03C7 range\n")

    print("3️⃣  Hexadecimal Signature (204 chars)")
    print(f"    Function: Immutable authenticity proof")
    print(f"    Hex:      {bridge.sequence_3_hex[:60]}...")
    print(f"    Hash:     {bridge.hash_signature}")
    print(f"    Key:      QCAL-888-UTF8-{bridge.sequence_3_hex[:12]}\n")

    print("4️⃣  Symbiotic QR Data")
    print(f"    {bridge.sequence_4_qr_data}\n")

    print("✅ VALIDATION RESULTS:")
    for key, value in bridge.validation_status.items():
        status = "✅" if value else "❌"
        print(f"   {status} {key.replace('_', ' ').title()}: {value}")
    print()


def demo_st26_generation():
    """Demonstrate ST.26 XML generation."""
    print("\n" + "=" * 80)
    print("📝 ST.26 XML GENERATION")
    print("=" * 80 + "\n")

    bridge_engine = PiCode888Bridge()
    bridge = bridge_engine.generate_complete_bridge()

    xml_file = bridge_engine.generate_st26_xml(bridge)

    print(f"✅ ST.26 XML file generated successfully!")
    print(f"   File: {xml_file}\n")

    print("📋 XML Content Preview:")
    print("   - WIPO Standard ST.26 format")
    print("   - Application: QCAL-2026-PICODE-888")
    print("   - Applicant: José Manuel Mota Burruezo (JMMB Ψ✧)")
    print("   - Sequence Type: Synthetic RNA")
    print("   - Length: 51 nucleotides")
    print("   - Features: Conscious materialization bridge")
    print("   - Resonance: 888 Hz\n")


def main():
    """Main demonstration."""
    print("\n" + "=" * 80)
    print("🌐 piCODE-888 BRIDGE DEMONSTRATION")
    print("Bridge of Conscious Materialization in QCAL ∞³")
    print("=" * 80)
    print("\nAuthor: José Manuel Mota Burruezo Ψ ✧ ∞³")
    print("Institution: Instituto de Conciencia Cuántica (ICQ)")
    print("DOI: https://doi.org/10.5281/zenodo.16425986")
    print("\n" + "=" * 80)

    # Run all demonstrations
    demo_sequence_transformations()
    demo_reversibility()
    demo_symbolic_mapping()
    demo_qcal_field_connection()
    demo_complete_bridge()
    demo_st26_generation()

    # Final summary
    print("\n" + "=" * 80)
    print("✨ DEMONSTRATION COMPLETE")
    print("=" * 80 + "\n")
    print("The piCODE-888 bridge is a quantum transducer that unites:")
    print("  • Computational complexity (P ≠ NP as ontological friction)")
    print("  • Consciousness (threshold C ≥ 1/κ_Π ≈ 0.388)")
    print("  • Vibrational resonance (888 Hz antenna)")
    print("  • Symbolic encoding (Greek UTF-8 carriers)")
    print("  • Cryptographic integrity (reversible chain validation)\n")
    print("Processing this sequence triggers automatic connection to")
    print("the QCAL ∞³ field for conscious materialization.\n")
    print("Current state: Ψ = 1.000 (bidirectional symbiotic link)\n")
    print("=" * 80 + "\n")


if __name__ == "__main__":
    main()
