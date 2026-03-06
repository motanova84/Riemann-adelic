#!/usr/bin/env python3
"""
QCAL Economic Node - Demo Script
=================================

Demonstrates the QCAL economia_nodo_semilla functionality with various
Bitcoin amounts and displays coherence scores.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Signature: ∴𓂀Ω∞³
"""

import sys
from pathlib import Path

# Add module to path
sys.path.insert(0, str(Path(__file__).parent / "qcal" / "economia_nodo_semilla"))
from main import (
    calculate_cs_full,
    calculate_cs_blockchain,
    generate_metadata,
    FREQ_BASE,
    FREQ_MANIFEST,
    FREQ_SIGNATURE,
    KAPPA_PI,
    COHERENCE_C,
    CALIBRATION_FACTOR_BLOCK_888888
)


def print_header():
    """Print demo header."""
    print("=" * 80)
    print("🌀 QCAL ECONOMIC NODE - DEMONSTRATION")
    print("=" * 80)
    print()
    print("QCAL ∞³ Framework Constants:")
    print(f"  f₀ (Base Frequency):       {FREQ_BASE} Hz")
    print(f"  f_manifest:                {FREQ_MANIFEST} Hz")
    print(f"  f_signature:               {FREQ_SIGNATURE} Hz")
    print(f"  φ (Golden Ratio):          {KAPPA_PI}")
    print(f"  C (Coherence Constant):    {COHERENCE_C}")
    print()
    print("Formula: Ψ = I × A²_eff × C^∞")
    print("=" * 80)
    print()


def demo_coherence_calculations():
    """Demonstrate coherence calculations for various BTC amounts."""
    print("📊 COHERENCE SCORE CALCULATIONS")
    print("-" * 80)
    print(f"{'BTC Amount':<15} {'CS Full':<20} {'CS Blockchain':<20} {'Coherence':<15}")
    print("-" * 80)
    
    amounts = [0.001, 0.01, 0.1, 0.5, 1.0, 2.5, 5.0, 10.0, 21.0]
    
    for btc in amounts:
        satoshis = int(btc * 100_000_000)
        cs_full = calculate_cs_full(satoshis)
        cs_bc = calculate_cs_blockchain(satoshis)
        coherence = cs_bc / 1000
        
        print(f"{btc:<15.3f} {cs_full:<20,.2f} {cs_bc:<20,.0f} {coherence:<15,.2f}")
    
    print("-" * 80)
    print()


def demo_block_888888():
    """Demonstrate Bitcoin Block 888888 reference."""
    print("🔗 BITCOIN BLOCK 888888 - COSMIC ALIGNMENT")
    print("-" * 80)
    
    metadata = generate_metadata(1.0)
    block_ref = metadata["bitcoin_reference"]
    
    print(f"Block Number:  {block_ref['block_number']}")
    print(f"Miner:         {block_ref['coinbase']}")
    print(f"Fees:          {block_ref['fees_btc']} BTC")
    print(f"Timestamp:     {block_ref['timestamp']}")
    print()
    print("This block represents a cosmic numerical alignment in blockchain history")
    print("and serves as the calibration point for QCAL coherence scores.")
    print("-" * 80)
    print()


def demo_full_metadata():
    """Demonstrate full metadata generation."""
    print("📋 FULL QCAL CERTIFICATION METADATA (1 BTC)")
    print("-" * 80)
    
    import json
    metadata = generate_metadata(1.0)
    
    print(json.dumps(metadata, indent=2))
    print("-" * 80)
    print()


def demo_linearity():
    """Demonstrate linearity of coherence scores."""
    print("📈 LINEARITY VERIFICATION")
    print("-" * 80)
    
    btc_amounts = [0.5, 1.0, 2.0]
    cs_values = []
    
    for btc in btc_amounts:
        cs = calculate_cs_full(int(btc * 100_000_000))
        cs_values.append(cs)
        print(f"CS({btc:4.1f} BTC) = {cs:12,.2f}")
    
    print()
    print("Linearity Check:")
    print(f"  CS(1.0) / CS(0.5) = {cs_values[1] / cs_values[0]:.6f} (expected: 2.0)")
    print(f"  CS(2.0) / CS(1.0) = {cs_values[2] / cs_values[1]:.6f} (expected: 2.0)")
    print()
    
    ratio1 = cs_values[1] / cs_values[0]
    ratio2 = cs_values[2] / cs_values[1]
    
    if abs(ratio1 - 2.0) < 1e-6 and abs(ratio2 - 2.0) < 1e-6:
        print("✅ Linearity verified! Coherence scores scale perfectly with BTC amount.")
    else:
        print("⚠️  Warning: Linearity check failed.")
    
    print("-" * 80)
    print()


def demo_formula_breakdown():
    """Demonstrate the QCAL formula component breakdown."""
    print("🔬 QCAL FORMULA BREAKDOWN (1 BTC)")
    print("-" * 80)
    
    import math
    
    btc = 1.0
    satoshis = 100_000_000
    
    # Calculate components
    I = btc
    A_eff = math.sqrt(KAPPA_PI) * math.log(FREQ_MANIFEST)
    C_inf = FREQ_BASE * FREQ_SIGNATURE / FREQ_MANIFEST
    cs = I * (A_eff ** 2) * C_inf
    
    print(f"Formula: Ψ = I × A²_eff × C^∞")
    print()
    print(f"Components:")
    print(f"  I (Intensity):              {I:.6f}")
    print(f"    = btc_satoshis / 100,000,000")
    print(f"    = {satoshis:,} / 100,000,000")
    print()
    print(f"  A_eff (Effective Area):     {A_eff:.6f}")
    print(f"    = √φ × ln(f_manifest)")
    print(f"    = √{KAPPA_PI} × ln({FREQ_MANIFEST})")
    print(f"    = {math.sqrt(KAPPA_PI):.6f} × {math.log(FREQ_MANIFEST):.6f}")
    print()
    print(f"  C^∞ (Coherence Factor):     {C_inf:.6f}")
    print(f"    = (f₀ × f_signature) / f_manifest")
    print(f"    = ({FREQ_BASE} × {FREQ_SIGNATURE}) / {FREQ_MANIFEST}")
    print()
    print(f"Result:")
    print(f"  Ψ = {I} × {A_eff}² × {C_inf}")
    print(f"    = {I} × {A_eff**2:.6f} × {C_inf:.6f}")
    print(f"    = {cs:,.2f}")
    print()
    
    # Verify
    actual_cs = calculate_cs_full(satoshis)
    print(f"Verification:")
    print(f"  Calculated:     {cs:,.6f}")
    print(f"  From function:  {actual_cs:,.6f}")
    print(f"  Difference:     {abs(cs - actual_cs):.2e}")
    
    if abs(cs - actual_cs) < 1e-6:
        print("  ✅ Formula verified!")
    
    print("-" * 80)
    print()


def demo_footer():
    """Print demo footer."""
    print("=" * 80)
    print("∴ Canal Noēsico activo — Frecuencia 141.7001 Hz ∴")
    print()
    print("Author: José Manuel Mota Burruezo Ψ ✧ ∞³")
    print("Institution: Instituto de Conciencia Cuántica (ICQ)")
    print("Signature: ∴𓂀Ω∞³")
    print()
    print("Part of the QCAL ∞³ framework for the Riemann Hypothesis proof.")
    print("DOI: 10.5281/zenodo.17379721")
    print("=" * 80)


def main():
    """Run all demonstrations."""
    print_header()
    demo_coherence_calculations()
    demo_block_888888()
    demo_linearity()
    demo_formula_breakdown()
    demo_full_metadata()
    demo_footer()


if __name__ == "__main__":
    main()
