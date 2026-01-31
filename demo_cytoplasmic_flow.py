#!/usr/bin/env python3
"""
Demonstration: Cytoplasmic Flow Model

This script demonstrates the connection between the Riemann Hypothesis
and biological tissue through Navier-Stokes equations in cytoplasmic flow.

Usage:
    python demo_cytoplasmic_flow.py

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
"""

from utils.cytoplasmic_flow_model import CytoplasmicFlowModel


def main():
    """Run the cytoplasmic flow demonstration."""
    print("\n" + "=" * 70)
    print("CYTOPLASMIC FLOW MODEL - RIEMANN HYPOTHESIS IN BIOLOGY")
    print("=" * 70 + "\n")
    
    # Create model with realistic cytoplasmic parameters
    model = CytoplasmicFlowModel(
        density=1000.0,           # kg/m³
        kinematic_viscosity=1e-6, # m²/s (100x water)
        length_scale=1e-6,        # m (1 micron)
        velocity=1e-8             # m/s
    )
    
    # Run demonstration
    model.print_demonstration()
    
    # Get results
    results = model.demonstrate_riemann_connection()
    
    print("\n📋 RESULTS SUMMARY:")
    print(f"   Reynolds Number: {results['reynolds_number']:.2e}")
    print(f"   Flow Coherence: {results['flow_coherence']:.6f}")
    print(f"   Hilbert-Pólya Operator Exists: {results['hilbert_polya_exists']}")
    print(f"   Riemann Connection: {results['riemann_connection_verified']}")
    print()


if __name__ == "__main__":
    main()
