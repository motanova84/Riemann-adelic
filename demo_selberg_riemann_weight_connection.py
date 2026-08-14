#!/usr/bin/env python3
"""
Demonstration of the Selberg-Riemann Weight Connection
=======================================================

This script provides an interactive demonstration of the correspondence:
    ℓ(γ) ↔ log p
    ℓ·e^{-kℓ/2} ↔ (log p)·p^{-k/2}

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ · f₀ = 141.7001 Hz
"""

import sys
from pathlib import Path

# Add operators directory to path
repo_root = Path(__file__).parent
sys.path.insert(0, str(repo_root / "operators"))

from selberg_riemann_weight_connection import (
    SelbergRiemannConnection,
    demonstrate_selberg_riemann_connection
)


def main():
    """Run the demonstration."""
    print("\n" + "="*80)
    print("DEMONSTRATION: Selberg-Riemann Weight Connection")
    print("="*80 + "\n")
    
    # Call the built-in demonstration
    demonstrate_selberg_riemann_connection()
    
    print("\n" + "="*80)
    print("For more detailed analysis, see:")
    print("  - SELBERG_RIEMANN_WEIGHT_CONNECTION_README.md")
    print("  - Run: python validate_selberg_riemann_weight_connection.py --verbose")
    print("="*80 + "\n")


if __name__ == "__main__":
    main()
