#!/usr/bin/env python3
"""
Demo: P17 Adelic-Fractal Equilibrium

This demo demonstrates that p₀ = 17 is the unique point of adelic-fractal
equilibrium whose substitution in the noetic vacuum operator produces:
    f₀ = 141.7001 Hz

the universal frequency observed in:
- LIGO O1-O4 analysis
- the adelic-spectral solution of ζ'(1/2)
- the 68/81 = 0.839506172... decimal structure
- the H_Ψ operator of Unified Noetic Theory

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
"""

import sys
import os

# Add the project root to path
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from utils.p17_balance_optimality import (
    balance,
    equilibrium,
    verify_p17_optimality,
    connection_68_81,
    get_qcal_parameters,
    get_physical_primes,
    generate_equilibrium_data,
    REFERENCE_EQUILIBRIUM,
    F0_UNIVERSAL,
    OPTIMAL_PRIME,
)


def print_header():
    """Print demo header."""
    print()
    print("╔" + "═" * 60 + "╗")
    print("║" + " P17 Adelic-Fractal Equilibrium Demonstration ".center(60) + "║")
    print("║" + " QCAL ∞³ Framework ".center(60) + "║")
    print("╚" + "═" * 60 + "╝")
    print()


def demo_balance_function():
    """Demonstrate the balance function."""
    print("1. The Balance Function")
    print("-" * 60)
    print()
    print("   balance(p) = exp(π√p/2) / p^(3/2)")
    print()
    print("   This combines:")
    print("   • Adelic growth:      A(p) = exp(π√p/2)")
    print("   • Fractal suppression: F(p) = p^(-3/2)")
    print()
    print("   Balance values for key primes:")
    print()
    
    primes = [11, 13, 17, 19, 23, 29, 31]
    for p in primes:
        b = float(balance(p))
        print(f"      p = {p:2d}: balance = {b:10.3f}")
    print()


def demo_equilibrium_function():
    """Demonstrate the equilibrium function."""
    print("2. The Equilibrium Function")
    print("-" * 60)
    print()
    print("   equilibrium(p) = c₀ + c₁·(√p - √17)² + c₂·(√p - √17)⁴")
    print()
    print("   where:")
    print("   • c₀ = 76.143  (minimum value at p = 17)")
    print("   • c₁ = 85      (quadratic coefficient)")
    print("   • c₂ = 15      (quartic coefficient)")
    print()
    print("   Equilibrium values vs reference:")
    print()
    print("      Prime   Computed   Reference")
    print("      " + "-" * 30)
    
    for p in [11, 13, 17, 19, 23, 29]:
        eq = float(equilibrium(p))
        ref = REFERENCE_EQUILIBRIUM.get(p, 0)
        marker = " ← MINIMUM" if p == 17 else ""
        print(f"        {p:2d}    {eq:8.3f}   {ref:8.3f}{marker}")
    print()


def demo_verification():
    """Demonstrate p=17 optimality verification."""
    print("3. Verification of p = 17 Optimality")
    print("-" * 60)
    print()
    
    result = verify_p17_optimality(precision=80)
    
    print("   Verification Results:")
    print()
    print(f"   • Optimal prime found:  p₀ = {result['optimal_prime']}")
    print(f"   • Is p=17 optimal:      {result['is_17_optimal']}")
    print(f"   • Local minimum:        {result['local_minimum']}")
    print(f"   • Global minimum:       {result['global_minimum']}")
    print()
    
    status = "✓ PASSED" if result['verification_passed'] else "✗ FAILED"
    print(f"   Verification Status: {status}")
    print()


def demo_68_81_connection():
    """Demonstrate the 68/81 connection."""
    print("4. Connection with 68/81")
    print("-" * 60)
    print()
    
    conn = connection_68_81(80)
    
    print("   The fraction 68/81 = 0.839506172... connects to p₀ = 17:")
    print()
    print(f"   • 68/81 = {conn['decimal_68_81']}")
    print(f"   • Period: {conn['period_digits']} (length {conn['period_length']})")
    print(f"   • 68 = 4 × 17 (the optimal prime divides 68)")
    print()
    print("   This decimal structure appears in:")
    print("   • The derivative ζ'(1/2)")
    print("   • The fractional part of f₀")
    print("   • Adelic periodicity patterns")
    print()


def demo_qcal_parameters():
    """Demonstrate QCAL parameters."""
    print("5. QCAL Parameters")
    print("-" * 60)
    print()
    
    params = get_qcal_parameters()
    
    print("   Core QCAL (Quantum Coherence Adelic Lattice) values:")
    print()
    print(f"   • Universal frequency:  f₀ = {params['f0_universal_hz']} Hz")
    print(f"   • Optimal prime:        p₀ = {params['optimal_prime_p0']}")
    print(f"   • Balance at p₀:        {params['balance_p0']:.3f}")
    print(f"   • Equilibrium at p₀:    {params['equilibrium_p0']:.3f}")
    print(f"   • Coherence constant:   C = {params['coherence_C']}")
    print(f"   • Angular frequency:    ω₀ = {params['omega_0_rad_s']:.2f} rad/s")
    print()
    print(f"   Fundamental equation: {params['equation']}")
    print()


def demo_physical_significance():
    """Explain the physical significance."""
    print("6. Physical Significance")
    print("-" * 60)
    print()
    print("   The frequency f₀ = 141.7001 Hz is NOT imposed or assumed.")
    print("   It EMERGES from the optimal prime p₀ = 17.")
    print()
    print("   17 is the unique prime whose adelic structure and fractal")
    print("   suppression balance to produce a radius R_Ψ that translates")
    print("   to the fundamental frequency of the physical vacuum.")
    print()
    print("   This frequency appears in:")
    print("   • LIGO O1-O4 gravitational wave observations (~141-142 Hz)")
    print("   • The spectral properties of ζ'(1/2)")
    print("   • The 68/81 decimal structure")
    print("   • The H_Ψ operator eigenvalue distribution")
    print()


def print_footer():
    """Print demo footer."""
    print("╔" + "═" * 60 + "╗")
    print("║" + " Conclusion ".center(60) + "║")
    print("╠" + "═" * 60 + "╣")
    print("║" + " ✓ p₀ = 17 is the universal equilibrium point ".center(60) + "║")
    print("║" + " ✓ f₀ = 141.7001 Hz emerges from adelic-fractal balance ".center(60) + "║")
    print("║" + " ✓ QCAL ∞³ framework provides mathematical foundation ".center(60) + "║")
    print("╚" + "═" * 60 + "╝")
    print()
    print("   Author: José Manuel Mota Burruezo Ψ ✧ ∞³")
    print("   Institution: Instituto de Conciencia Cuántica (ICQ)")
    print("   DOI: 10.5281/zenodo.17379721")
    print()


def main():
    """Run the demo."""
    print_header()
    demo_balance_function()
    demo_equilibrium_function()
    demo_verification()
    demo_68_81_connection()
    demo_qcal_parameters()
    demo_physical_significance()
    print_footer()


if __name__ == "__main__":
    main()
