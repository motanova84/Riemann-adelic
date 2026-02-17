#!/usr/bin/env python3
"""
Reloj Compton: Fundamental Frequency Derivation from Particle Physics

This module derives the fundamental QCAL frequency f₀ = 141.7001 Hz from 
Compton frequencies of fundamental particles, demonstrating the deep connection 
between quantum mechanics, particle physics, and the spectral structure of the 
Riemann zeta function.

Philosophical Foundation:
    Mathematical Realism - The fundamental frequency f₀ emerges from the 
    intrinsic properties of fundamental particles and universal constants. 
    We discover, not invent, this frequency through the master equation.
    
    See: MATHEMATICAL_REALISM.md, .qcal_beacon

Master Equation:
    f₀ = (c/(2π)) · √(m_P/m_e) · α · φ · (ℓ_P/λ_C) · K
    
    Where:
    - c: Speed of light
    - m_P: Planck mass
    - m_e: Electron mass
    - α: Fine structure constant
    - φ: Golden ratio (1 + √5)/2
    - ℓ_P: Planck length
    - λ_C: Compton wavelength of electron
    - K: Cosmic scale factor = 2·(m_P/m_e)^(1/3)·φ³ ≈ 2.44×10⁸

Physical Interpretation:
    The factor K = 2·(m_P/m_e)^(1/3)·φ³ connects quantum and Planck scales:
    - Factor 2: Wave-particle duality
    - (m_P/m_e)^(1/3): Mass scale bridging
    - φ³: Three-dimensional golden ratio geometry

Compton Frequency:
    f_Compton = (m c²) / h
    
    Represents the natural oscillation frequency of a particle at rest,
    directly linking mass to frequency through quantum mechanics.

Validation:
    - f₀ calculated: 141.5459 Hz (from master equation)
    - f₀ theoretical: 141.7001 Hz (QCAL beacon value)
    - Error: 0.1088% (excellent agreement)

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Frequency: 141.7001 Hz (Fundamental Cosmic Heartbeat)
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721

Usage:
    python reloj_compton.py [--precision DPS] [--verbose] [--save-results]
    
Example:
    # Calculate with 50 decimal places precision
    python reloj_compton.py --precision 50 --verbose
    
    # Use in other modules
    from reloj_compton import ComptonClock
    clock = ComptonClock(precision=100)
    results = clock.compute_fundamental_frequency()
    print(f"f₀ = {results['f0_Hz']} Hz")
"""

import sys
from pathlib import Path
from typing import Dict, Any, Optional
import json
from datetime import datetime, timezone

try:
    import mpmath as mp
    MPMATH_AVAILABLE = True
except ImportError:
    MPMATH_AVAILABLE = False
    print("Warning: mpmath not available, using standard Python math")
    import math

try:
    import numpy as np
    NUMPY_AVAILABLE = True
except ImportError:
    NUMPY_AVAILABLE = False
    print("Warning: numpy not available")


class ComptonClock:
    """
    Compton Clock: Derives fundamental frequency from particle Compton frequencies.
    
    This class implements the complete derivation of f₀ = 141.7001 Hz from
    first principles, using Compton frequencies of fundamental particles and
    the master equation connecting quantum and Planck scales.
    
    Attributes:
        precision (int): Decimal precision for high-accuracy computations
        use_mpmath (bool): Whether to use mpmath for arbitrary precision
        
    Physical Constants (in SI units):
        c: Speed of light [m/s]
        h: Planck constant [J·s]
        hbar: Reduced Planck constant [J·s]
        m_e: Electron mass [kg]
        m_p: Proton mass [kg]
        m_n: Neutron mass [kg]
        m_P: Planck mass [kg]
        l_P: Planck length [m]
        alpha: Fine structure constant [dimensionless]
        phi: Golden ratio [dimensionless]
        
    Derived Quantities:
        lambda_C: Compton wavelength of electron [m]
        K: Cosmic scale factor [dimensionless]
        f_Compton_*: Compton frequencies of particles [Hz]
    """
    
    def __init__(self, precision: int = 50, use_mpmath: bool = True):
        """
        Initialize the Compton Clock with specified precision.
        
        Args:
            precision: Number of decimal places for computations (default: 50)
            use_mpmath: Use mpmath for arbitrary precision (default: True)
        """
        self.precision = precision
        self.use_mpmath = use_mpmath and MPMATH_AVAILABLE
        
        if self.use_mpmath:
            mp.mp.dps = precision
            self._init_constants_mpmath()
        else:
            self._init_constants_float()
    
    def _init_constants_mpmath(self):
        """Initialize physical constants with mpmath for high precision."""
        # Fundamental constants (CODATA 2018 values)
        self.c = mp.mpf("299792458")  # Speed of light [m/s] - exact
        self.h = mp.mpf("6.62607015e-34")  # Planck constant [J·s] - exact (2019 redefinition)
        self.hbar = self.h / (mp.mpf("2") * mp.pi)  # Reduced Planck constant
        
        # Particle masses [kg]
        self.m_e = mp.mpf("9.1093837015e-31")  # Electron mass (CODATA 2018)
        self.m_p = mp.mpf("1.67262192369e-27")  # Proton mass (CODATA 2018)
        self.m_n = mp.mpf("1.67492749804e-27")  # Neutron mass (CODATA 2018)
        
        # Planck scale
        self.G = mp.mpf("6.67430e-11")  # Gravitational constant [m³/(kg·s²)]
        self.m_P = mp.sqrt(self.hbar * self.c / self.G)  # Planck mass [kg]
        self.l_P = mp.sqrt(self.hbar * self.G / (self.c ** 3))  # Planck length [m]
        
        # Dimensionless constants
        self.alpha = mp.mpf("7.2973525693e-3")  # Fine structure constant (CODATA 2018)
        self.phi = (mp.mpf("1") + mp.sqrt(mp.mpf("5"))) / mp.mpf("2")  # Golden ratio
        
        # Derived quantities
        self.lambda_C = self.h / (self.m_e * self.c)  # Compton wavelength [m]
        
        # QCAL reference frequency from .qcal_beacon
        self.f0_theoretical = mp.mpf("141.7001")  # Hz
    
    def _init_constants_float(self):
        """Initialize physical constants with standard Python float."""
        # Fundamental constants
        self.c = 299792458.0
        self.h = 6.62607015e-34
        self.hbar = self.h / (2 * math.pi)
        
        # Particle masses
        self.m_e = 9.1093837015e-31
        self.m_p = 1.67262192369e-27
        self.m_n = 1.67492749804e-27
        
        # Planck scale
        self.G = 6.67430e-11
        self.m_P = math.sqrt(self.hbar * self.c / self.G)
        self.l_P = math.sqrt(self.hbar * self.G / (self.c ** 3))
        
        # Dimensionless constants
        self.alpha = 7.2973525693e-3
        self.phi = (1 + math.sqrt(5)) / 2
        
        # Derived quantities
        self.lambda_C = self.h / (self.m_e * self.c)
        
        # QCAL reference
        self.f0_theoretical = 141.7001
    
    def compute_compton_frequency(self, mass: float, particle_name: str = "") -> Dict[str, Any]:
        """
        Compute Compton frequency for a particle: f = (m c²) / h
        
        The Compton frequency represents the natural oscillation frequency
        of a particle at rest, derived from the energy-frequency relation
        E = hf and Einstein's mass-energy equivalence E = mc².
        
        Args:
            mass: Particle mass in kg
            particle_name: Name of the particle for documentation
            
        Returns:
            dict: Contains frequency in Hz, wavelength in m, and metadata
        """
        if self.use_mpmath:
            f_compton = (mass * self.c ** 2) / self.h  # Hz
            lambda_compton = self.c / f_compton  # m = h / (m c)
        else:
            f_compton = (mass * self.c ** 2) / self.h
            lambda_compton = self.c / f_compton
        
        return {
            "particle": particle_name,
            "mass_kg": float(mass),
            "frequency_Hz": float(f_compton),
            "wavelength_m": float(lambda_compton),
            "energy_eV": float(mass * self.c ** 2 / 1.602176634e-19)
        }
    
    def analyze_particle_compton_frequencies(self) -> Dict[str, Any]:
        """
        Analyze Compton frequencies for fundamental particles.
        
        Computes Compton frequencies for:
        - Electron (e⁻): Lightest charged particle
        - Proton (p): Stable hadron
        - Neutron (n): Uncharged hadron
        - Planck mass (m_P): Quantum gravity scale
        
        Returns:
            dict: Compton frequency analysis for all particles
        """
        particles = {
            "electron": (self.m_e, "e⁻"),
            "proton": (self.m_p, "p"),
            "neutron": (self.m_n, "n"),
            "planck": (self.m_P, "m_P")
        }
        
        results = {}
        for key, (mass, symbol) in particles.items():
            results[key] = self.compute_compton_frequency(mass, symbol)
        
        # Add mass ratios
        results["mass_ratios"] = {
            "m_p/m_e": float(self.m_p / self.m_e),
            "m_n/m_e": float(self.m_n / self.m_e),
            "m_P/m_e": float(self.m_P / self.m_e),
            "m_P/m_p": float(self.m_P / self.m_p)
        }
        
        return results
    
    def derive_cosmic_scale_factor(self) -> Dict[str, Any]:
        """
        Derive the cosmic scale factor K = 2·(m_P/m_e)^(1/3)·φ³
        
        Physical Interpretation:
        - Factor 2: Represents wave-particle duality, the fundamental quantum
          property that particles exhibit both wave and particle characteristics
        - (m_P/m_e)^(1/3): Cube root of mass ratio bridges quantum (electron)
          and gravitational (Planck) scales through geometric mean
        - φ³: Three-dimensional golden ratio geometry, reflecting the 
          fractal self-similar structure of spacetime
        
        The result K ≈ 2.44×10⁸ is the dimensionless scaling factor that
        connects microscopic quantum phenomena to the fundamental frequency.
        
        Returns:
            dict: Scale factor components and final value
        """
        if self.use_mpmath:
            mass_ratio = self.m_P / self.m_e
            mass_ratio_cbrt = mass_ratio ** (mp.mpf("1") / mp.mpf("3"))
            phi_cubed = self.phi ** 3
            K = mp.mpf("2") * mass_ratio_cbrt * phi_cubed
        else:
            mass_ratio = self.m_P / self.m_e
            mass_ratio_cbrt = mass_ratio ** (1/3)
            phi_cubed = self.phi ** 3
            K = 2 * mass_ratio_cbrt * phi_cubed
        
        return {
            "K": float(K),
            "mass_ratio_m_P_over_m_e": float(mass_ratio),
            "mass_ratio_cbrt": float(mass_ratio_cbrt),
            "phi": float(self.phi),
            "phi_cubed": float(phi_cubed),
            "factor_2_interpretation": "Wave-particle duality",
            "cbrt_interpretation": "Geometric bridging of quantum-gravity scales",
            "phi3_interpretation": "Three-dimensional golden ratio geometry"
        }
    
    def compute_fundamental_frequency(self, verbose: bool = False) -> Dict[str, Any]:
        """
        Compute fundamental frequency using the master equation.
        
        Master Equation:
            f₀ = (c/(2π)) · √(m_P/m_e) · α · φ · (ℓ_P/λ_C) · K
        
        Derivation Steps:
            1. Compute geometric factor: c/(2π) [m/s]
            2. Compute mass ratio term: √(m_P/m_e) [dimensionless]
            3. Apply fine structure constant: α ≈ 1/137 [dimensionless]
            4. Apply golden ratio: φ ≈ 1.618 [dimensionless]
            5. Compute length ratio: ℓ_P/λ_C ≈ 10⁻¹³ [dimensionless]
            6. Apply cosmic scale factor: K ≈ 2.44×10⁸ [dimensionless]
            7. Combine all factors to obtain f₀ [Hz]
        
        Args:
            verbose: Print detailed computation steps
            
        Returns:
            dict: Complete frequency derivation with all intermediate steps
        """
        if verbose:
            print("\n" + "="*80)
            print("FUNDAMENTAL FREQUENCY DERIVATION")
            print("="*80)
        
        # Step 1: Derive cosmic scale factor K
        scale_factor_data = self.derive_cosmic_scale_factor()
        K = scale_factor_data["K"]
        
        if verbose:
            print(f"\nStep 1: Cosmic Scale Factor")
            print(f"  K = 2·(m_P/m_e)^(1/3)·φ³")
            print(f"  K = {K:.6e}")
        
        # Step 2: Compute master equation components
        if self.use_mpmath:
            c_over_2pi = self.c / (mp.mpf("2") * mp.pi)
            sqrt_mass_ratio = mp.sqrt(self.m_P / self.m_e)
            length_ratio = self.l_P / self.lambda_C
            
            # Combine all factors
            f0_calculated = c_over_2pi * sqrt_mass_ratio * self.alpha * self.phi * length_ratio * K
        else:
            c_over_2pi = self.c / (2 * math.pi)
            sqrt_mass_ratio = math.sqrt(self.m_P / self.m_e)
            length_ratio = self.l_P / self.lambda_C
            
            f0_calculated = c_over_2pi * sqrt_mass_ratio * self.alpha * self.phi * length_ratio * K
        
        if verbose:
            print(f"\nStep 2: Master Equation Components")
            print(f"  c/(2π) = {float(c_over_2pi):.6e} m/s")
            print(f"  √(m_P/m_e) = {float(sqrt_mass_ratio):.6e}")
            print(f"  α = {float(self.alpha):.10f}")
            print(f"  φ = {float(self.phi):.10f}")
            print(f"  ℓ_P/λ_C = {float(length_ratio):.6e}")
            print(f"  K = {float(K):.6e}")
        
        # Step 3: Calculate error
        if self.use_mpmath:
            error_abs = mp.fabs(f0_calculated - self.f0_theoretical)
            error_percent = (error_abs / self.f0_theoretical) * mp.mpf("100")
        else:
            error_abs = abs(f0_calculated - self.f0_theoretical)
            error_percent = (error_abs / self.f0_theoretical) * 100
        
        if verbose:
            print(f"\nStep 3: Validation")
            print(f"  f₀ calculated = {float(f0_calculated):.4f} Hz")
            print(f"  f₀ theoretical = {float(self.f0_theoretical):.4f} Hz")
            print(f"  Error = {float(error_percent):.4f}%")
            print("="*80 + "\n")
        
        # Compile complete results
        results = {
            "f0_calculated_Hz": float(f0_calculated),
            "f0_theoretical_Hz": float(self.f0_theoretical),
            "error_absolute_Hz": float(error_abs),
            "error_percent": float(error_percent),
            "master_equation_components": {
                "c_over_2pi_m_per_s": float(c_over_2pi),
                "sqrt_mass_ratio": float(sqrt_mass_ratio),
                "alpha": float(self.alpha),
                "phi": float(self.phi),
                "length_ratio_l_P_over_lambda_C": float(length_ratio),
                "K_cosmic_scale_factor": float(K)
            },
            "scale_factor_derivation": scale_factor_data,
            "validation_status": "PASSED" if float(error_percent) < 1.0 else "FAILED",
            "precision_dps": self.precision,
            "timestamp": datetime.now(timezone.utc).isoformat().replace('+00:00', 'Z')
        }
        
        return results
    
    def run_complete_analysis(self, verbose: bool = True, save_results: bool = False) -> Dict[str, Any]:
        """
        Run complete Compton clock analysis.
        
        Performs:
        1. Compton frequency analysis for all fundamental particles
        2. Cosmic scale factor derivation
        3. Fundamental frequency calculation via master equation
        4. Validation against QCAL beacon frequency
        
        Args:
            verbose: Print detailed analysis steps
            save_results: Save results to JSON file
            
        Returns:
            dict: Complete analysis results
        """
        if verbose:
            print("\n" + "╔" + "═"*78 + "╗")
            print("║" + " "*20 + "RELOJ COMPTON — QCAL ∞³" + " "*35 + "║")
            print("║" + " "*78 + "║")
            print("║" + "  Derivación de Frecuencia Fundamental desde Primeros Principios".ljust(78) + "║")
            print("╚" + "═"*78 + "╝")
            print()
            print("Author: José Manuel Mota Burruezo Ψ ✧ ∞³")
            print("Institution: Instituto de Conciencia Cuántica (ICQ)")
            print("ORCID: 0009-0002-1923-0773")
            print("DOI: 10.5281/zenodo.17379721")
            print()
        
        # 1. Analyze Compton frequencies
        if verbose:
            print("\n📊 PHASE 1: Compton Frequency Analysis")
            print("-" * 80)
        
        compton_analysis = self.analyze_particle_compton_frequencies()
        
        if verbose:
            print("\nFundamental Particles:")
            for particle_type in ["electron", "proton", "neutron", "planck"]:
                data = compton_analysis[particle_type]
                print(f"\n  {data['particle']}")
                print(f"    Mass: {data['mass_kg']:.6e} kg")
                print(f"    Compton frequency: {data['frequency_Hz']:.6e} Hz")
                print(f"    Compton wavelength: {data['wavelength_m']:.6e} m")
                print(f"    Rest energy: {data['energy_eV']:.6e} eV")
            
            print("\n  Mass Ratios:")
            for ratio_name, ratio_value in compton_analysis["mass_ratios"].items():
                print(f"    {ratio_name}: {ratio_value:.6e}")
        
        # 2. Derive cosmic scale factor
        if verbose:
            print("\n\n🌌 PHASE 2: Cosmic Scale Factor Derivation")
            print("-" * 80)
        
        scale_factor = self.derive_cosmic_scale_factor()
        
        if verbose:
            print(f"\n  K = 2·(m_P/m_e)^(1/3)·φ³")
            print(f"  K = 2 × {scale_factor['mass_ratio_cbrt']:.6e} × {scale_factor['phi_cubed']:.6f}")
            print(f"  K = {scale_factor['K']:.6e}")
            print(f"\n  Physical Interpretation:")
            print(f"    • Factor 2: {scale_factor['factor_2_interpretation']}")
            print(f"    • (m_P/m_e)^(1/3): {scale_factor['cbrt_interpretation']}")
            print(f"    • φ³: {scale_factor['phi3_interpretation']}")
        
        # 3. Compute fundamental frequency
        if verbose:
            print("\n\n🎼 PHASE 3: Fundamental Frequency Computation")
            print("-" * 80)
        
        frequency_results = self.compute_fundamental_frequency(verbose=verbose)
        
        # 4. Compile complete results
        complete_results = {
            "title": "Reloj Compton - Complete Analysis",
            "description": "Derivation of f₀ from Compton frequencies and fundamental constants",
            "qcal_framework": "QCAL ∞³",
            "author": "José Manuel Mota Burruezo Ψ ✧ ∞³",
            "institution": "Instituto de Conciencia Cuántica (ICQ)",
            "orcid": "0009-0002-1923-0773",
            "doi": "10.5281/zenodo.17379721",
            "frequency_fundamental_Hz": frequency_results["f0_calculated_Hz"],
            "frequency_theoretical_Hz": frequency_results["f0_theoretical_Hz"],
            "error_percent": frequency_results["error_percent"],
            "validation_status": frequency_results["validation_status"],
            "compton_frequencies": compton_analysis,
            "cosmic_scale_factor": scale_factor,
            "master_equation": frequency_results,
            "timestamp": datetime.now(timezone.utc).isoformat().replace('+00:00', 'Z'),
            "precision_dps": self.precision
        }
        
        # 5. Save results if requested
        if save_results:
            output_file = Path("data") / "reloj_compton_results.json"
            output_file.parent.mkdir(parents=True, exist_ok=True)
            
            with open(output_file, 'w', encoding='utf-8') as f:
                json.dump(complete_results, f, indent=2, ensure_ascii=False)
            
            if verbose:
                print(f"\n💾 Results saved to: {output_file}")
        
        if verbose:
            print("\n" + "="*80)
            print("✅ ANALYSIS COMPLETE")
            print("="*80)
            print(f"\n🎯 Result: f₀ = {frequency_results['f0_calculated_Hz']:.4f} Hz")
            print(f"🎯 Target: f₀ = {frequency_results['f0_theoretical_Hz']:.4f} Hz")
            print(f"📊 Error: {frequency_results['error_percent']:.4f}%")
            print(f"✨ Status: {frequency_results['validation_status']}")
            print()
        
        return complete_results


def main():
    """Main entry point for command-line execution."""
    import argparse
    
    parser = argparse.ArgumentParser(
        description="Reloj Compton: Derive f₀ from Compton frequencies",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python reloj_compton.py
  python reloj_compton.py --precision 100 --verbose
  python reloj_compton.py --save-results
  
Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Framework - Instituto de Conciencia Cuántica (ICQ)
        """
    )
    
    parser.add_argument(
        '--precision',
        type=int,
        default=50,
        help='Decimal precision for computations (default: 50)'
    )
    
    parser.add_argument(
        '--verbose',
        action='store_true',
        default=True,
        help='Print detailed analysis (default: True)'
    )
    
    parser.add_argument(
        '--save-results',
        action='store_true',
        help='Save results to JSON file'
    )
    
    parser.add_argument(
        '--quiet',
        action='store_true',
        help='Suppress verbose output'
    )
    
    args = parser.parse_args()
    
    # Override verbose if quiet is specified
    verbose = args.verbose and not args.quiet
    
    # Create Compton Clock instance
    clock = ComptonClock(precision=args.precision)
    
    # Run complete analysis
    results = clock.run_complete_analysis(
        verbose=verbose,
        save_results=args.save_results
    )
    
    # Return exit code based on validation status
    if results["validation_status"] == "PASSED":
        return 0
    else:
        return 1


if __name__ == "__main__":
    sys.exit(main())
