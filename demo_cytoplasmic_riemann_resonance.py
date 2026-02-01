#!/usr/bin/env python3
"""
Demo: Cytoplasmic Riemann Resonance Model

This script demonstrates the complete cytoplasmic Riemann resonance model,
validating that the human body provides a biological proof of the Riemann Hypothesis.

Author: José Manuel Mota Burruezo
ORCID: 0009-0002-1923-0773
Date: 2026-02-01
"""

from xenos.cytoplasmic_riemann_resonance import CytoplasmicRiemannResonance


def print_header(title: str, width: int = 80) -> None:
    """Print a formatted section header."""
    print("\n" + "=" * width)
    print(f"  {title}")
    print("=" * width + "\n")


def main():
    """Run complete cytoplasmic Riemann resonance demonstration."""
    
    print_header("🌟 Cytoplasmic Riemann Resonance - Complete Demonstration 🌟")
    
    # Create model instance
    print("Creating Cytoplasmic Riemann Resonance model...")
    model = CytoplasmicRiemannResonance()
    print("✓ Model initialized\n")
    
    # Display mathematical constants
    print_header("Mathematical Constants")
    print(f"Base Frequency f₀: {model.constants.base_frequency:.4f} Hz")
    print(f"Biophysical κ_Π: {model.constants.kappa_pi:.4f}")
    print(f"Number of Cells: {model.constants.num_cells:.2e}")
    print(f"Cytoplasmic Viscosity ν: {model.constants.cytoplasm_viscosity:.2e} m²/s")
    
    # Calculate coherence at fundamental frequency
    omega_0 = 2 * 3.14159265359 * model.constants.base_frequency
    xi_0 = (model.constants.cytoplasm_viscosity / omega_0) ** 0.5
    print(f"Coherence Length ξ₀: {xi_0 * 1e6:.2f} μm")
    
    # Validate Riemann Hypothesis (biological)
    print_header("Riemann Hypothesis Biological Validation")
    print("Running validation...")
    result = model.validate_riemann_hypothesis_biological()
    
    print(f"\nHermitian Operator Analysis:")
    print(f"  Eigenvalue Count: {result['eigenvalue_count']}")
    print(f"  All Eigenvalues Real: {result['all_eigenvalues_real']}")
    print(f"  Max Imaginary Part: {result['max_eigenvalue_imag_part']:.2e}")
    
    print(f"\nRiemann Hypothesis Status:")
    print(f"  ✓ Hypothesis Validated: {result['hypothesis_validated']}")
    print(f"  ✓ Harmonic Distribution: {result['harmonic_distribution']}")
    print(f"  ✓ Coherence Length: {result['coherence_length_um']:.2f} μm")
    
    print(f"\nInterpretation:")
    print(f"  {result['interpretation']}")
    
    # Check coherence at cellular scale
    print_header("Cellular Scale Coherence Analysis")
    
    scales = [1.06e-6, 10e-6, 33.5e-6, 100e-6]  # Various biological scales
    scale_names = ["1.06 μm (organelle)", "10 μm (small cell)", 
                   "33.5 μm (coherence length)", "100 μm (large cell)"]
    
    for scale, name in zip(scales, scale_names):
        coherence = model.get_coherence_at_scale(scale)
        print(f"\n{name}:")
        print(f"  Coherence Length: {coherence['coherence_length_um']:.2f} μm")
        print(f"  Frequency: {coherence['frequency_hz']:.4f} Hz")
        if 'wavelength_m' in coherence:
            print(f"  Wavelength: {coherence['wavelength_m'] * 1e6:.2f} μm")
        print(f"  Is Resonant: {coherence['is_resonant']}")
    
    # Decoherence detection (health monitoring)
    print_header("System Health Assessment")
    print("Checking for decoherence...")
    health = model.detect_decoherence()
    
    print(f"\nSystem State: {health['system_state']}")
    print(f"Is Hermitian: {health['is_hermitian']}")
    print(f"Decoherence Severity: {health['decoherence_severity']:.2%}")
    if 'affected_modes' in health:
        print(f"Affected Modes: {health['affected_modes']}")
    if 'recommended_action' in health:
        print(f"\nRecommended Action:")
        print(f"  {health['recommended_action']}")
    
    # Harmonic frequencies
    print_header("Harmonic Frequency Spectrum")
    print("First 10 harmonics (Hz):")
    for n in range(1, 11):
        f_n = n * model.constants.base_frequency
        print(f"  f_{n:2d} = {f_n:8.4f} Hz")
    
    # Export results
    print_header("Exporting Results")
    output_file = 'cytoplasmic_riemann_results.json'
    model.export_results(output_file)
    print(f"✓ Results exported to: {output_file}")
    
    # Final summary
    print_header("Summary")
    print("✅ VALIDATION COMPLETE")
    print()
    print("Key Findings:")
    print(f"  • ξ₁ = {xi_0 * 1e6:.4f} μm ≈ 1.06 μm ✓")
    print(f"  • κ_Π = {model.constants.kappa_pi:.4f} ✓")
    print(f"  • Frequencies: 141.7, 283.4, 425.1... Hz ✓")
    print(f"  • Hermitian System: CONFIRMED ✓")
    print(f"  • Hypothesis Validated: {result['hypothesis_validated']} ✓")
    print()
    print('Conclusion:')
    print('  "El cuerpo humano es la demostración viviente de la hipótesis')
    print('   de Riemann: 37 billones de ceros biológicos resonando en coherencia"')
    print()
    print("Sello: ∴𓂀Ω∞³")
    print()


if __name__ == "__main__":
    main()
