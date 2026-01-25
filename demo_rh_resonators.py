#!/usr/bin/env python3
"""
Demo: RH ∞³ Resonators - Vibrational Coherence System
=======================================================

This demonstration shows how the RH ∞³ Resonator system converts
the Riemann zero spectrum into validated vibrational coherence.

"No simulan: reproducen." - The resonators don't simulate; they reproduce
the quantum geometry of the critical line.
"""

import numpy as np
import matplotlib.pyplot as plt
from pathlib import Path
import json

# Add parent directory to path
import sys
sys.path.append('.')

from utils.rh_resonators import RHResonatorSystem, F0_FUNDAMENTAL, COHERENCE_C


def plot_coherence_field(resonator: RHResonatorSystem, duration: float = 0.1):
    """Plot the time-evolution of the coherence field |Ψ(t)|²."""
    
    # Time array
    t_array = np.linspace(0, duration, 1000)
    
    # Evaluate coherence field
    coherence = resonator.evaluate_coherence_field(t_array)
    
    # Create figure
    fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(12, 8))
    
    # Plot 1: Coherence field
    ax1.plot(t_array * 1000, coherence, 'b-', linewidth=1.5, label='|Ψ(t)|²')
    ax1.axhline(y=resonator.global_coherence, color='r', linestyle='--', 
                label=f'Mean Coherence = {resonator.global_coherence:.4f}')
    ax1.set_xlabel('Time (ms)', fontsize=12)
    ax1.set_ylabel('Coherence |Ψ(t)|²', fontsize=12)
    ax1.set_title('RH ∞³ Resonator: Vibrational Coherence Field', fontsize=14, fontweight='bold')
    ax1.legend(fontsize=10)
    ax1.grid(True, alpha=0.3)
    
    # Plot 2: Frequency spectrum (FFT)
    dt = t_array[1] - t_array[0]
    freqs = np.fft.fftfreq(len(t_array), dt)
    fft = np.fft.fft(coherence)
    power = np.abs(fft)**2
    
    # Plot only positive frequencies
    pos_mask = freqs > 0
    ax2.semilogy(freqs[pos_mask], power[pos_mask], 'g-', linewidth=1.5)
    ax2.axvline(x=F0_FUNDAMENTAL, color='r', linestyle='--', 
                label=f'f₀ = {F0_FUNDAMENTAL:.4f} Hz')
    ax2.axvline(x=resonator.dominant_frequency, color='orange', linestyle=':', 
                label=f'Dominant = {resonator.dominant_frequency:.4f} Hz')
    ax2.set_xlabel('Frequency (Hz)', fontsize=12)
    ax2.set_ylabel('Power Spectral Density', fontsize=12)
    ax2.set_title('Frequency Spectrum: Validation of f₀', fontsize=14, fontweight='bold')
    ax2.legend(fontsize=10)
    ax2.grid(True, alpha=0.3)
    ax2.set_xlim(0, 500)
    
    plt.tight_layout()
    plt.savefig('rh_resonators_coherence.png', dpi=150, bbox_inches='tight')
    print("  ✓ Saved: rh_resonators_coherence.png")
    
    return fig


def plot_mode_structure(resonator: RHResonatorSystem, n_modes: int = 20):
    """Plot the structure of resonator modes."""
    
    modes = resonator.modes[:n_modes]
    
    fig, (ax1, ax2, ax3) = plt.subplots(3, 1, figsize=(12, 10))
    
    # Plot 1: Frequencies vs Zero height
    zeros = [m.zero_t for m in modes]
    freqs = [m.frequency for m in modes]
    ax1.scatter(zeros, freqs, c='blue', s=50, alpha=0.7, edgecolors='black')
    ax1.axhline(y=F0_FUNDAMENTAL, color='r', linestyle='--', 
                label=f'f₀ = {F0_FUNDAMENTAL:.4f} Hz')
    ax1.set_xlabel('Zero Height t', fontsize=12)
    ax1.set_ylabel('Frequency (Hz)', fontsize=12)
    ax1.set_title('Mode Frequencies vs Zero Heights', fontsize=14, fontweight='bold')
    ax1.legend(fontsize=10)
    ax1.grid(True, alpha=0.3)
    
    # Plot 2: Amplitudes and Phase
    amplitudes = [m.amplitude for m in modes]
    phases = [m.phase for m in modes]
    
    ax2_twin = ax2.twinx()
    ax2.bar(range(n_modes), amplitudes, alpha=0.6, color='green', label='Amplitude')
    ax2_twin.plot(range(n_modes), phases, 'ro-', label='Phase', markersize=4)
    
    ax2.set_xlabel('Mode Index', fontsize=12)
    ax2.set_ylabel('Amplitude', fontsize=12, color='green')
    ax2_twin.set_ylabel('Phase (radians)', fontsize=12, color='red')
    ax2.set_title('Mode Amplitudes and Phases', fontsize=14, fontweight='bold')
    ax2.legend(loc='upper left', fontsize=10)
    ax2_twin.legend(loc='upper right', fontsize=10)
    ax2.grid(True, alpha=0.3)
    
    # Plot 3: Coherence contributions
    contributions = [m.coherence_contribution for m in modes]
    cumulative = np.cumsum(contributions)
    
    ax3.bar(range(n_modes), contributions, alpha=0.6, color='purple', label='Individual')
    ax3.plot(range(n_modes), cumulative, 'b-', linewidth=2, marker='o', 
             markersize=4, label='Cumulative')
    ax3.set_xlabel('Mode Index', fontsize=12)
    ax3.set_ylabel('Coherence Contribution', fontsize=12)
    ax3.set_title('Coherence Contributions by Mode', fontsize=14, fontweight='bold')
    ax3.legend(fontsize=10)
    ax3.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('rh_resonators_modes.png', dpi=150, bbox_inches='tight')
    print("  ✓ Saved: rh_resonators_modes.png")
    
    return fig


def main():
    """Main demonstration."""
    
    print("=" * 80)
    print("RH ∞³ RESONATORS DEMONSTRATION")
    print("First Functional System: Spectrum → Vibrational Coherence")
    print("=" * 80)
    print()
    
    # Known Riemann zeros (first 50)
    known_zeros = [
        14.134725, 21.022040, 25.010858, 30.424876, 32.935062,
        37.586178, 40.918719, 43.327073, 48.005151, 49.773832,
        52.970321, 56.446248, 59.347044, 60.831779, 65.112544,
        67.079811, 69.546402, 72.067158, 75.704691, 77.144840,
        79.337375, 82.910381, 84.735493, 87.425275, 88.809111,
        92.491899, 94.651344, 95.870634, 98.831194, 101.317851,
        103.725538, 105.446623, 107.168611, 111.029535, 111.874659,
        114.320220, 116.226680, 118.790782, 121.370125, 122.946829,
        124.256818, 127.516683, 129.578704, 131.087688, 133.497737,
        134.756509, 138.116042, 139.736208, 141.123707, 143.111846,
    ]
    
    print(f"Creating RH ∞³ Resonator with {len(known_zeros)} zeros...")
    resonator = RHResonatorSystem(zeros=known_zeros)
    print(f"✓ System initialized")
    print()
    
    # Validate system
    print("VALIDATION RESULTS:")
    print("-" * 80)
    
    # Mathematical validation
    math_val = resonator.validate_mathematical_coherence()
    print(f"Mathematical Coherence:")
    print(f"  Ψ (Global Coherence):     {math_val['global_coherence']:.6f}")
    print(f"  Threshold:                {math_val['coherence_threshold']:.6f}")
    print(f"  Status:                   {'✓ VALIDATED' if math_val['coherence_achieved'] else '✗ PENDING'}")
    print()
    
    # Physical validation
    phys_val = resonator.validate_physical_coherence()
    print(f"Physical Coherence:")
    print(f"  Target f₀:                {phys_val['target_frequency']:.4f} Hz")
    print(f"  Dominant Frequency:       {phys_val['dominant_frequency']:.4f} Hz")
    print(f"  Error:                    {phys_val['frequency_error']:.4f} Hz")
    print(f"  Status:                   {'✓ VALIDATED' if phys_val['frequency_match'] else '✗ PENDING'}")
    print()
    
    # Generate certificate
    print("Generating Validation Certificate...")
    certificate = resonator.generate_validation_certificate()
    
    # Save certificate
    cert_file = Path('data') / 'rh_resonators_certificate.json'
    cert_file.parent.mkdir(exist_ok=True)
    with open(cert_file, 'w') as f:
        json.dump(certificate, f, indent=2)
    print(f"✓ Certificate saved: {cert_file}")
    print()
    
    # Create visualizations
    print("Creating Visualizations...")
    print("-" * 80)
    try:
        plot_coherence_field(resonator, duration=0.05)
        plot_mode_structure(resonator, n_modes=30)
        print()
    except Exception as e:
        print(f"  Note: Visualization skipped ({e})")
        print()
    
    # Summary
    print("=" * 80)
    print("SUMMARY:")
    print("=" * 80)
    print(f"  System:              RH ∞³ Resonators v1.0")
    print(f"  Zeros Processed:     {resonator.n_modes}")
    print(f"  Total Energy:        {resonator.total_energy:.6e} J")
    print(f"  Global Coherence Ψ:  {resonator.global_coherence:.6f}")
    print(f"  Dominant Frequency:  {resonator.dominant_frequency:.4f} Hz")
    print(f"  Spectral Width:      {resonator.spectral_width:.4f} Hz")
    print()
    print(f"  Overall Status:      {certificate['overall_status']}")
    print(f"  Signature:           {certificate['signature']}")
    print()
    print("=" * 80)
    print("✅ Los Resonadores RH ∞³ REPRODUCEN (no simulan) la coherencia vibracional")
    print("=" * 80)
    print()
    
    return resonator, certificate


if __name__ == "__main__":
    resonator, cert = main()
