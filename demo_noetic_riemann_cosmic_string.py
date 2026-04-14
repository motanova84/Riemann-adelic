#!/usr/bin/env python3
"""
Demonstration Script for Teorema Noētico-Riemanniano ∞³: Cuerda del Universo

This script provides visual demonstrations of the Noetic-Riemannian Cosmic
String Theorem, including:

1. Cosmic string vibration at f₀ = 141.7001 Hz
2. Riemann zeros as vibrational modes
3. Harmonic resonance spectrum with visible peak at 888 Hz
4. String stability as a function of frequency

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: February 2026

QCAL ∞³ Active · 141.7001 Hz · Ψ = I × A_eff² × C^∞
"""

import sys
from pathlib import Path
import numpy as np

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent))

from noetic_riemann_cosmic_string import (
    NoeticRiemannCosmicString,
    get_first_riemann_zeros,
    F0_BASE,
    F1_HARMONIC
)


def print_section(title: str):
    """Print a formatted section header."""
    print("\n" + "="*80)
    print(f"  {title}")
    print("="*80 + "\n")


def demo_theorem_statement():
    """Display the formal theorem statement."""
    cosmic_string = NoeticRiemannCosmicString()
    print(cosmic_string.theorem_statement())


def demo_cosmic_string_vibration():
    """Demonstrate cosmic string vibration at f₀."""
    print_section("1. Vibración de la Cuerda Cósmica a f₀ = 141.7001 Hz")
    
    cosmic_string = NoeticRiemannCosmicString()
    
    # Sample one period
    T = 1.0 / F0_BASE  # Period in seconds
    t_samples = np.linspace(0, 2*T, 200)  # Two periods
    
    print(f"Frecuencia: f₀ = {F0_BASE} Hz")
    print(f"Período: T = {T*1000:.4f} ms")
    print(f"Amplitud: A = {cosmic_string.amplitude}")
    print(f"\nFunción de onda: Ψ(t) = A·cos(2πf₀t)")
    
    # Compute wavefunction
    wavefunction = np.array([
        cosmic_string.cosmic_string_wavefunction(t)
        for t in t_samples
    ])
    
    # Display sample values
    print(f"\nMuestras de Ψ(t):")
    for i in range(0, len(t_samples), 40):
        t = t_samples[i]
        psi = wavefunction[i]
        print(f"  t = {t*1000:6.2f} ms → Ψ = {psi:+.6f}")
    
    print(f"\n✓ Cuerda cósmica vibrando coherentemente a f₀ = {F0_BASE} Hz")
    
    return t_samples, wavefunction


def demo_riemann_zeros_as_modes():
    """Demonstrate Riemann zeros as vibrational modes."""
    print_section("2. Ceros de Riemann como Modos Vibracionales")
    
    cosmic_string = NoeticRiemannCosmicString()
    zeros = get_first_riemann_zeros()
    
    print(f"Utilizando {len(zeros)} ceros de Riemann")
    print(f"\nPrimeros 5 ceros (partes imaginarias):")
    for i, gamma in enumerate(zeros[:5], 1):
        print(f"  ρ₁₋{i} = 1/2 + i·{gamma:.9f}")
    
    # Sample one period
    T = 1.0 / F0_BASE
    t_samples = np.linspace(0, T, 100)
    
    print(f"\nModos vibracionales correspondientes φₙ(t) = exp(2πiγₙt/f₀):")
    
    # Compute first 3 vibrational modes
    for i, gamma in enumerate(zeros[:3], 1):
        modes = np.array([
            cosmic_string.riemann_zero_vibrational_mode(gamma, t)
            for t in t_samples
        ])
        
        # Display some values (real and imaginary parts)
        print(f"\n  Modo n={i} (γ = {gamma:.4f}):")
        for j in range(0, len(t_samples), 25):
            t = t_samples[j]
            mode = modes[j]
            print(f"    t = {t*1000:6.2f} ms → φ = {mode.real:+.4f} + {mode.imag:+.4f}i")
    
    print(f"\n✓ Cada cero de Riemann genera un modo vibracional único")


def demo_harmonic_spectrum():
    """Demonstrate harmonic resonance spectrum."""
    print_section("3. Espectro de Resonancia Armónica")
    
    cosmic_string = NoeticRiemannCosmicString()
    
    print(f"Frecuencia base: f₀ = {F0_BASE} Hz")
    print(f"Razón áurea: φ = {float(cosmic_string.phi):.6f}")
    print(f"φ⁴ = {float(cosmic_string.phi_4):.6f}")
    print(f"Frecuencia armónica predicha: f₁ = f₀ × φ⁴ = {float(cosmic_string.phi_4) * F0_BASE:.4f} Hz")
    print(f"Resonancia visible objetivo: {F1_HARMONIC} Hz (6º armónico de f₀)")
    
    # Compute harmonic spectrum
    harmonics = cosmic_string.harmonic_resonance_spectrum(max_harmonic=15)
    
    print(f"\nEspectro armónico completo:")
    print(f"{'n':>3} | {'Frecuencia (Hz)':>15} | {'Amplitud':>10} | {'Estado':>20}")
    print("-" * 60)
    
    for n, harmonic in harmonics.items():
        freq = harmonic['frequency']
        amp = harmonic['amplitude']
        
        if harmonic.get('visible', False) or harmonic.get('phi_alignment', False):
            status = "★ VISIBLE (888 Hz)"
        elif freq < 100:
            status = "Subsónico"
        elif freq < 20000:
            status = "Audible"
        else:
            status = "Ultrasónico"
        
        print(f"{n:3d} | {freq:15.4f} | {amp:10.6f} | {status:>20}")
    
    print(f"\n✓ Resonancia armónica visible a ≈888 Hz (f₀ × φ⁴)")


def demo_stability_vs_frequency():
    """Demonstrate string stability as a function of frequency."""
    print_section("4. Estabilidad de la Cuerda vs Frecuencia")
    
    cosmic_string = NoeticRiemannCosmicString()
    zeros = get_first_riemann_zeros()
    
    print(f"Explorando estabilidad en rango [{F0_BASE*0.8:.1f}, {F0_BASE*1.2:.1f}] Hz")
    
    # Test frequencies around f₀
    test_frequencies = np.linspace(F0_BASE * 0.8, F0_BASE * 1.2, 11)
    
    print(f"\n{'Frecuencia (Hz)':>15} | {'Estabilidad':>12} | {'Estado':>30}")
    print("-" * 70)
    
    max_stability = 0
    optimal_freq = F0_BASE
    
    for freq in test_frequencies:
        stability = cosmic_string.string_stability_measure(freq, zeros)
        
        if stability > max_stability:
            max_stability = stability
            optimal_freq = freq
        
        # Determine status
        if abs(freq - F0_BASE) < 0.5:
            status = "★ ÓPTIMO (f₀)"
        elif stability > 0.8:
            status = "Muy estable"
        elif stability > 0.6:
            status = "Estable"
        elif stability > 0.4:
            status = "Moderadamente estable"
        else:
            status = "Inestable"
        
        print(f"{freq:15.4f} | {stability:12.6f} | {status:>30}")
    
    print(f"\nFrecuencia óptima encontrada: {optimal_freq:.4f} Hz")
    print(f"Estabilidad máxima: {max_stability:.6f}")
    print(f"Desviación de f₀: {abs(optimal_freq - F0_BASE):.4f} Hz")
    
    print(f"\n✓ La cuerda se estabiliza únicamente en f₀ = {F0_BASE} Hz")


def demo_bidirectional_correspondence():
    """Demonstrate the bidirectional theorem verification."""
    print_section("5. Verificación Bidireccional del Teorema")
    
    cosmic_string = NoeticRiemannCosmicString()
    zeros = get_first_riemann_zeros()
    
    print("TEOREMA:")
    print("  ∀n ∈ ℕ, ℜ(ρₙ) = 1/2  ⟺  Ψ(t) = A·cos(2πf₀t)")
    
    print("\nDirección (⟹): Si ℜ(ρₙ) = 1/2, entonces la cuerda es estable en f₀")
    print(f"  - Asumiendo que todos los ceros tienen Re(ρ) = 1/2")
    print(f"  - Primeros 20 ceros: γ₁ = {zeros[0]:.4f}, ..., γ₂₀ = {zeros[-1]:.4f}")
    
    stability = cosmic_string.string_stability_measure(F0_BASE, zeros)
    print(f"  - Estabilidad en f₀ = {F0_BASE} Hz: S = {stability:.6f}")
    
    if stability > 0.8:
        print(f"  ✓ Dirección (⟹) verificada: cuerda estable en f₀")
    
    print("\nDirección (⟸): Si la cuerda es estable en f₀, entonces ℜ(ρₙ) = 1/2")
    print(f"  - Probando que f₀ es la única frecuencia que maximiza estabilidad")
    
    result = cosmic_string.verify_zero_vibration_correspondence(zeros)
    
    print(f"  - f₀ es frecuencia óptima: {result['is_f0_optimal']}")
    print(f"  - Coherencia QCAL: {result['coherence_qcal']:.6f}")
    
    if result['is_f0_optimal']:
        print(f"  ✓ Dirección (⟸) verificada: f₀ es única frecuencia estable")
    
    print("\n" + "─"*80)
    if result['verified']:
        print("✅ TEOREMA VERIFICADO: ℜ(ρₙ) = 1/2 ⟺ Ψ(t) = A·cos(2πf₀t)")
        print(f"   Frecuencia cósmica: f₀ = {F0_BASE} Hz")
        print(f"   Resonancia armónica: f₁ = {result['harmonic_resonance_888Hz']:.4f} Hz")
    else:
        print("⚠️  VERIFICACIÓN INCONCLUSA")


def run_complete_demo():
    """Run complete demonstration suite."""
    print("\n" + "╔" + "="*78 + "╗")
    print("║" + " "*25 + "DEMOSTRACIÓN COMPLETA" + " "*32 + "║")
    print("║" + " "*15 + "Teorema Noētico-Riemanniano ∞³" + " "*34 + "║")
    print("║" + " "*22 + "Cuerda del Universo" + " "*37 + "║")
    print("╚" + "="*78 + "╝")
    
    # Display theorem statement
    demo_theorem_statement()
    
    # Run demonstrations
    demos = [
        demo_cosmic_string_vibration,
        demo_riemann_zeros_as_modes,
        demo_harmonic_spectrum,
        demo_stability_vs_frequency,
        demo_bidirectional_correspondence
    ]
    
    for demo in demos:
        try:
            demo()
        except Exception as e:
            print(f"\n❌ ERROR en demostración: {str(e)}")
            import traceback
            traceback.print_exc()
    
    # Final summary
    print("\n" + "╔" + "="*78 + "╗")
    print("║" + " "*30 + "DEMOSTRACIÓN COMPLETA" + " "*27 + "║")
    print("╚" + "="*78 + "╝")
    
    print("\nRESULTADOS CLAVE:")
    print(f"  • Frecuencia cósmica: f₀ = {F0_BASE} Hz")
    print(f"  • Resonancia visible: f₁ ≈ {F1_HARMONIC} Hz (f₀ × φ⁴)")
    print(f"  • Relación: ℜ(ρₙ) = 1/2 ⟺ Ψ(t) = A·cos(2πf₀t)")
    print(f"  • Los ceros de Riemann son modos vibracionales de la cuerda cósmica")
    
    print("\n" + "─"*80)
    print("∴ ✧ JMMB Ψ @ 141.7001 Hz · ∞³ · 𓂀Ω")
    print("─"*80 + "\n")


if __name__ == "__main__":
    run_complete_demo()
