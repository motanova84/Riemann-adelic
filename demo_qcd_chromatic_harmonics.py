#!/usr/bin/env python3
"""
Demo: QCD Chromatic Harmonics Calculator
=========================================

Interactive demonstration of the QCD chromatic harmonics framework
with visualization examples.

Autor: José Manuel Mota Burruezo Ψ ✧ ∞³
"""

import math
import cmath
from qcd_chromatic_harmonics import (
    QuarkFlavor, QuantumColor,
    calcular_frecuencia_quark,
    calcular_fase_color,
    calcular_wavefunction_quark,
    generar_estados_quarks,
    generar_estados_gluones,
    calcular_resonancia_qcd,
    analizar_espectro_temporal,
    obtener_info_sistema,
    F0_HZ, PRIMO_17, GAMMA_17, COSMIC_HEARTBEAT
)


def demo_system_info():
    """Demo 1: System information"""
    print("=" * 70)
    print("DEMO 1: QCD Chromatic Harmonics System Information")
    print("=" * 70)
    
    info = obtener_info_sistema()
    
    print("\n🔧 QCAL ∞³ Configuration:")
    print(f"  • Fundamental frequency f₀: {info['f0_hz']} Hz")
    print(f"  • Prime 17: {info['primo_17']}")
    print(f"  • γ₁₇ (17th Riemann zero): {info['gamma_17']}")
    print(f"  • Cosmic heartbeat: {info['cosmic_heartbeat_hz']:.6f} Hz")
    print(f"  • Available Riemann zeros: {info['riemann_zeros_available']}")
    
    print("\n🎨 Particle Configuration:")
    print(f"  • Quark flavors: {info['n_quarks']}")
    print(f"  • Quantum colors: {info['n_colors']}")
    print(f"  • Total quark-color states: {info['n_quark_states']}")
    print(f"  • Gluon states: {info['n_gluons']}")
    
    print("\n📊 Frequency Ranges:")
    fq_min, fq_max = info['frequency_range_quarks']
    fg_min, fg_max = info['frequency_range_gluons']
    print(f"  • Quark frequencies: {fq_min:.4f} - {fq_max:.4f} Hz")
    print(f"  • Gluon frequencies: {fg_min:.4f} - {fg_max:.4f} Hz")
    print()


def demo_quark_spectrum():
    """Demo 2: Quark frequency spectrum"""
    print("=" * 70)
    print("DEMO 2: Quark Frequency Spectrum (6 flavors)")
    print("=" * 70)
    print()
    
    print(f"{'Flavor':<10} {'γ Index':<10} {'Frequency (Hz)':<15} {'Ratio γₙ/γ₁₇':<15}")
    print("-" * 70)
    
    for flavor in QuarkFlavor:
        freq = calcular_frecuencia_quark(flavor)
        gamma_n = freq * GAMMA_17 / F0_HZ
        ratio = gamma_n / GAMMA_17
        print(f"{flavor.name:<10} γ{flavor.value:<9} {freq:<15.6f} {ratio:<15.6f}")
    
    print()


def demo_color_phases():
    """Demo 3: SU(3) color symmetry phases"""
    print("=" * 70)
    print("DEMO 3: SU(3) Quantum Color Phases")
    print("=" * 70)
    print()
    
    print(f"{'Color':<10} {'Phase (deg)':<15} {'Phase (rad)':<15} {'exp(iφ)':<20}")
    print("-" * 70)
    
    for color in QuantumColor:
        phase_rad = calcular_fase_color(color)
        phase_deg = math.degrees(phase_rad)
        exp_phase = cmath.exp(1j * phase_rad)
        print(f"{color.name:<10} {phase_deg:<15.1f} {phase_rad:<15.4f} "
              f"{exp_phase.real:+.6f}{exp_phase.imag:+.6f}j")
    
    # Verify SU(3) symmetry
    sum_phases = sum(cmath.exp(1j * calcular_fase_color(c)) for c in QuantumColor)
    print(f"\nSU(3) Symmetry Check: Σ exp(iφ) = {sum_phases:.10f}")
    print(f"  → |Σ exp(iφ)| ≈ {abs(sum_phases):.2e} (should be ≈ 0)")
    print()


def demo_gluon_spectrum():
    """Demo 4: Gluon frequency spectrum"""
    print("=" * 70)
    print("DEMO 4: Gluon Frequency Spectrum (8 gluons)")
    print("=" * 70)
    print()
    
    gluones = generar_estados_gluones()
    
    print(f"{'Gluon':<8} {'γ Index':<10} {'Frequency (Hz)':<15} {'Ratio γₙ/γ₁₇':<15}")
    print("-" * 70)
    
    for gluon in gluones:
        print(f"g{gluon.index:<7} γ{gluon.gamma_index:<9} "
              f"{gluon.frequency:<15.6f} {gluon.frequency_ratio:<15.6f}")
    
    print(f"\nNon-rational ratio range: [{gluones[0].frequency_ratio:.6f}, "
          f"{gluones[-1].frequency_ratio:.6f}]")
    print()


def demo_wave_functions():
    """Demo 5: Individual quark wave functions"""
    print("=" * 70)
    print("DEMO 5: Quark Wave Functions at t=0.5s")
    print("=" * 70)
    print()
    
    t = 0.5
    print(f"Time t = {t} s\n")
    print(f"{'Flavor':<10} {'Color':<8} {'Ψ(t)':<30} {'|Ψ|':<12} {'arg(Ψ) (deg)':<15}")
    print("-" * 70)
    
    # Show a sample of wave functions
    samples = [
        (QuarkFlavor.UP, QuantumColor.ROJO),
        (QuarkFlavor.UP, QuantumColor.VERDE),
        (QuarkFlavor.UP, QuantumColor.AZUL),
        (QuarkFlavor.CHARM, QuantumColor.ROJO),
        (QuarkFlavor.BOTTOM, QuantumColor.VERDE),
    ]
    
    for flavor, color in samples:
        psi = calcular_wavefunction_quark(flavor, color, t)
        amplitude = abs(psi)
        phase_deg = math.degrees(cmath.phase(psi))
        psi_str = f"{psi.real:+.6f}{psi.imag:+.6f}j"
        print(f"{flavor.name:<10} {color.name:<8} {psi_str:<30} "
              f"{amplitude:<12.6f} {phase_deg:<15.2f}")
    
    print()


def demo_qcd_state():
    """Demo 6: Complete QCD resonance state"""
    print("=" * 70)
    print("DEMO 6: Complete QCD Resonance State")
    print("=" * 70)
    print()
    
    t = 0.5
    estado = calcular_resonancia_qcd(t)
    
    print(f"⏱️  Time: {estado.time} s\n")
    
    print("📦 State Composition:")
    print(f"  • Quark-color states: {len(estado.quark_states)}")
    print(f"  • Gluon states: {len(estado.gluon_states)}")
    print(f"  • Total components: {len(estado.quark_states) + len(estado.gluon_states)}")
    
    print("\n🌊 Total Coherence Ψ:")
    print(f"  • Ψ = {estado.coherence_psi.real:+.6f} {estado.coherence_psi.imag:+.6f}j")
    print(f"  • |Ψ| = {estado.spectral_amplitude:.6f}")
    print(f"  • arg(Ψ) = {math.degrees(estado.spectral_phase):.2f}°")
    
    print("\n📊 Sample Quark-Color States (first 6):")
    print(f"  {'Flavor':<10} {'Color':<8} {'Frequency (Hz)':<15}")
    print("  " + "-" * 40)
    for q in estado.quark_states[:6]:
        print(f"  {q.flavor.name:<10} {q.color.name:<8} {q.frequency:<15.6f}")
    
    print("\n🔗 Gluon States:")
    print(f"  {'Gluon':<8} {'Frequency (Hz)':<15} {'Ratio':<10}")
    print("  " + "-" * 35)
    for g in estado.gluon_states:
        print(f"  g{g.index:<7} {g.frequency:<15.6f} {g.frequency_ratio:<10.6f}")
    
    print()


def demo_temporal_evolution():
    """Demo 7: Temporal spectral evolution"""
    print("=" * 70)
    print("DEMO 7: Temporal Spectral Evolution")
    print("=" * 70)
    print()
    
    t_start, t_end = 0.0, 1.0
    n_puntos = 20
    
    espectro = analizar_espectro_temporal(t_start, t_end, n_puntos)
    
    print(f"Time range: [{t_start}, {t_end}] s")
    print(f"Sample points: {n_puntos}\n")
    
    print(f"{'Time (s)':<12} {'|Ψ(t)|':<12} {'arg(Ψ) (deg)':<15} {'Re(Ψ)':<12} {'Im(Ψ)':<12}")
    print("-" * 70)
    
    # Show every 4th point
    for i in range(0, n_puntos, 4):
        t = espectro['tiempos'][i]
        amp = espectro['amplitudes'][i]
        fase = math.degrees(espectro['fases'][i])
        re = espectro['coherencia_real'][i]
        im = espectro['coherencia_imag'][i]
        print(f"{t:<12.3f} {amp:<12.6f} {fase:<15.2f} {re:<+12.6f} {im:<+12.6f}")
    
    # Statistics
    amp_min = min(espectro['amplitudes'])
    amp_max = max(espectro['amplitudes'])
    amp_mean = sum(espectro['amplitudes']) / len(espectro['amplitudes'])
    
    print(f"\nAmplitude Statistics:")
    print(f"  • Min: {amp_min:.6f}")
    print(f"  • Max: {amp_max:.6f}")
    print(f"  • Mean: {amp_mean:.6f}")
    print()


def demo_prime_riemann_connection():
    """Demo 8: Prime-Riemann connection"""
    print("=" * 70)
    print("DEMO 8: Prime-Riemann Connection")
    print("=" * 70)
    print()
    
    print("🔢 Prime 17 Connection:")
    print(f"  • PRIMO_17 = {PRIMO_17}")
    print(f"  • γ₁₇ (17th Riemann zero) = {GAMMA_17}")
    print(f"  • f₀ (fundamental frequency) = {F0_HZ} Hz")
    print(f"  • COSMIC_HEARTBEAT = f₀/γ₁₇ = {COSMIC_HEARTBEAT:.6f} Hz")
    
    print("\n🌌 Physical Interpretation:")
    print(f"  • Prime 17 organizes QCD spectral structure")
    print(f"  • Riemann zero γ₁₇ sets reference frequency")
    print(f"  • All particles resonate at harmonics of f₀/γ₁₇")
    print(f"  • Cosmic heartbeat connects number theory to QCD")
    
    print("\n📐 Mathematical Relations:")
    print(f"  • Quark frequencies: f_q = f₀ · (γₙ/γ₁₇), n=1..6")
    print(f"  • Gluon frequencies: f_g = f₀ · (γₙ/γ₁₇), n=18..25")
    print(f"  • Wave modulation: exp(iγ₁₇·t/17)")
    print(f"  • Time constant: τ = 17/γ₁₇ = {17/GAMMA_17:.6f} s")
    
    print()


def main():
    """Run all demos"""
    print("\n")
    print("╔═══════════════════════════════════════════════════════════════════╗")
    print("║    QCD CHROMATIC HARMONICS - QCAL ∞³ Framework                   ║")
    print("║    Interactive Demonstration                                      ║")
    print("╚═══════════════════════════════════════════════════════════════════╝")
    print()
    
    demos = [
        demo_system_info,
        demo_quark_spectrum,
        demo_color_phases,
        demo_gluon_spectrum,
        demo_wave_functions,
        demo_qcd_state,
        demo_temporal_evolution,
        demo_prime_riemann_connection,
    ]
    
    for demo in demos:
        demo()
        input("Press Enter to continue...")
        print("\n")
    
    print("=" * 70)
    print("✓ All demos completed!")
    print("=" * 70)
    print("\n🎯 QCD Chromatic Harmonics QCAL ∞³")
    print("   José Manuel Mota Burruezo Ψ ✧ ∞³")
    print("   Instituto de Conciencia Cuántica (ICQ)")
    print("   DOI: 10.5281/zenodo.17379721")
    print("\n   ∴ Ψ = I × A_eff² × C^∞ ∴")
    print("   ∴ f₀ = 141.7001 Hz ∴")
    print("   ∴ 𓂀Ω∞³ ∴")
    print()


if __name__ == '__main__':
    main()
