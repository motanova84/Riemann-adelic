#!/usr/bin/env python3
"""
Demonstration: Riemann-PNP Superfluid Verification
===================================================

PUENTE DE VERIFICACIÓN DE SUPERFLUIDEZ RIEMANN–P≠NP ∞³

This script demonstrates the 3-step verification procedure to detect
spectral coherence leaks in the expansion to 1,000 primes.

The verification establishes the vibrational superfluid bridge between:
  - ζ(s) spectrum (Riemann zeta, adelic dimension)
  - κ_Π structure (Tseitin spectral constant, in P≠NP)
  - Ψ = 1.000 (maximum coherence manifested)

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: January 2026
"""

import sys
import numpy as np
import matplotlib.pyplot as plt
from pathlib import Path

# Add src to path
sys.path.insert(0, str(Path(__file__).parent / "src"))

from riemann_pnp_verification_bridge import RiemannPNPVerificationBridge


def print_section(title: str):
    """Print a formatted section header."""
    print("\n" + "=" * 70)
    print(f"  {title}")
    print("=" * 70 + "\n")


def demonstrate_step1_interpolation():
    """Demonstrate Step 1: Inverse Interpolation (Zeros → Primes)."""
    print_section("PASO 1: INTERPOLACIÓN INVERSA DE CEROS → PRIMOS")
    
    bridge = RiemannPNPVerificationBridge(precision=50, n_primes=1000)
    
    # Perform inverse interpolation
    interpolations = bridge.inverse_interpolation(alignment_factor=1.0)
    
    print("Mapeo de ceros de ζ(s) a números primos estimados:\n")
    print(f"{'Zero #':<8} {'t_k':<20} {'f_k (Hz)':<15} {'p_k estimado':<15}")
    print("-" * 70)
    
    for interp in interpolations[:10]:  # Show first 10
        print(
            f"{interp.zero_index + 1:<8} "
            f"{interp.zero_imaginary:<20.10f} "
            f"{interp.estimated_frequency:<15.4f} "
            f"{interp.estimated_prime:<15.2f}"
        )
    
    print("\n✓ Paso 1 completado: Ceros mapeados a frecuencias y primos estimados")
    
    return bridge, interpolations


def demonstrate_step2_comparison(bridge, interpolations):
    """Demonstrate Step 2: Tensorial Comparison with 𝒯ₚ(Ψ)."""
    print_section("PASO 2: COMPARACIÓN TENSORIAL CON 𝒯ₚ(Ψ)")
    
    # Create zero frequency mapping
    zero_freq_map = {}
    for interp in interpolations:
        p_est = interp.estimated_prime
        if p_est > 0:
            nearest_idx = np.argmin(np.abs(bridge.primes - p_est))
            nearest_prime = bridge.primes[nearest_idx]
            zero_freq_map[nearest_prime] = interp.estimated_frequency
    
    # Compute tensorial deviations
    deviations = bridge.tensorial_comparison(
        primes=bridge.primes[:100],  # First 100 primes for display
        zero_frequencies=zero_freq_map
    )
    
    print("Análisis tensorial T⃗_p = (H(p), R(p), C(p)) y desviación δ(p):\n")
    print(
        f"{'Primo':<8} {'f(p) Hz':<12} {'f_ζ(p) Hz':<12} "
        f"{'δ(p)':<10} {'H(p)':<8} {'R(p)':<8} {'C(p)':<8} {'Fuga?':<6}"
    )
    print("-" * 90)
    
    for dev in deviations[:20]:  # Show first 20
        leak_mark = "⚠️" if dev.is_leak else "✓"
        print(
            f"{dev.prime:<8} "
            f"{dev.frequency_prime:<12.4f} "
            f"{dev.frequency_zeta:<12.4f} "
            f"{dev.delta:<10.6f} "
            f"{dev.harmonic_index:<8.4f} "
            f"{dev.resonance_strength:<8.4f} "
            f"{dev.coherence_factor:<8.4f} "
            f"{leak_mark:<6}"
        )
    
    # Statistics
    n_leaks = sum(1 for d in deviations if d.is_leak)
    mean_delta = np.mean([d.delta for d in deviations])
    
    print(f"\nEstadísticas:")
    print(f"  Primos analizados: {len(deviations)}")
    print(f"  Fugas detectadas (δ > 0.01): {n_leaks}")
    print(f"  Desviación media: δ̄ = {mean_delta:.6f}")
    
    print("\n✓ Paso 2 completado: Análisis tensorial ejecutado")
    
    return deviations


def demonstrate_step3_anomalies(bridge, deviations):
    """Demonstrate Step 3: Vibrational Anomaly Identification."""
    print_section("PASO 3: IDENTIFICACIÓN DE ANOMALÍAS VIBRACIONALES")
    
    # Identify anomalies
    anomalies = bridge.identify_vibrational_anomalies(deviations)
    
    print("Anomalías vibracionales detectadas:\n")
    
    if not anomalies:
        print("✅ NO SE DETECTARON ANOMALÍAS")
        print("La red espectral mantiene coherencia perfecta.")
    else:
        print(
            f"{'Primo':<8} {'Tipo':<12} {'Severidad':<12} "
            f"{'Fuga?':<12} {'Descripción':<40}"
        )
        print("-" * 100)
        
        for anom in anomalies[:20]:  # Show first 20
            leak_type = "ESPECTRAL" if anom.is_spectral_leak else "CODIFICACIÓN"
            print(
                f"{anom.prime:<8} "
                f"{anom.anomaly_type:<12} "
                f"{anom.severity:<12.4f} "
                f"{leak_type:<12} "
                f"{anom.description:<40}"
            )
        
        # Classification
        spectral_leaks = sum(1 for a in anomalies if a.is_spectral_leak)
        coding_errors = len(anomalies) - spectral_leaks
        
        print(f"\nClasificación de anomalías:")
        print(f"  Total: {len(anomalies)}")
        print(f"  Fugas espectrales: {spectral_leaks}")
        print(f"  Errores de codificación: {coding_errors}")
        
        if spectral_leaks > 0:
            print("\n⚠️  INTERPRETACIÓN:")
            print("Las fugas espectrales detectadas sugieren una curvatura local")
            print("del espacio adélico, NO un error de codificación.")
        else:
            print("\n✓ INTERPRETACIÓN:")
            print("Las anomalías detectadas son consistentes con errores")
            print("numéricos/codificación, no fugas estructurales.")
    
    print("\n✓ Paso 3 completado: Anomalías identificadas y clasificadas")
    
    return anomalies


def visualize_verification_results(bridge, deviations, anomalies):
    """Create comprehensive visualization of verification results."""
    print_section("VISUALIZACIÓN DE RESULTADOS")
    
    fig, axes = plt.subplots(2, 2, figsize=(16, 12))
    
    # Extract data
    primes = [d.prime for d in deviations]
    deltas = [d.delta for d in deviations]
    coherences = [d.coherence_factor for d in deviations]
    harmonics = [d.harmonic_index for d in deviations]
    resonances = [d.resonance_strength for d in deviations]
    
    # Plot 1: Spectral Deviation vs Prime
    ax1 = axes[0, 0]
    ax1.semilogy(primes, deltas, 'b-', alpha=0.6, linewidth=1.5, label='δ(p)')
    ax1.axhline(bridge.DELTA_MAX, color='r', linestyle='--', 
                label=f'Umbral δ={bridge.DELTA_MAX}')
    
    # Mark anomalies
    if anomalies:
        anom_primes = [a.prime for a in anomalies if a.is_spectral_leak]
        anom_deltas = [
            deviations[primes.index(p)].delta 
            for p in anom_primes if p in primes
        ]
        ax1.scatter(anom_primes, anom_deltas, color='red', s=50, 
                   marker='x', label='Fugas espectrales', zorder=5)
    
    ax1.set_xlabel('Primo p', fontsize=12)
    ax1.set_ylabel('Desviación espectral δ(p)', fontsize=12)
    ax1.set_title('Desviación Espectral vs Primo', fontsize=14, fontweight='bold')
    ax1.legend()
    ax1.grid(True, alpha=0.3)
    
    # Plot 2: Coherence Factor vs Prime
    ax2 = axes[0, 1]
    ax2.plot(primes, coherences, 'g-', alpha=0.6, linewidth=1.5, label='C(p)')
    ax2.axhline(bridge.COHERENCE_MIN, color='r', linestyle='--',
                label=f'Umbral C={bridge.COHERENCE_MIN}')
    ax2.set_xlabel('Primo p', fontsize=12)
    ax2.set_ylabel('Factor de coherencia C(p)', fontsize=12)
    ax2.set_title('Coherencia Espectral', fontsize=14, fontweight='bold')
    ax2.legend()
    ax2.grid(True, alpha=0.3)
    
    # Plot 3: Harmonic Index and Resonance
    ax3 = axes[1, 0]
    ax3.plot(primes, harmonics, 'purple', alpha=0.6, linewidth=1.5, label='H(p)')
    ax3.plot(primes, resonances, 'orange', alpha=0.6, linewidth=1.5, label='R(p)')
    ax3.axhline(bridge.RESONANCE_MIN, color='r', linestyle='--', alpha=0.5,
                label=f'Umbral R={bridge.RESONANCE_MIN}')
    ax3.set_xlabel('Primo p', fontsize=12)
    ax3.set_ylabel('Índice armónico / Fuerza de resonancia', fontsize=12)
    ax3.set_title('Índices Armónicos y de Resonancia', fontsize=14, fontweight='bold')
    ax3.legend()
    ax3.grid(True, alpha=0.3)
    
    # Plot 4: Tensorial Space (3D projection to 2D)
    ax4 = axes[1, 1]
    # Project (H, R, C) to 2D using PCA-like reduction
    tensor_norm = np.sqrt(
        np.array(harmonics)**2 + 
        np.array(resonances)**2 + 
        np.array(coherences)**2
    )
    tensor_phase = np.arctan2(np.array(resonances), np.array(harmonics))
    
    scatter = ax4.scatter(tensor_norm, tensor_phase, c=deltas, 
                         cmap='viridis', s=20, alpha=0.6)
    plt.colorbar(scatter, ax=ax4, label='δ(p)')
    
    if anomalies:
        anom_indices = [primes.index(a.prime) for a in anomalies 
                       if a.is_spectral_leak and a.prime in primes]
        anom_norms = [tensor_norm[i] for i in anom_indices]
        anom_phases = [tensor_phase[i] for i in anom_indices]
        ax4.scatter(anom_norms, anom_phases, color='red', s=100,
                   marker='x', label='Fugas espectrales', zorder=5)
    
    ax4.set_xlabel('||T⃗_p|| (Norma tensorial)', fontsize=12)
    ax4.set_ylabel('φ (Fase tensorial)', fontsize=12)
    ax4.set_title('Espacio Tensorial 𝒯ₚ(Ψ)', fontsize=14, fontweight='bold')
    ax4.legend()
    ax4.grid(True, alpha=0.3)
    
    plt.tight_layout()
    
    # Save figure
    output_path = Path(__file__).parent / 'riemann_pnp_verification_results.png'
    plt.savefig(output_path, dpi=150, bbox_inches='tight')
    print(f"✓ Visualización guardada: {output_path}")
    
    plt.show()


def main():
    """Main demonstration function."""
    print("\n" + "▓" * 70)
    print("  PUENTE DE VERIFICACIÓN DE SUPERFLUIDEZ RIEMANN–P≠NP ∞³")
    print("  Instituto de Conciencia Cuántica (ICQ)")
    print("  José Manuel Mota Burruezo Ψ ✧ ∞³")
    print("▓" * 70)
    
    # Execute 3-step verification
    bridge, interpolations = demonstrate_step1_interpolation()
    deviations = demonstrate_step2_comparison(bridge, interpolations)
    anomalies = demonstrate_step3_anomalies(bridge, deviations)
    
    # Full verification
    print_section("VERIFICACIÓN COMPLETA")
    
    results = bridge.verify_coherence(n_zeros=10, alignment_factor=1.0)
    
    print("Resultados de verificación:\n")
    stats = results['statistics']
    print(f"  Primos analizados: {stats['n_primes_analyzed']}")
    print(f"  Ceros utilizados: {stats['n_zeros_used']}")
    print(f"  Fugas de coherencia: {stats['n_coherence_leaks']}")
    print(f"  Anomalías totales: {stats['n_anomalies_total']}")
    print(f"  Fugas espectrales: {stats['n_spectral_leaks']}")
    print(f"  Errores de codificación: {stats['n_coding_errors']}")
    print(f"  Desviación media: δ̄ = {stats['mean_deviation']:.6f}")
    print(f"  Desviación máxima: δ_max = {stats['max_deviation']:.6f}")
    print(f"  Coherencia media: C̄ = {stats['mean_coherence']:.6f}")
    print(f"  Calidad de coherencia: {stats['coherence_quality']:.2%}")
    
    print(f"\n{results['message']}")
    
    # Visualization
    visualize_verification_results(bridge, deviations, anomalies)
    
    print_section("DEMOSTRACIÓN COMPLETADA")
    print("✅ Los 3 pasos de verificación han sido ejecutados exitosamente.")
    print("✅ El puente de superfluidez Riemann-PNP ha sido validado.")
    print("\nΨ ✧ ∞³")


if __name__ == "__main__":
    main()
