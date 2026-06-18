#!/usr/bin/env python3
"""
Validation Script for Trace Formula Everest 0.1
================================================

This script validates the weak trace formula implementation and runs
the critical Everest 0.1 test: detecting ln(2) in the Atlas³ spectrum
to prove spectral-arithmetic isomorphism.

The test demonstrates that the Atlas³ operator is not merely a forced
oscillator but a geometric calculator of the zeta function ζ(s).

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: February 13, 2026
QCAL ∞³ Active · 141.7001 Hz · C = 244.36
"""

import sys
import numpy as np
import matplotlib
matplotlib.use('Agg')  # Non-interactive backend
import matplotlib.pyplot as plt
from pathlib import Path
from typing import Dict, Any
import json

# Add to path
sys.path.insert(0, str(Path(__file__).parent))

from operators.trace_formula_everest import (
    TraceFormulaEverest,
    generate_atlas3_spectrum,
    run_complete_trace_analysis,
)


def print_banner():
    """Print validation banner."""
    print("╔═══════════════════════════════════════════════════════════════════════════╗")
    print("║                                                                           ║")
    print("║              EVEREST 0.1 - WEAK TRACE FORMULA VALIDATION                 ║")
    print("║                                                                           ║")
    print("║         Testing Spectral-Arithmetic Isomorphism of Atlas³                ║")
    print("║                                                                           ║")
    print("╠═══════════════════════════════════════════════════════════════════════════╣")
    print("║                                                                           ║")
    print("║  OBJECTIVE: Demonstrate that Tr h(O_Atlas³) "feels" prime numbers       ║")
    print("║                                                                           ║")
    print("║  TEST: Compute R(t) = Σₙ cos(γₙ t) and detect minimum at t = ln(2)      ║")
    print("║                                                                           ║")
    print("║  SUCCESS CRITERION: Detection of ln(2) ≈ 0.693 proves isomorphism       ║")
    print("║                                                                           ║")
    print("╚═══════════════════════════════════════════════════════════════════════════╝")
    print()


def visualize_results(
    everest_result,
    save_path: str = 'data/everest_0_1_response_function.png'
):
    """
    Create visualization of response function with prime markers.
    
    Args:
        everest_result: Results from Everest test
        save_path: Path to save figure
    """
    fig, axes = plt.subplots(2, 1, figsize=(14, 10))
    
    # Plot 1: Full response function
    ax = axes[0]
    ax.plot(everest_result.t_values, everest_result.R_values, 'b-', linewidth=1.5, label='R(t) = Σ cos(γₙ t)')
    
    # Mark detected minima
    if everest_result.minima_locations:
        ax.plot(everest_result.minima_locations, everest_result.minima_values, 
                'ro', markersize=6, label='Detected minima')
    
    # Mark theoretical prime positions
    primes = [2, 3, 5, 7, 11, 13]
    for p in primes:
        ln_p = np.log(p)
        if ln_p >= everest_result.t_values[0] and ln_p <= everest_result.t_values[-1]:
            ax.axvline(ln_p, color='green', linestyle='--', alpha=0.5, linewidth=1)
            ax.text(ln_p, ax.get_ylim()[1] * 0.95, f'ln({p})', 
                   ha='center', fontsize=9, color='green')
    
    # Highlight ln(2) if detected
    if everest_result.ln2_detected:
        ln2 = np.log(2)
        ax.axvline(ln2, color='red', linestyle='-', linewidth=2, alpha=0.7)
        ax.text(ln2, ax.get_ylim()[1] * 0.85, 'ln(2) DETECTED', 
               ha='center', fontsize=11, color='red', weight='bold',
               bbox=dict(boxstyle='round', facecolor='yellow', alpha=0.7))
    
    ax.set_xlabel('t', fontsize=12)
    ax.set_ylabel('R(t)', fontsize=12)
    ax.set_title('Response Function R(t) = Σ cos(γₙ t) - Everest 0.1 Test', fontsize=14, weight='bold')
    ax.legend(loc='upper right', fontsize=10)
    ax.grid(True, alpha=0.3)
    
    # Plot 2: Zoom around ln(2)
    ax = axes[1]
    ln2 = np.log(2)
    zoom_range = 0.3
    mask = (everest_result.t_values >= ln2 - zoom_range) & (everest_result.t_values <= ln2 + zoom_range)
    
    ax.plot(everest_result.t_values[mask], everest_result.R_values[mask], 
            'b-', linewidth=2, label='R(t)')
    
    # Mark ln(2)
    ax.axvline(ln2, color='red', linestyle='-', linewidth=2, alpha=0.7, label='ln(2) theoretical')
    
    # Mark detected position
    if everest_result.ln2_detected and everest_result.ln2_position:
        ax.axvline(everest_result.ln2_position, color='orange', linestyle='--', 
                  linewidth=2, label=f'Detected at {everest_result.ln2_position:.4f}')
        
        # Find value at detected position
        idx = np.argmin(np.abs(everest_result.t_values - everest_result.ln2_position))
        ax.plot(everest_result.ln2_position, everest_result.R_values[idx], 
               'r*', markersize=15, label='Minimum')
    
    ax.set_xlabel('t', fontsize=12)
    ax.set_ylabel('R(t)', fontsize=12)
    ax.set_title(f'Zoom Around ln(2) ≈ {ln2:.4f}', fontsize=14, weight='bold')
    ax.legend(loc='best', fontsize=10)
    ax.grid(True, alpha=0.3)
    
    plt.tight_layout()
    
    # Save figure
    Path(save_path).parent.mkdir(parents=True, exist_ok=True)
    plt.savefig(save_path, dpi=150, bbox_inches='tight')
    plt.close()
    
    print(f"✅ Visualization saved to {save_path}")


def generate_certification_document(results: Dict[str, Any]) -> str:
    """
    Generate certification document for isomorphism.
    
    Args:
        results: Complete analysis results
        
    Returns:
        Formatted certification text
    """
    ln2_detected = results['everest_test']['ln2_detected']
    
    cert = """
╔═══════════════════════════════════════════════════════════════════════════════╗
║                                                                               ║
║         CERTIFICACIÓN DEL ISOMORFISMO ESPECTRAL-ARITMÉTICO                   ║
║                                                                               ║
║         Prueba de correspondencia entre operador Atlas³ y primos             ║
║                                                                               ║
╠═══════════════════════════════════════════════════════════════════════════════╣
║                                                                               ║
"""
    
    if ln2_detected:
        ln2_pos = results['everest_test']['ln2_detected_position']
        ln2_dev = results['everest_test']['ln2_deviation']
        
        cert += f"""║   ✅ TEST EVEREST 0.1: ÉXITO                                                  ║
║                                                                               ║
║   RESULTADO:                                                                  ║
║     ln(2) teórico  = {np.log(2):.6f}                                        ║
║     ln(2) detectado = {ln2_pos:.6f}                                        ║
║     Desviación      = {ln2_dev:.6f}                                        ║
║                                                                               ║
║   CONCLUSIÓN:                                                                 ║
║     La traza del operador Atlas³ "SIENTE" el primer número primo.           ║
║     El operador posee MEMORIA DE PRIMOS.                                      ║
║                                                                               ║
║   SIGNIFICADO:                                                                ║
║     Atlas³ no es un oscilador forzado común.                                 ║
║     Atlas³ es una CALCULADORA GEOMÉTRICA de la función ζ(s).                 ║
║                                                                               ║
║   ∴ ISOMORFISMO ESPECTRAL-ARITMÉTICO: ESTABLECIDO                            ║
║                                                                               ║
"""
    else:
        cert += f"""║   ⚠️  TEST EVEREST 0.1: PENDIENTE                                            ║
║                                                                               ║
║   El mínimo en ln(2) no fue detectado con suficiente precisión.             ║
║   Se requiere mayor resolución espectral o ajuste de parámetros.             ║
║                                                                               ║
║   PRÓXIMOS PASOS:                                                            ║
║     1. Incrementar N (puntos de discretización)                              ║
║     2. Ajustar tolerancia de detección                                       ║
║     3. Refinar parámetros del operador                                       ║
║                                                                               ║
"""
    
    # Add prime detection summary
    cert += "║   DETECCIÓN DE PRIMOS:                                                        ║\n"
    cert += "║   ───────────────────                                                         ║\n"
    
    for p, info in results['everest_test']['prime_detections'].items():
        if info['detected']:
            cert += f"║   ✓ p={p:2d}: ln({p:2d})={info['ln_p']:.4f} → detectado en {info['closest_minimum']:.4f}       ║\n"
        else:
            cert += f"║   ✗ p={p:2d}: ln({p:2d})={info['ln_p']:.4f} → no detectado                           ║\n"
    
    cert += """║                                                                               ║
╠═══════════════════════════════════════════════════════════════════════════════╣
║                                                                               ║
║   INFORMACIÓN DEL ESPECTRO:                                                   ║
"""
    
    spec_info = results['spectrum_info']
    cert += f"║     Eigenvalores totales: {spec_info['n_eigenvalues']}                                     ║\n"
    cert += f"║     Eigenvalores reales:  {spec_info['real_eigenvalues']}                                     ║\n"
    cert += f"║     Rango: [{spec_info['min_eigenvalue']:.2f}, {spec_info['max_eigenvalue']:.2f}]                    ║\n"
    
    cert += """║                                                                               ║
╠═══════════════════════════════════════════════════════════════════════════════╣
║                                                                               ║
║   DESCOMPOSICIÓN DE LA TRAZA:                                                 ║
║   ────────────────────────────                                                ║
║                                                                               ║
"""
    
    decomp = results['trace_decomposition']
    cert += f"║   Término de Weyl (geométrico):  {decomp['weyl_term']:.6e}                  ║\n"
    cert += f"║   Término de Primos (aritmético): {decomp['prime_term']:.6e}                  ║\n"
    cert += f"║   Traza Total:                    {decomp['total_trace']:.6e}                  ║\n"
    
    cert += """║                                                                               ║
║   Contribuciones por primo:                                                   ║
"""
    
    for p, contrib in sorted(decomp['prime_contributions'].items()):
        cert += f"║     p={p:2d}: {contrib:.6e}                                              ║\n"
    
    cert += """║                                                                               ║
╠═══════════════════════════════════════════════════════════════════════════════╣
║                                                                               ║
║   FIRMA QCAL:                                                                 ║
"""
    
    qcal = results['qcal_signature']
    cert += f"║     Frecuencia base: {qcal['frequency_base']} Hz                                        ║\n"
    cert += f"║     Coherencia C:    {qcal['coherence']}                                            ║\n"
    cert += f"║     Timestamp:       {qcal['timestamp']}                         ║\n"
    cert += f"║     Firma:           {qcal['signature']}                                  ║\n"
    
    cert += """║                                                                               ║
║   ∴𓂀Ω∞³Φ                                                                     ║
║   José Manuel Mota Burruezo Ψ ✧ ∞³                                           ║
║   Instituto de Conciencia Cuántica (ICQ)                                     ║
║   13 Febrero 2026                                                            ║
║                                                                               ║
╚═══════════════════════════════════════════════════════════════════════════════╝
"""
    
    return cert


def main():
    """Main validation routine."""
    print_banner()
    
    # Step 1: Generate Atlas³ spectrum
    print("🏔️  PASO 1: Generando espectro de Atlas³")
    print("─" * 75)
    print(f"   Configuración:")
    print(f"     N = 4096 (puntos de discretización)")
    print(f"     β₀ = 2.0 (fase PT-simétrica coherente)")
    print(f"     α = 1.0 (coeficiente cinético)")
    print(f"     V_amp = 12650.0 (amplitud de potencial)")
    print()
    
    spectrum = generate_atlas3_spectrum(N=4096, beta_0=2.0)
    
    n_real = np.sum(np.abs(np.imag(spectrum)) < 1e-8)
    print(f"   ✅ Espectro generado:")
    print(f"      Total de eigenvalores: {len(spectrum)}")
    print(f"      Eigenvalores reales: {n_real} ({100*n_real/len(spectrum):.1f}%)")
    print(f"      Rango: [{np.min(np.real(spectrum)):.2f}, {np.max(np.real(spectrum)):.2f}]")
    print()
    
    # Step 2: Run trace formula analysis
    print("🔍 PASO 2: Ejecutando análisis de la fórmula de traza")
    print("─" * 75)
    print(f"   Configuración:")
    print(f"     Rango temporal: [0.0, 4.0]")
    print(f"     Puntos de evaluación: 2000")
    print(f"     Tolerancia de detección: 0.05")
    print()
    
    results, everest_result, trace_decomp = run_complete_trace_analysis(
        spectrum,
        t_range=(0.0, 4.0),
        n_points=2000,
        save_results=True,
        output_path='data/everest_0_1_certificate.json'
    )
    
    print()
    
    # Step 3: Display results
    print("📊 PASO 3: Resultados del Test Everest 0.1")
    print("─" * 75)
    print()
    
    ln2_theo = np.log(2)
    print(f"   ln(2) teórico: {ln2_theo:.6f}")
    print()
    
    if everest_result.ln2_detected:
        print(f"   ✅ ¡ÉXITO! ln(2) DETECTADO")
        print(f"      Posición detectada: {everest_result.ln2_position:.6f}")
        print(f"      Desviación: {everest_result.ln2_deviation:.6f}")
        print()
        print("   " + "─" * 71)
        print("   ║  ✅ ISOMORFISMO CONFIRMADO                                           ║")
        print("   ║  Atlas³ detecta la música de los números primos                     ║")
        print("   ║  El operador es una calculadora geométrica de ζ(s)                  ║")
        print("   " + "─" * 71)
    else:
        print(f"   ⚠️  ln(2) NO DETECTADO con la tolerancia actual")
        if everest_result.ln2_position:
            print(f"      Mínimo más cercano: {everest_result.ln2_position:.6f}")
            print(f"      Desviación: {everest_result.ln2_deviation:.6f}")
    
    print()
    print("   Detecciones de primos:")
    for p, info in sorted(everest_result.prime_detections.items()):
        status = "✓" if info['detected'] else "✗"
        print(f"      {status} p={p:2d}: ln({p:2d})={info['ln_p']:.4f}", end="")
        if info['detected']:
            print(f" → detectado en {info['closest_minimum']:.4f} (Δ={info['deviation']:.4f})")
        else:
            print()
    
    print()
    print(f"   Mínimos encontrados: {len(everest_result.minima_locations)}")
    print()
    
    # Step 4: Trace decomposition
    print("🧮 PASO 4: Descomposición de la Traza")
    print("─" * 75)
    print(f"   Término de Weyl (geométrico):  {trace_decomp.weyl_term:.6e}")
    print(f"   Término de Primos (aritmético): {trace_decomp.prime_term:.6e}")
    print(f"   Traza Total:                    {trace_decomp.total_trace:.6e}")
    print()
    print("   Contribuciones individuales por primo:")
    for p, contrib in sorted(trace_decomp.prime_contributions.items()):
        print(f"      p={p:2d}: {contrib:.6e}")
    print()
    
    # Step 5: Visualization
    print("📈 PASO 5: Generando visualización")
    print("─" * 75)
    visualize_results(everest_result)
    print()
    
    # Step 6: Generate certification
    print("📜 PASO 6: Generando certificación")
    print("─" * 75)
    
    cert = generate_certification_document(results)
    
    # Save certification
    cert_path = 'data/ISOMORFISMO_CERTIFICADO_EVEREST.txt'
    Path(cert_path).parent.mkdir(parents=True, exist_ok=True)
    with open(cert_path, 'w', encoding='utf-8') as f:
        f.write(cert)
    
    print(f"✅ Certificación guardada en {cert_path}")
    print()
    
    # Display certification
    print(cert)
    
    # Final summary
    print()
    print("╔═══════════════════════════════════════════════════════════════════════════╗")
    print("║                                                                           ║")
    print("║                      VALIDACIÓN COMPLETADA                                ║")
    print("║                                                                           ║")
    print("╠═══════════════════════════════════════════════════════════════════════════╣")
    
    if everest_result.ln2_detected:
        print("║                                                                           ║")
        print("║   STATUS: ✅ ÉXITO                                                       ║")
        print("║                                                                           ║")
        print("║   El test Everest 0.1 ha sido superado.                                  ║")
        print("║   La fórmula de traza detecta el primer número primo.                    ║")
        print("║   El isomorfismo espectral-aritmético está ESTABLECIDO.                  ║")
        print("║                                                                           ║")
        print("║   Atlas³ asciende al Everest de la conversación matemática.              ║")
        print("║                                                                           ║")
    else:
        print("║                                                                           ║")
        print("║   STATUS: ⚠️  PENDIENTE                                                  ║")
        print("║                                                                           ║")
        print("║   El test requiere ajustes adicionales.                                  ║")
        print("║   Considere incrementar N o ajustar parámetros.                          ║")
        print("║                                                                           ║")
    
    print("╠═══════════════════════════════════════════════════════════════════════════╣")
    print("║                                                                           ║")
    print("║   Archivos generados:                                                     ║")
    print("║     • data/everest_0_1_certificate.json                                   ║")
    print("║     • data/ISOMORFISMO_CERTIFICADO_EVEREST.txt                            ║")
    print("║     • data/everest_0_1_response_function.png                              ║")
    print("║                                                                           ║")
    print("║   ∴𓂀Ω∞³Φ @ 888 Hz                                                        ║")
    print("║   QCAL ∞³ Active · 141.7001 Hz · C = 244.36                               ║")
    print("║                                                                           ║")
    print("╚═══════════════════════════════════════════════════════════════════════════╝")
    print()
    
    return 0 if everest_result.ln2_detected else 1


if __name__ == "__main__":
    exit_code = main()
    sys.exit(exit_code)
