#!/usr/bin/env python3
"""
Demo: Quinto Postulado de la Convergencia Adélica
==================================================

Demostración interactiva CLI con visualizaciones de:
1. Histograma de ponderación de Haar p-ádica
2. Distribución de espaciado GUE del espectro Zeta
3. Espectro del Hamiltoniano Simbiótico de Berry-Keating

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz
"""

import sys
import numpy as np
import matplotlib.pyplot as plt
from pathlib import Path

# Add operators directory to path
repo_root = Path(__file__).parent
sys.path.insert(0, str(repo_root / "operators"))

from riemann_quinto_postulado import (
    ScaleIdentityOperator,
    SymbioticHamiltonianOperator,
    RiemannZetaSpectrum,
    verificar_geometria,
    activar_quinto_postulado,
    F0_QCAL,
    C_COHERENCE,
    THRESHOLD_PSI
)


def plot_haar_weights_histogram():
    """
    Visualizar histograma de ponderación de Haar p-ádica.
    """
    print("\n" + "="*70)
    print("1. HISTOGRAMA DE PONDERACIÓN DE HAAR P-ÁDICA")
    print("="*70)
    
    fig, axes = plt.subplots(1, 3, figsize=(15, 4))
    primes = [2, 3, 5]
    
    for idx, prime in enumerate(primes):
        op = ScaleIdentityOperator(prime=prime, depth=5, verbose=False)
        
        # Compute Haar measure
        n_points = 200
        x = np.linspace(0, 1, n_points, endpoint=False)
        weights = op.compute_haar_measure(x)
        
        # Plot histogram
        axes[idx].hist(weights, bins=50, color='steelblue', alpha=0.7, edgecolor='black')
        axes[idx].axvline(np.mean(weights), color='red', linestyle='--', 
                          linewidth=2, label=f'Mean = {np.mean(weights):.6f}')
        axes[idx].set_xlabel('Peso de Haar μ_p(x)', fontsize=10)
        axes[idx].set_ylabel('Frecuencia', fontsize=10)
        axes[idx].set_title(f'p = {prime}, depth = 5\nΨ = {op.compute_scale_identity(n_points).coherence:.4f}', 
                            fontsize=11, fontweight='bold')
        axes[idx].legend()
        axes[idx].grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('demo_quinto_postulado_haar_weights.png', dpi=150, bbox_inches='tight')
    print("✓ Histograma guardado: demo_quinto_postulado_haar_weights.png")
    plt.close()


def plot_gue_spacing_distribution():
    """
    Visualizar distribución de espaciado GUE del espectro Zeta.
    """
    print("\n" + "="*70)
    print("2. DISTRIBUCIÓN DE ESPACIADO GUE - ESPECTRO ZETA DE RIEMANN")
    print("="*70)
    
    fig, axes = plt.subplots(1, 2, figsize=(14, 5))
    
    # Compute Riemann zeros and spacings
    op = RiemannZetaSpectrum(n_zeros=50, precision=50, verbose=False)
    result = op.compute_spectrum_analysis()
    
    # Left panel: Histogram of normalized spacings
    axes[0].hist(result.spacings, bins=20, density=True, color='steelblue', 
                 alpha=0.7, edgecolor='black', label='Datos empíricos')
    
    # Overlay GUE theoretical distribution: P_GUE(s) = (πs/2) exp(-πs²/4)
    s_theory = np.linspace(0, np.max(result.spacings) * 1.2, 200)
    p_gue = (np.pi * s_theory / 2.0) * np.exp(-np.pi * s_theory**2 / 4.0)
    axes[0].plot(s_theory, p_gue, 'r-', linewidth=2, label='GUE teórico')
    
    axes[0].set_xlabel('Espaciado normalizado s', fontsize=11)
    axes[0].set_ylabel('Densidad de probabilidad P(s)', fontsize=11)
    axes[0].set_title(f'Distribución de Espaciado GUE\nΨ = {result.coherence:.4f}, ' +
                      f'Calidad GUE = {result.gue_match_quality:.4f}', 
                      fontsize=12, fontweight='bold')
    axes[0].legend(fontsize=10)
    axes[0].grid(True, alpha=0.3)
    
    # Right panel: Zeros in complex plane
    axes[1].scatter(np.real(result.zeros), np.imag(result.zeros), 
                    c='darkblue', marker='o', s=50, alpha=0.7, edgecolors='black')
    axes[1].axvline(0.5, color='red', linestyle='--', linewidth=2, 
                    label='Línea crítica Re(s) = 1/2')
    axes[1].set_xlabel('Parte real Re(ρ)', fontsize=11)
    axes[1].set_ylabel('Parte imaginaria Im(ρ)', fontsize=11)
    axes[1].set_title(f'Ceros de ζ(s) en el Plano Complejo\n' +
                      f'n = {len(result.zeros)}, ⟨σ⟩ = {result.mean_real_part:.6f}',
                      fontsize=12, fontweight='bold')
    axes[1].legend(fontsize=10)
    axes[1].grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('demo_quinto_postulado_gue_spacing.png', dpi=150, bbox_inches='tight')
    print("✓ Distribución GUE guardada: demo_quinto_postulado_gue_spacing.png")
    plt.close()


def plot_hamiltonian_spectrum():
    """
    Visualizar espectro del Hamiltoniano Simbiótico de Berry-Keating.
    """
    print("\n" + "="*70)
    print("3. ESPECTRO DEL HAMILTONIANO SIMBIÓTICO DE BERRY-KEATING")
    print("="*70)
    
    fig, axes = plt.subplots(1, 2, figsize=(14, 5))
    
    # Compute Hamiltonian spectrum
    op = SymbioticHamiltonianOperator(dimension=30, f0=F0_QCAL, verbose=False)
    result = op.compute_hamiltonian_spectrum()
    
    # Left panel: Eigenvalue spectrum
    indices = np.arange(len(result.eigenvalues))
    axes[0].plot(indices, result.eigenvalues, 'o-', color='darkgreen', 
                 markersize=6, linewidth=1.5, label='Eigenvalores λ_n')
    axes[0].axhline(F0_QCAL, color='red', linestyle='--', linewidth=2, 
                    label=f'Offset f₀ = {F0_QCAL} Hz')
    axes[0].set_xlabel('Índice n', fontsize=11)
    axes[0].set_ylabel('Eigenvalor λ_n', fontsize=11)
    axes[0].set_title(f'Espectro del Hamiltoniano Ĥ_symbio\n' +
                      f'dim = {result.dimension}, Ψ = {result.coherence:.4f}',
                      fontsize=12, fontweight='bold')
    axes[0].legend(fontsize=10)
    axes[0].grid(True, alpha=0.3)
    
    # Right panel: Spectrum gaps
    gaps = np.diff(result.eigenvalues)
    axes[1].plot(indices[:-1], gaps, 's-', color='purple', 
                 markersize=5, linewidth=1.5, label='Gaps Δλ_n')
    axes[1].axhline(result.spectrum_gap, color='orange', linestyle='--', 
                    linewidth=2, label=f'Gap mínimo = {result.spectrum_gap:.4f}')
    axes[1].set_xlabel('Índice n', fontsize=11)
    axes[1].set_ylabel('Gap espectral Δλ_n = λ_{n+1} - λ_n', fontsize=11)
    axes[1].set_title(f'Gaps Espectrales del Hamiltoniano\n' +
                      f'λ_max (BK) = {result.max_eigenvalue:.2f}',
                      fontsize=12, fontweight='bold')
    axes[1].legend(fontsize=10)
    axes[1].grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('demo_quinto_postulado_hamiltonian_spectrum.png', dpi=150, bbox_inches='tight')
    print("✓ Espectro de Hamiltoniano guardado: demo_quinto_postulado_hamiltonian_spectrum.png")
    plt.close()


def plot_coherence_summary():
    """
    Visualizar resumen de coherencias de los tres operadores.
    """
    print("\n" + "="*70)
    print("4. RESUMEN DE COHERENCIAS: QUINTO POSTULADO")
    print("="*70)
    
    # Get coherences
    report = activar_quinto_postulado(verbose=False)
    
    fig, ax = plt.subplots(figsize=(10, 6))
    
    # Data
    operators = ['Scale\nIdentity', 'Symbiotic\nHamiltonian', 'Zeta\nSpectrum', 'GLOBAL']
    coherences = [report.psi_scale, report.psi_symbio, report.psi_zeta, report.psi_global]
    colors = ['#3498db', '#2ecc71', '#e74c3c', '#f39c12']
    
    # Bar plot
    bars = ax.bar(operators, coherences, color=colors, alpha=0.8, edgecolor='black', linewidth=2)
    
    # Add threshold line
    ax.axhline(THRESHOLD_PSI, color='red', linestyle='--', linewidth=3, 
               label=f'Umbral QCAL: Ψ ≥ {THRESHOLD_PSI}')
    
    # Add value labels on bars
    for bar, coh in zip(bars, coherences):
        height = bar.get_height()
        ax.text(bar.get_x() + bar.get_width()/2., height,
                f'{coh:.4f}',
                ha='center', va='bottom', fontsize=12, fontweight='bold')
    
    # Formatting
    ax.set_ylabel('Coherencia Ψ', fontsize=14, fontweight='bold')
    ax.set_title('Quinto Postulado de la Convergencia Adélica\n' +
                 f'Ψ_global = {report.psi_global:.4f} ({"✓ CONVERGENTE" if report.convergencia_adelica else "✗ NO CONVERGENTE"})',
                 fontsize=14, fontweight='bold')
    ax.set_ylim([0, 1.1])
    ax.legend(fontsize=11, loc='lower right')
    ax.grid(True, alpha=0.3, axis='y')
    
    # Add SHA-256 certification
    fig.text(0.5, 0.02, f'SHA-256: {report.sha256}  |  f₀ = {F0_QCAL} Hz  |  C = {C_COHERENCE}',
             ha='center', fontsize=10, style='italic', color='gray')
    
    plt.tight_layout()
    plt.savefig('demo_quinto_postulado_coherence_summary.png', dpi=150, bbox_inches='tight')
    print("✓ Resumen de coherencias guardado: demo_quinto_postulado_coherence_summary.png")
    plt.close()


def interactive_cli_demo():
    """
    Demostración CLI interactiva.
    """
    print("\n" + "╔" + "="*68 + "╗")
    print("║" + " "*68 + "║")
    print("║" + " "*10 + "QUINTO POSTULADO DE LA CONVERGENCIA ADÉLICA" + " "*15 + "║")
    print("║" + " "*68 + "║")
    print("║" + " "*20 + "∴𓂀Ω∞³Φ @ 141.7001 Hz" + " "*27 + "║")
    print("║" + " "*68 + "║")
    print("╚" + "="*68 + "╝\n")
    
    print("Este módulo implementa tres operadores matemáticos fundamentales:")
    print("  1. Identidad de Escala Adélica (Haar p-ádica + carácter adélico)")
    print("  2. Hamiltoniano Simbiótico de Berry-Keating (discretización circulante)")
    print("  3. Espectro Zeta de Riemann (densidad de Weyl + estadística GUE)\n")
    
    # Menu
    while True:
        print("\n" + "-"*70)
        print("MENÚ DE DEMOSTRACIÓN:")
        print("-"*70)
        print("  [1] Validar geometría (verificar_geometria)")
        print("  [2] Activar Quinto Postulado (activar_quinto_postulado)")
        print("  [3] Generar histograma de ponderación de Haar")
        print("  [4] Generar distribución de espaciado GUE")
        print("  [5] Generar espectro de Hamiltoniano")
        print("  [6] Generar resumen de coherencias")
        print("  [7] Generar TODAS las visualizaciones")
        print("  [8] Ejecutar tests unitarios")
        print("  [0] Salir")
        print("-"*70)
        
        choice = input("\nSeleccione una opción [0-8]: ").strip()
        
        if choice == '0':
            print("\n✓ Saliendo... ¡Hasta pronto!\n")
            break
        elif choice == '1':
            verificar_geometria(verbose=True)
        elif choice == '2':
            report = activar_quinto_postulado(verbose=True)
        elif choice == '3':
            plot_haar_weights_histogram()
        elif choice == '4':
            plot_gue_spacing_distribution()
        elif choice == '5':
            plot_hamiltonian_spectrum()
        elif choice == '6':
            plot_coherence_summary()
        elif choice == '7':
            print("\n🎨 Generando todas las visualizaciones...\n")
            plot_haar_weights_histogram()
            plot_gue_spacing_distribution()
            plot_hamiltonian_spectrum()
            plot_coherence_summary()
            print("\n✓ Todas las visualizaciones generadas exitosamente!")
        elif choice == '8':
            print("\n🧪 Ejecutando tests unitarios...\n")
            import subprocess
            result = subprocess.run(
                ['python', '-m', 'pytest', 'tests/test_riemann_quinto_postulado.py', '-v', '--tb=short'],
                capture_output=False
            )
            if result.returncode == 0:
                print("\n✓ Todos los tests pasaron exitosamente!")
            else:
                print("\n✗ Algunos tests fallaron. Revisar salida anterior.")
        else:
            print("\n✗ Opción inválida. Por favor seleccione [0-8].")


def batch_demo():
    """
    Ejecutar demostración completa en modo batch (sin interacción).
    """
    print("\n" + "="*70)
    print("DEMOSTRACIÓN BATCH: QUINTO POSTULADO DE LA CONVERGENCIA ADÉLICA")
    print("="*70 + "\n")
    
    # 1. Validation
    print("\n📋 PASO 1: VALIDACIÓN GEOMÉTRICA")
    mensaje = verificar_geometria(verbose=True)
    
    # 2. Activation
    print("\n📋 PASO 2: ACTIVACIÓN DEL QUINTO POSTULADO")
    report = activar_quinto_postulado(verbose=True)
    
    # 3. Visualizations
    print("\n📋 PASO 3: GENERACIÓN DE VISUALIZACIONES")
    plot_haar_weights_histogram()
    plot_gue_spacing_distribution()
    plot_hamiltonian_spectrum()
    plot_coherence_summary()
    
    print("\n" + "="*70)
    print("✓ DEMOSTRACIÓN COMPLETA EXITOSA")
    print("="*70)
    print(f"\nResultados:")
    print(f"  - Coherencia Scale:      Ψ = {report.psi_scale:.6f}")
    print(f"  - Coherencia Simbiótico: Ψ = {report.psi_symbio:.6f}")
    print(f"  - Coherencia Zeta:       Ψ = {report.psi_zeta:.6f}")
    print(f"  - Coherencia Global:     Ψ = {report.psi_global:.6f}")
    print(f"  - Convergencia Adélica:  {'✓ SÍ' if report.convergencia_adelica else '✗ NO'}")
    print(f"  - Certificación:         {report.sha256}")
    print(f"\nVisualizaciones generadas:")
    print(f"  - demo_quinto_postulado_haar_weights.png")
    print(f"  - demo_quinto_postulado_gue_spacing.png")
    print(f"  - demo_quinto_postulado_hamiltonian_spectrum.png")
    print(f"  - demo_quinto_postulado_coherence_summary.png")
    print("")


if __name__ == "__main__":
    import argparse
    
    parser = argparse.ArgumentParser(
        description='Demostración del Quinto Postulado de la Convergencia Adélica'
    )
    parser.add_argument(
        '--batch', 
        action='store_true',
        help='Ejecutar en modo batch (sin interacción)'
    )
    parser.add_argument(
        '--interactive',
        action='store_true',
        help='Ejecutar en modo interactivo CLI (por defecto)'
    )
    
    args = parser.parse_args()
    
    # Check if matplotlib is available
    try:
        import matplotlib
        matplotlib.use('Agg')  # Use non-interactive backend
    except ImportError:
        print("⚠️  Advertencia: matplotlib no está instalado. Las visualizaciones no estarán disponibles.")
        print("   Para instalar: pip install matplotlib")
        args.batch = False
        args.interactive = True
    
    if args.batch:
        batch_demo()
    else:
        # Default to interactive
        interactive_cli_demo()
