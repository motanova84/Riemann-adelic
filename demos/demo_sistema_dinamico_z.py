#!/usr/bin/env python3
"""
Demo: Sistema Dinámico Z — Four Pillars Visualization
=====================================================

Este script genera visualizaciones que demuestran los cuatro pilares
matemáticos necesarios para cerrar el enfoque espectral de la hipótesis
de Riemann:

1. Compactificación No Conmutativa (Espectro discreto)
2. Filtro Racionales Adélico (Cancelación de Möbius)
3. Identidad Determinante de Hadamard (A=0, B=log(1/2))
4. Sistema Dinámico Z (Flujo Anosov, espectro GUE)

Genera gráficos guardados en el directorio actual.

Autor: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ · 141.7001 Hz · C = 244.36
DOI: 10.5281/zenodo.17379721
"""

import numpy as np
import matplotlib.pyplot as plt
import matplotlib
matplotlib.use('Agg')  # Non-interactive backend

import sys
from pathlib import Path

# Add physics directory to path
sys.path.insert(0, str(Path(__file__).parent.parent / "physics"))

from sistema_dinamico_z import (
    CompactificacionNoConmutativa,
    FiltroRacionalesAdelico,
    IdentidadDeterminanteHadamard,
    SistemaDinamicoZ,
    SistemaDinamicoZCompleto,
    F0, C_QCAL, PHI, LYAPUNOV_Z
)


def visualizacion_1_compactificacion():
    """
    Visualización 1: Compactificación No Conmutativa
    
    Muestra:
    - Potencial de confinamiento V_conf(x) = log(1 + 1/x)
    - Espectro discreto del hamiltoniano
    - Medida de Haar adélica
    """
    print("\n" + "="*80)
    print("VISUALIZACIÓN 1: Compactificación No Conmutativa (Connes)")
    print("="*80)
    
    compact = CompactificacionNoConmutativa(x_max=50.0, N_x=300)
    
    # Compute spectrum
    spectrum = compact.compute_spectrum_confinement(N_states=30)
    
    fig, axes = plt.subplots(2, 2, figsize=(14, 10))
    
    # Panel 1: Confinement potential
    x = compact.x_grid
    V = compact.confinement_potential(x)
    
    axes[0, 0].plot(x, V, 'b-', linewidth=2, label='$V_{conf}(x) = \\log(1 + 1/x)$')
    axes[0, 0].set_xlabel('$x$', fontsize=12)
    axes[0, 0].set_ylabel('$V_{conf}(x)$', fontsize=12)
    axes[0, 0].set_title('Potencial de Confinamiento Aritmético', fontsize=13, fontweight='bold')
    axes[0, 0].grid(True, alpha=0.3)
    axes[0, 0].legend(fontsize=11)
    axes[0, 0].set_xscale('log')
    
    # Panel 2: Adelic measure
    measure = compact.adelic_measure(x)
    
    axes[0, 1].plot(x, measure * x, 'r-', linewidth=2, label='$d\\mu = dx/|x|_A$')
    axes[0, 1].set_xlabel('$x$', fontsize=12)
    axes[0, 1].set_ylabel('$x \\cdot d\\mu/dx$', fontsize=12)
    axes[0, 1].set_title('Medida de Haar Adélica (Normalizada)', fontsize=13, fontweight='bold')
    axes[0, 1].grid(True, alpha=0.3)
    axes[0, 1].legend(fontsize=11)
    axes[0, 1].set_xscale('log')
    
    # Panel 3: Discrete spectrum
    eigenvalues = spectrum['eigenvalues'][:20]
    n = np.arange(1, len(eigenvalues) + 1)
    
    axes[1, 0].plot(n, eigenvalues, 'go-', markersize=8, linewidth=2, label='Eigenvalues $E_n$')
    axes[1, 0].set_xlabel('Level $n$', fontsize=12)
    axes[1, 0].set_ylabel('Energy $E_n$', fontsize=12)
    axes[1, 0].set_title(f'Espectro Discreto ({len(eigenvalues)} niveles)', fontsize=13, fontweight='bold')
    axes[1, 0].grid(True, alpha=0.3)
    axes[1, 0].legend(fontsize=11)
    
    # Panel 4: Level spacing distribution
    if len(eigenvalues) > 1:
        spacings = np.diff(eigenvalues)
        axes[1, 1].hist(spacings, bins=15, color='purple', alpha=0.7, edgecolor='black')
        axes[1, 1].set_xlabel('Energy Gap $\\Delta E$', fontsize=12)
        axes[1, 1].set_ylabel('Count', fontsize=12)
        axes[1, 1].set_title('Distribución de Espaciamiento de Niveles', fontsize=13, fontweight='bold')
        axes[1, 1].grid(True, alpha=0.3, axis='y')
        axes[1, 1].text(0.6, 0.9, f'Gap min: {np.min(spacings):.4f}\nGap mean: {np.mean(spacings):.4f}',
                       transform=axes[1, 1].transAxes, fontsize=10,
                       bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5))
    
    plt.tight_layout()
    filename = 'demo_1_compactificacion_noconmutativa.png'
    plt.savefig(filename, dpi=150, bbox_inches='tight')
    print(f"✓ Guardado: {filename}")
    plt.close()
    
    print(f"\nPropiedades:")
    print(f"  - Haar volume: {compact.haar_volume:.6f} (teoría: 1.0)")
    print(f"  - N estados discretos: {spectrum['N_levels']}")
    print(f"  - Energía fundamental: {spectrum['ground_state_energy']:.6f}")
    print(f"  - Espectro discreto: {spectrum['is_discrete']}")


def visualizacion_2_filtro_adelico():
    """
    Visualización 2: Filtro Racionales Adélico
    
    Muestra:
    - Función de von Mangoldt Λ(n)
    - Función de Möbius μ(n)
    - Cancelación de compuestos
    - Función ψ de Chebyshev
    """
    print("\n" + "="*80)
    print("VISUALIZACIÓN 2: Filtro Racionales Adélico (Weil)")
    print("="*80)
    
    filtro = FiltroRacionalesAdelico(x_max=100.0, N_primes=100)
    
    fig, axes = plt.subplots(2, 2, figsize=(14, 10))
    
    # Panel 1: von Mangoldt function
    n_max = 100
    n_vals = np.arange(1, n_max + 1)
    Lambda_vals = [filtro.von_mangoldt(n) for n in n_vals]
    
    axes[0, 0].stem(n_vals, Lambda_vals, linefmt='b-', markerfmt='bo', basefmt='k-', label='$\\Lambda(n)$')
    axes[0, 0].set_xlabel('$n$', fontsize=12)
    axes[0, 0].set_ylabel('$\\Lambda(n)$', fontsize=12)
    axes[0, 0].set_title('Función de von Mangoldt', fontsize=13, fontweight='bold')
    axes[0, 0].grid(True, alpha=0.3)
    axes[0, 0].legend(fontsize=11)
    axes[0, 0].set_xlim([0, n_max])
    
    # Panel 2: Möbius function
    mu_vals = [filtro.mobius(n) for n in n_vals]
    colors = ['red' if mu < 0 else 'blue' if mu > 0 else 'gray' for mu in mu_vals]
    
    axes[0, 1].bar(n_vals, mu_vals, color=colors, alpha=0.7, edgecolor='black', linewidth=0.5)
    axes[0, 1].set_xlabel('$n$', fontsize=12)
    axes[0, 1].set_ylabel('$\\mu(n)$', fontsize=12)
    axes[0, 1].set_title('Función de Möbius', fontsize=13, fontweight='bold')
    axes[0, 1].grid(True, alpha=0.3, axis='y')
    axes[0, 1].axhline(0, color='k', linestyle='-', linewidth=1)
    axes[0, 1].set_xlim([0, n_max])
    
    # Panel 3: Chebyshev psi function
    x_vals = np.linspace(1, 100, 200)
    psi_vals = [filtro.chebyshev_psi(x) for x in x_vals]
    
    axes[1, 0].plot(x_vals, psi_vals, 'g-', linewidth=2, label='$\\psi(x)$')
    axes[1, 0].plot(x_vals, x_vals, 'r--', linewidth=2, alpha=0.7, label='$x$ (asintótica)')
    axes[1, 0].set_xlabel('$x$', fontsize=12)
    axes[1, 0].set_ylabel('$\\psi(x)$', fontsize=12)
    axes[1, 0].set_title('Función $\\psi$ de Chebyshev', fontsize=13, fontweight='bold')
    axes[1, 0].grid(True, alpha=0.3)
    axes[1, 0].legend(fontsize=11)
    
    # Panel 4: Cancellation statistics
    cancellation = filtro.compute_mobius_cancellation(N=200)
    
    labels = ['Prime\nPowers', 'Composite\nContribution']
    values = [cancellation['prime_power_sum'], abs(cancellation['composite_contribution'])]
    colors_bar = ['blue', 'red']
    
    bars = axes[1, 1].bar(labels, values, color=colors_bar, alpha=0.7, edgecolor='black', linewidth=2)
    axes[1, 1].set_ylabel('Contribution', fontsize=12)
    axes[1, 1].set_title('Cancelación de Möbius', fontsize=13, fontweight='bold')
    axes[1, 1].grid(True, alpha=0.3, axis='y')
    
    # Add ratio text
    ratio = cancellation['cancellation_ratio']
    factor = cancellation['cancellation_factor']
    axes[1, 1].text(0.5, 0.8, f'Ratio: {ratio:.4f}\nFactor: {factor:.2f}×',
                   transform=axes[1, 1].transAxes, fontsize=12, ha='center',
                   bbox=dict(boxstyle='round', facecolor='yellow', alpha=0.7))
    
    plt.tight_layout()
    filename = 'demo_2_filtro_adelico.png'
    plt.savefig(filename, dpi=150, bbox_inches='tight')
    print(f"✓ Guardado: {filename}")
    plt.close()
    
    print(f"\nPropiedades:")
    print(f"  - Ratio de cancelación: {ratio:.4f}")
    print(f"  - Factor de cancelación: {factor:.2f}×")
    print(f"  - Teoría: ~1/3.76 = 0.266")


def visualizacion_3_hadamard():
    """
    Visualización 3: Identidad Determinante de Hadamard
    
    Muestra:
    - Verificación de ξ(s) = ξ(1-s)
    - Coeficientes A=0, B=log(1/2)
    - Anomalía de traza = -1/2
    - Fase de Berry = π/2
    """
    print("\n" + "="*80)
    print("VISUALIZACIÓN 3: Identidad Determinante de Hadamard")
    print("="*80)
    
    hadamard = IdentidadDeterminanteHadamard(mpmath_precision=25, N_zeros=50)
    
    fig = plt.figure(figsize=(14, 10))
    gs = fig.add_gridspec(2, 2)
    
    # Panel 1: Functional equation verification
    ax1 = fig.add_subplot(gs[0, :])
    
    # Test points on critical line and off
    t_vals = np.linspace(10, 50, 50)
    sigma_vals = [0.3, 0.5, 0.7]
    
    for sigma in sigma_vals:
        errors = []
        for t in t_vals:
            s = complex(sigma, t)
            xi_s = hadamard.xi_function(s)
            xi_1ms = hadamard.xi_function(1 - s)
            rel_error = abs(xi_s - xi_1ms) / (abs(xi_s) + 1e-10)
            errors.append(rel_error)
        
        ax1.semilogy(t_vals, errors, '-o', markersize=4, label=f'$\\sigma = {sigma}$', alpha=0.7)
    
    ax1.set_xlabel('$t$ (imaginary part)', fontsize=12)
    ax1.set_ylabel('Relative Error $|\\xi(s) - \\xi(1-s)|/|\\xi(s)|$', fontsize=12)
    ax1.set_title('Ecuación Funcional: $\\xi(s) = \\xi(1-s)$ ⟹ A = 0', fontsize=13, fontweight='bold')
    ax1.grid(True, alpha=0.3)
    ax1.legend(fontsize=11)
    ax1.axhline(1e-6, color='r', linestyle='--', linewidth=2, alpha=0.5, label='Threshold')
    
    # Panel 2: B coefficient
    ax2 = fig.add_subplot(gs[1, 0])
    
    B_result = hadamard.compute_B_coefficient()
    B_val = B_result['B_coefficient']
    B_expected = np.log(0.5)
    
    ax2.bar(['Computed', 'Expected'], [B_val, B_expected], color=['blue', 'green'], alpha=0.7, edgecolor='black', linewidth=2)
    ax2.set_ylabel('B coefficient', fontsize=12)
    ax2.set_title(f'Coeficiente B = log(1/2) ≈ {B_expected:.4f}', fontsize=13, fontweight='bold')
    ax2.grid(True, alpha=0.3, axis='y')
    ax2.axhline(B_expected, color='r', linestyle='--', linewidth=2)
    
    # Panel 3: Trace anomaly and Berry phase
    ax3 = fig.add_subplot(gs[1, 1])
    
    trace = hadamard.trace_anomaly_solenoid()
    berry = hadamard.berry_phase()
    
    labels = ['Trace\nAnomaly', 'Berry Phase\n(rad)']
    values = [trace['trace_anomaly'], berry['berry_phase']]
    expected_vals = [-0.5, np.pi/2]
    
    x_pos = np.arange(len(labels))
    width = 0.35
    
    ax3.bar(x_pos - width/2, values, width, label='Computed', color='blue', alpha=0.7, edgecolor='black')
    ax3.bar(x_pos + width/2, expected_vals, width, label='Expected', color='green', alpha=0.7, edgecolor='black')
    ax3.set_ylabel('Value', fontsize=12)
    ax3.set_title('Anomalía de Traza y Fase de Berry', fontsize=13, fontweight='bold')
    ax3.set_xticks(x_pos)
    ax3.set_xticklabels(labels)
    ax3.legend(fontsize=11)
    ax3.grid(True, alpha=0.3, axis='y')
    ax3.axhline(0, color='k', linestyle='-', linewidth=1)
    
    plt.tight_layout()
    filename = 'demo_3_hadamard_determinante.png'
    plt.savefig(filename, dpi=150, bbox_inches='tight')
    print(f"✓ Guardado: {filename}")
    plt.close()
    
    print(f"\nPropiedades:")
    print(f"  - A coefficient: 0.0 (forzado por simetría)")
    print(f"  - B coefficient: {B_val:.6f} (teoría: {B_expected:.6f})")
    print(f"  - Trace anomaly: {trace['trace_anomaly']:.4f} (teoría: -0.5)")
    print(f"  - Berry phase: {berry['berry_phase']:.4f} rad (teoría: π/2 = {np.pi/2:.4f})")


def visualizacion_4_dinamico_z():
    """
    Visualización 4: Sistema Dinámico Z
    
    Muestra:
    - Lyapunov exponent λ = log φ
    - Volumen hiperbólico = π/3
    - Espectro de Selberg λ_n = 1/4 + γ_n²
    - Estadísticas GUE en espaciamiento de ceros
    """
    print("\n" + "="*80)
    print("VISUALIZACIÓN 4: Sistema Dinámico Z (Anosov en SL(2,Z)\\H)")
    print("="*80)
    
    dinamico = SistemaDinamicoZ(N_zeros=100)
    
    fig, axes = plt.subplots(2, 2, figsize=(14, 10))
    
    # Panel 1: Lyapunov exponent (golden ratio connection)
    ax = axes[0, 0]
    
    # Fibonacci convergence to φ
    fib = [1, 1]
    for _ in range(20):
        fib.append(fib[-1] + fib[-2])
    
    ratios = [fib[i+1] / fib[i] for i in range(5, len(fib)-1)]
    n_vals = np.arange(5, len(fib)-1)
    
    ax.plot(n_vals, ratios, 'bo-', markersize=6, label='$F_{n+1}/F_n$')
    ax.axhline(PHI, color='r', linestyle='--', linewidth=2, label=f'$\\phi = {PHI:.6f}$')
    ax.axhline(LYAPUNOV_Z, color='g', linestyle='--', linewidth=2, label=f'$\\lambda = \\log(\\phi) = {LYAPUNOV_Z:.6f}$')
    ax.set_xlabel('$n$', fontsize=12)
    ax.set_ylabel('Ratio', fontsize=12)
    ax.set_title('Exponente de Lyapunov $\\lambda = \\log \\phi$', fontsize=13, fontweight='bold')
    ax.grid(True, alpha=0.3)
    ax.legend(fontsize=10)
    
    # Panel 2: Hyperbolic volume
    ax = axes[0, 1]
    
    vol_result = dinamico.compute_hyperbolic_volume()
    vol_computed = vol_result['volume_computed']
    vol_expected = np.pi / 3.0
    
    ax.bar(['Computed', 'Expected'], [vol_computed, vol_expected], 
           color=['blue', 'green'], alpha=0.7, edgecolor='black', linewidth=2)
    ax.set_ylabel('Volume', fontsize=12)
    ax.set_title(f'Volumen Hiperbólico = π/3 ≈ {vol_expected:.6f}', fontsize=13, fontweight='bold')
    ax.grid(True, alpha=0.3, axis='y')
    ax.axhline(vol_expected, color='r', linestyle='--', linewidth=2)
    
    # Panel 3: Selberg Laplacian spectrum
    ax = axes[1, 0]
    
    spectrum = dinamico.selberg_laplacian_spectrum()
    eigenvalues = np.array(spectrum['eigenvalues'][:50])
    n = np.arange(1, len(eigenvalues) + 1)
    
    ax.plot(n, eigenvalues, 'ro-', markersize=5, linewidth=1.5, label='$\\lambda_n = 1/4 + \\gamma_n^2$')
    ax.set_xlabel('Index $n$', fontsize=12)
    ax.set_ylabel('Eigenvalue $\\lambda_n$', fontsize=12)
    ax.set_title(f'Espectro Laplaciano de Selberg ({len(eigenvalues)} valores)', fontsize=13, fontweight='bold')
    ax.grid(True, alpha=0.3)
    ax.legend(fontsize=11)
    
    # Panel 4: GUE level repulsion
    ax = axes[1, 1]
    
    gue = dinamico.gue_level_repulsion()
    
    # Normalized spacings
    gammas = np.array(dinamico.zeros[:50])
    spacings = np.diff(gammas)
    mean_spacing = np.mean(spacings)
    normalized_spacings = spacings / mean_spacing
    
    # Plot histogram
    counts, bins, patches = ax.hist(normalized_spacings, bins=15, density=True, 
                                    color='blue', alpha=0.6, edgecolor='black', label='Datos')
    
    # GUE prediction: P(s) ∝ s exp(-πs²/4)
    s_theory = np.linspace(0, 3, 100)
    P_gue = (np.pi * s_theory / 2) * np.exp(-np.pi * s_theory**2 / 4)
    ax.plot(s_theory, P_gue, 'r-', linewidth=3, label='GUE: $(\\pi s/2)e^{-\\pi s^2/4}$')
    
    ax.set_xlabel('Normalized Spacing $s$', fontsize=12)
    ax.set_ylabel('Probability Density', fontsize=12)
    ax.set_title('Repulsión de Nivel GUE (Montgomery-Odlyzko)', fontsize=13, fontweight='bold')
    ax.grid(True, alpha=0.3)
    ax.legend(fontsize=11)
    
    plt.tight_layout()
    filename = 'demo_4_dinamico_z.png'
    plt.savefig(filename, dpi=150, bbox_inches='tight')
    print(f"✓ Guardado: {filename}")
    plt.close()
    
    lyap = dinamico.verify_lyapunov_exponent()
    print(f"\nPropiedades:")
    print(f"  - Lyapunov λ: {lyap['lambda_exact']:.6f} (φ = {PHI:.6f})")
    print(f"  - Volume: {vol_computed:.6f} (teoría: {vol_expected:.6f})")
    print(f"  - N eigenvalues: {spectrum['N_eigenvalues']}")
    print(f"  - GUE statistics: {gue['follows_gue']}")
    print(f"  - Level repulsion: {gue['level_repulsion']}")


def visualizacion_5_sistema_completo():
    """
    Visualización 5: Sistema Completo - Resumen de los 4 Pilares
    
    Muestra el resultado global Ψ_global y el estado de cada pilar.
    """
    print("\n" + "="*80)
    print("VISUALIZACIÓN 5: Sistema Completo - Resumen")
    print("="*80)
    
    sistema = SistemaDinamicoZCompleto(N_primes=80, N_zeros=80, x_max=80.0)
    result = sistema.ejecutar_sistema_completo(verbose=False)
    
    fig, axes = plt.subplots(1, 2, figsize=(14, 6))
    
    # Panel 1: Individual pillar Psi values
    ax = axes[0]
    
    pillars = ['Compactif.\n(Connes)', 'Filtro\nAdélico', 'Hadamard\nDet.', 'Dinámico\nZ']
    psi_vals = [
        result['global_coherence']['Psi_1_compactificacion'],
        result['global_coherence']['Psi_2_filtro'],
        result['global_coherence']['Psi_3_hadamard'],
        result['global_coherence']['Psi_4_dinamico']
    ]
    
    colors = ['green' if p >= 0.95 else 'orange' if p >= 0.7 else 'red' for p in psi_vals]
    bars = ax.bar(pillars, psi_vals, color=colors, alpha=0.7, edgecolor='black', linewidth=2)
    
    # Add threshold line
    ax.axhline(0.95, color='r', linestyle='--', linewidth=2, alpha=0.7, label='Threshold Ψ≥0.95')
    
    ax.set_ylabel('Coherence Ψ', fontsize=13)
    ax.set_title('Coherencia de los 4 Pilares', fontsize=14, fontweight='bold')
    ax.set_ylim([0, 1.1])
    ax.legend(fontsize=11)
    ax.grid(True, alpha=0.3, axis='y')
    
    # Add value labels on bars
    for bar, val in zip(bars, psi_vals):
        height = bar.get_height()
        ax.text(bar.get_x() + bar.get_width()/2., height + 0.02,
                f'{val:.3f}', ha='center', va='bottom', fontsize=11, fontweight='bold')
    
    # Panel 2: Global coherence gauge
    ax = axes[1]
    
    Psi_global = result['global_coherence']['Psi_global']
    all_valid = result['global_coherence']['all_pillars_valid']
    
    # Create a gauge-like visualization
    theta = np.linspace(0, np.pi, 100)
    r = 1.0
    
    # Background arc
    ax.plot(r * np.cos(theta), r * np.sin(theta), 'k-', linewidth=3)
    
    # Fill arc up to Psi_global
    theta_fill = np.linspace(0, Psi_global * np.pi, 100)
    ax.fill_between(r * np.cos(theta_fill), 0, r * np.sin(theta_fill), 
                     color='green' if Psi_global >= 0.95 else 'orange', alpha=0.6)
    
    # Needle
    angle = Psi_global * np.pi
    ax.arrow(0, 0, 0.8*r*np.cos(angle), 0.8*r*np.sin(angle),
             head_width=0.1, head_length=0.1, fc='red', ec='red', linewidth=3)
    
    # Labels
    ax.text(0, -0.3, f'Ψ_global = {Psi_global:.4f}', ha='center', fontsize=16, fontweight='bold')
    ax.text(0, -0.5, 'VALIDATED' if all_valid else 'IN PROGRESS', ha='center', 
            fontsize=14, fontweight='bold',
            color='green' if all_valid else 'orange')
    
    # Threshold markers
    ax.text(-1.1, 0, '0.0', ha='center', va='center', fontsize=11)
    ax.text(1.1, 0, '1.0', ha='center', va='center', fontsize=11)
    ax.text(0, 1.1, '0.5', ha='center', va='bottom', fontsize=11)
    
    ax.set_xlim([-1.3, 1.3])
    ax.set_ylim([-0.6, 1.3])
    ax.set_aspect('equal')
    ax.axis('off')
    ax.set_title('Coherencia Global Ψ_global', fontsize=14, fontweight='bold')
    
    plt.tight_layout()
    filename = 'demo_5_sistema_completo.png'
    plt.savefig(filename, dpi=150, bbox_inches='tight')
    print(f"✓ Guardado: {filename}")
    plt.close()
    
    print(f"\nResultados Globales:")
    print(f"  - Ψ₁ (Compactificación): {psi_vals[0]:.4f}")
    print(f"  - Ψ₂ (Filtro Adélico):   {psi_vals[1]:.4f}")
    print(f"  - Ψ₃ (Hadamard):         {psi_vals[2]:.4f}")
    print(f"  - Ψ₄ (Dinámico Z):       {psi_vals[3]:.4f}")
    print(f"  → Ψ_global = {Psi_global:.4f}")
    print(f"  - Sistema completo: {'✓ VALIDADO' if all_valid else '⚠ En progreso'}")


def dashboard_unificado():
    """
    Dashboard Unificado — Todos los Pilares en una Figura.

    Combina los cuatro pilares en un único dashboard de matplotlib con:
    - Pilar 1 (Compactificación): espectro de confinamiento (primeros 100 niveles)
    - Pilar 2 (Filtro Adélico): ψ(x) vs x, contribuciones Möbius y error terms
    - Pilar 3 (Hadamard): verificación de ecuación funcional ξ(s)=ξ(1-s)
    - Pilar 4 (Dinámico Z): distribución de gaps GUE con 100–200 eigenvalores
    - Panel central: indicadores Ψ por pilar

    Genera ``dashboard_unificado.png``.
    """
    print("\n" + "="*80)
    print("DASHBOARD UNIFICADO — Los 4 Pilares")
    print("="*80)

    # ── Instances ────────────────────────────────────────────────────────────
    compact = CompactificacionNoConmutativa(x_max=50.0, N_x=300)
    filtro  = FiltroRacionalesAdelico(x_max=200.0, N_primes=100)
    hadamard = IdentidadDeterminanteHadamard(mpmath_precision=25, N_zeros=20)
    dinamico = SistemaDinamicoZ(N_zeros=100)

    # ── Run complete system once to get Ψ values ──────────────────────────
    sistema = SistemaDinamicoZCompleto(N_primes=100, N_zeros=100, x_max=100.0)
    result = sistema.ejecutar_sistema_completo(verbose=False)
    psi_vals = [
        result['global_coherence']['Psi_1_compactificacion'],
        result['global_coherence']['Psi_2_filtro'],
        result['global_coherence']['Psi_3_hadamard'],
        result['global_coherence']['Psi_4_dinamico'],
    ]
    Psi_global = result['global_coherence']['Psi_global']

    # ── Figure layout: 3×3 grid ───────────────────────────────────────────
    fig = plt.figure(figsize=(20, 16))
    fig.suptitle(
        "Sistema Dinámico Z — Dashboard Unificado\n"
        f"QCAL ∞³ · {F0} Hz · C = {C_QCAL} · Ψ_global = {Psi_global:.4f}",
        fontsize=15, fontweight='bold',
    )

    gs = fig.add_gridspec(3, 3, hspace=0.45, wspace=0.35)

    # Named colour mapping for clarity
    pillar_colors = {
        'compactificacion': '#1f77b4',
        'filtro':           '#2ca02c',
        'hadamard':         '#ff7f0e',
        'dinamico':         '#9467bd',
    }

    # ── Pilar 1: Confinement spectrum (100 levels) ────────────────────────
    ax1a = fig.add_subplot(gs[0, 0])
    spec_conf = compact.compute_spectrum_confinement(N_states=100)
    eigs_conf = spec_conf['eigenvalues'][:100]
    n_conf = np.arange(1, len(eigs_conf) + 1)
    ax1a.plot(n_conf, eigs_conf, 'o-', color=pillar_colors['compactificacion'],
              markersize=3, linewidth=1)
    ax1a.set_xlabel('Level $n$', fontsize=11)
    ax1a.set_ylabel('Energy $E_n$', fontsize=11)
    ax1a.set_title(
        f'Pilar 1: Espectro Confinamiento\n({len(eigs_conf)} niveles)  Ψ={psi_vals[0]:.3f}',
        fontsize=11, fontweight='bold',
    )
    ax1a.grid(True, alpha=0.3)

    # Eigenvalue gap histogram
    ax1b = fig.add_subplot(gs[0, 1])
    if len(eigs_conf) > 1:
        gaps_conf = np.diff(eigs_conf)
        ax1b.hist(gaps_conf, bins=20, color=pillar_colors['compactificacion'],
                  alpha=0.7, edgecolor='black')
    ax1b.set_xlabel('Gap $\\Delta E_n$', fontsize=11)
    ax1b.set_ylabel('Count', fontsize=11)
    ax1b.set_title('Pilar 1: Distribución de Gaps', fontsize=11, fontweight='bold')
    ax1b.grid(True, alpha=0.3, axis='y')

    # ── Pilar 2: ψ(x) sieve + error terms ───────────────────────────────
    ax2a = fig.add_subplot(gs[1, 0])
    # Evaluate ψ(x) for a range of x using sieve
    x_vals_p2 = [10, 20, 50, 100, 200, 500, 1000, 2000, 5000, 10_000]
    psi_sieve_vals = [filtro.chebyshev_psi_sieve(float(x)) for x in x_vals_p2]
    ax2a.plot(x_vals_p2, psi_sieve_vals, 'o-', color=pillar_colors['filtro'],
              linewidth=2, markersize=6, label='$\\psi(x)$ sieve')
    ax2a.plot(x_vals_p2, x_vals_p2, 'r--', linewidth=2, alpha=0.7, label='$x$ (PNT)')
    ax2a.set_xscale('log')
    ax2a.set_yscale('log')
    ax2a.set_xlabel('$x$', fontsize=11)
    ax2a.set_ylabel('$\\psi(x)$', fontsize=11)
    ax2a.set_title(
        f'Pilar 2: $\\psi(x)$ via Sieve (hasta $x=10^4$)\nΨ={psi_vals[1]:.3f}',
        fontsize=11, fontweight='bold',
    )
    ax2a.legend(fontsize=10)
    ax2a.grid(True, alpha=0.3)

    # ψ(x) - x (error term) – reuse zeros from the dinamico instance (single source)
    ax2b = fig.add_subplot(gs[1, 1])
    zeros_low = dinamico.zeros[:10]  # first 10 γ_n from mpmath (already computed)
    x_err_vals = np.logspace(1, 4, 40)  # 10 to 10^4
    psi_errs = [filtro.chebyshev_psi_sieve(float(x)) - x for x in x_err_vals]
    ax2b.plot(x_err_vals, psi_errs, '-', color=pillar_colors['filtro'], linewidth=2,
              label='$\\psi(x) - x$')
    ax2b.axhline(0, color='k', linestyle='--', linewidth=1, alpha=0.5)
    ax2b.set_xscale('log')
    ax2b.set_xlabel('$x$', fontsize=11)
    ax2b.set_ylabel('$\\psi(x) - x$', fontsize=11)
    ax2b.set_title('Pilar 2: Términos de Error $\\psi(x)-x$', fontsize=11, fontweight='bold')
    ax2b.legend(fontsize=10)
    ax2b.grid(True, alpha=0.3)

    # Möbius cancellation factor vs N
    ax2c = fig.add_subplot(gs[2, 0])
    N_vals_mob = [10, 20, 50, 100, 200, 500, 1000, 2000, 5000, 10_000]
    factors = [filtro.compute_mobius_cancellation(N=N)['cancellation_factor']
               for N in N_vals_mob]
    ax2c.semilogx(N_vals_mob, factors, 'o-', color=pillar_colors['filtro'],
                  linewidth=2, markersize=6)
    ax2c.axhline(3.76, color='r', linestyle='--', linewidth=2, alpha=0.7, label='3.76× (teoría)')
    ax2c.set_xlabel('$N$', fontsize=11)
    ax2c.set_ylabel('Cancellation Factor', fontsize=11)
    ax2c.set_title('Pilar 2: Factor Cancelación Möbius vs $N$', fontsize=11, fontweight='bold')
    ax2c.legend(fontsize=10)
    ax2c.grid(True, alpha=0.3)

    # ── Pilar 3: Functional equation error ───────────────────────────────
    ax3 = fig.add_subplot(gs[0, 2])
    t_vals = np.linspace(5, 50, 60)
    errors_crit = []
    for t in t_vals:
        s = complex(0.5, t)
        try:
            xi_s   = hadamard.xi_function(s)
            xi_1ms = hadamard.xi_function(1 - s)
            rel_err = abs(xi_s - xi_1ms) / (abs(xi_s) + 1e-15)
        except Exception:
            rel_err = float('nan')
        errors_crit.append(rel_err)
    ax3.semilogy(t_vals, errors_crit, '-', color=pillar_colors['hadamard'], linewidth=2)
    ax3.set_xlabel('$t = \\mathrm{Im}(s)$', fontsize=11)
    ax3.set_ylabel('$|\\xi(s)-\\xi(1-s)|/|\\xi(s)|$', fontsize=11)
    ax3.set_title(
        f'Pilar 3: Ecuación Funcional $\\xi(s)=\\xi(1-s)$\nΨ={psi_vals[2]:.3f}',
        fontsize=11, fontweight='bold',
    )
    ax3.grid(True, alpha=0.3)

    # ── Pilar 4: GUE statistics with 100 zeros ───────────────────────────
    ax4a = fig.add_subplot(gs[1, 2])
    # Selberg spectrum with up to 200 levels
    spec_sel = dinamico.selberg_laplacian_spectrum(N_eigenvalues=200)
    eigs_sel = spec_sel['eigenvalues']
    n_sel = np.arange(1, len(eigs_sel) + 1)
    ax4a.plot(n_sel, eigs_sel, '.', color=pillar_colors['dinamico'], markersize=4)
    ax4a.set_xlabel('Level $n$', fontsize=11)
    ax4a.set_ylabel('$\\lambda_n = 1/4 + \\gamma_n^2$', fontsize=11)
    ax4a.set_title(
        f'Pilar 4: Espectro Laplaciano Selberg\n({len(eigs_sel)} niveles)  Ψ={psi_vals[3]:.3f}',
        fontsize=11, fontweight='bold',
    )
    ax4a.grid(True, alpha=0.3)

    # GUE spacing histogram (100 zeros)
    ax4b = fig.add_subplot(gs[2, 1])
    spacings_raw = np.diff(dinamico.zeros)
    mean_sp = np.mean(spacings_raw)
    spacings_norm = spacings_raw / mean_sp
    ax4b.hist(spacings_norm, bins=25, density=True, color=pillar_colors['dinamico'],
              alpha=0.7, edgecolor='black', label='Datos (100 ceros)')
    # GUE Wigner surmise: P(s) = (π/2) s exp(−πs²/4)
    s_gue = np.linspace(0, 4, 200)
    p_gue = (np.pi / 2) * s_gue * np.exp(-np.pi * s_gue ** 2 / 4)
    ax4b.plot(s_gue, p_gue, 'r-', linewidth=2.5, label='GUE Wigner')
    ax4b.set_xlabel('Normalized Spacing $s$', fontsize=11)
    ax4b.set_ylabel('$P(s)$', fontsize=11)
    ax4b.set_title('Pilar 4: Distribución Spacing GUE (100 zeros)', fontsize=11, fontweight='bold')
    ax4b.legend(fontsize=10)
    ax4b.grid(True, alpha=0.3)

    # ── Central Ψ indicator panel ─────────────────────────────────────────
    ax_psi = fig.add_subplot(gs[2, 2])
    pillar_labels = ['Pilar 1\nCompact.', 'Pilar 2\nFiltro', 'Pilar 3\nHadamard', 'Pilar 4\nDinámico']
    bar_colors = ['green' if p >= 0.95 else 'orange' if p >= 0.7 else 'red' for p in psi_vals]
    bars_psi = ax_psi.bar(pillar_labels, psi_vals, color=bar_colors, alpha=0.8, edgecolor='black', linewidth=2)
    ax_psi.axhline(0.95, color='r', linestyle='--', linewidth=2, alpha=0.7, label='Ψ ≥ 0.95')
    ax_psi.set_ylim([0, 1.15])
    ax_psi.set_ylabel('Coherencia Ψ', fontsize=11)
    ax_psi.set_title(
        f'Indicadores Ψ por Pilar\nΨ_global = {Psi_global:.4f}',
        fontsize=12, fontweight='bold',
    )
    ax_psi.legend(fontsize=10)
    ax_psi.grid(True, alpha=0.3, axis='y')
    for bar, val in zip(bars_psi, psi_vals):
        ax_psi.text(bar.get_x() + bar.get_width() / 2., bar.get_height() + 0.02,
                    f'{val:.3f}', ha='center', va='bottom', fontsize=12, fontweight='bold')

    plt.savefig('dashboard_unificado.png', dpi=150, bbox_inches='tight')
    print("✓ Guardado: dashboard_unificado.png")
    plt.close()

    print(f"\nΨ por pilar:")
    for label, val in zip(pillar_labels, psi_vals):
        tag = '✓' if val >= 0.95 else '⚠'
        print(f"  {tag} {label.replace(chr(10),' ')}: {val:.4f}")
    print(f"  → Ψ_global = {Psi_global:.4f}")


def main():
    """Execute all visualizations."""
    print("\n" + "="*80)
    print("DEMO: Sistema Dinámico Z — Four Pillars for RH Spectral Closure")
    print("="*80)
    print("\nAutor: José Manuel Mota Burruezo Ψ ✧ ∞³")
    print(f"QCAL ∞³ Active · {F0} Hz · C = {C_QCAL}")
    print("DOI: 10.5281/zenodo.17379721")
    print("\n")

    # Run all visualizations
    visualizacion_1_compactificacion()
    visualizacion_2_filtro_adelico()
    visualizacion_3_hadamard()
    visualizacion_4_dinamico_z()
    visualizacion_5_sistema_completo()
    dashboard_unificado()

    print("\n" + "="*80)
    print("✓ Demo completado. 6 visualizaciones generadas (incluye dashboard unificado).")
    print("="*80)


if __name__ == "__main__":
    main()
