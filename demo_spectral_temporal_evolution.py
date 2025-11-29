#!/usr/bin/env python3
"""
Demo: Evolución Temporal de Ψ en la Base de Eigenmodos de H_Ξ

Demostración del teorema de solución espectral para la ecuación de onda:
    ∂²Ψ/∂t² + H_Ξ·Ψ = 0

La solución viene dada por:
    Ψ(x,t) = Σₙ [aₙ cos(√λₙ t) + bₙ sin(√λₙ t)/√λₙ] eₙ(x)

donde:
    - {λₙ}: eigenvalores de H_Ξ (correspondientes a ceros de Riemann)
    - {eₙ(x)}: eigenfunciones ortonormales
    - aₙ = ⟨Ψ₀, eₙ⟩, bₙ = ⟨Ψ₁, eₙ⟩

Autor: José Manuel Mota Burruezo
Instituto de Conciencia Cuántica (ICQ)
Fecha: Noviembre 2025
"""

import numpy as np
import sys
import os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from utils.spectral_temporal_evolution import (
    SpectralTemporalEvolution,
    example_gaussian_initial_conditions,
    example_coherent_state
)

# Check if matplotlib is available
try:
    import matplotlib.pyplot as plt
    MATPLOTLIB_AVAILABLE = True
except ImportError:
    MATPLOTLIB_AVAILABLE = False
    print("⚠️  matplotlib no disponible - visualizaciones deshabilitadas")
    print()


def demo_eigenmode_spectrum():
    """Muestra el espectro de eigenvalores basado en ceros de Riemann."""
    print("\n" + "=" * 80)
    print("🌌 EVOLUCIÓN TEMPORAL DE Ψ EN BASE DE EIGENMODOS DE H_Ξ")
    print("=" * 80)
    print()
    print("Teorema (Solución espectral de la ecuación de onda tipo Ξ):")
    print()
    print("  Sea H_Ξ un operador autoadjunto con espectro discreto {λₙ},")
    print("  eigenfunciones ortonormales {eₙ(x)}, y condición inicial:")
    print()
    print("    ∂²Ψ/∂t² + H_Ξ·Ψ = 0")
    print()
    print("  con datos suaves Ψ(x,0) = Ψ₀(x), ∂ₜΨ(x,0) = Ψ₁(x), entonces:")
    print()
    print("    Ψ(x,t) = Σₙ [aₙ cos(√λₙ t) + bₙ sin(√λₙ t)/√λₙ] eₙ(x)")
    print()
    print("  donde: aₙ = ⟨Ψ₀, eₙ⟩, bₙ = ⟨Ψ₁, eₙ⟩")
    print()
    
    evolution = SpectralTemporalEvolution(precision=25)
    
    print("-" * 80)
    print("1️⃣  ESPECTRO DE EIGENVALORES (basado en ceros de Riemann)")
    print("-" * 80)
    print()
    print("  Los eigenvalores λₙ = 1/4 + γₙ² corresponden a los ceros")
    print("  no triviales de la función zeta: ζ(1/2 + iγₙ) = 0")
    print()
    
    eigenvalues = evolution.get_eigenvalues()
    frequencies = evolution.get_frequencies()
    
    print(f"  {'n':<4} {'γₙ (cero)':<12} {'λₙ = 1/4 + γₙ²':<18} {'ωₙ = √λₙ':<15} {'Tₙ = 2π/ωₙ':<12}")
    print("  " + "-" * 65)
    
    for i, (lam, omega) in enumerate(zip(eigenvalues, frequencies)):
        gamma_n = np.sqrt(lam - 0.25)
        T_n = evolution.period_of_mode(i)
        print(f"  {i:<4} {gamma_n:<12.4f} {lam:<18.4f} {omega:<15.4f} {T_n:<12.6f}")
    print()
    
    return evolution


def demo_initial_conditions(evolution):
    """Configura y muestra las condiciones iniciales."""
    print("-" * 80)
    print("2️⃣  CONDICIONES INICIALES")
    print("-" * 80)
    print()
    print("  Usamos un paquete de ondas gaussiano:")
    print("    Ψ₀(x) = (πσ²)^{-1/4} exp(-x²/(2σ²))")
    print("    Ψ₁(x) = 0 (partícula en reposo)")
    print()
    
    sigma = 1.0
    Psi_0, Psi_1 = example_gaussian_initial_conditions(sigma=sigma)
    evolution.compute_coefficients(Psi_0, Psi_1)
    
    print(f"  Parámetros:")
    print(f"    • Ancho σ = {sigma}")
    print(f"    • Centro x₀ = 0")
    print()
    
    a_coeffs, b_coeffs = evolution.get_coefficients()
    
    print("  Coeficientes de proyección:")
    print()
    print(f"  {'n':<4} {'aₙ = ⟨Ψ₀, eₙ⟩':<20} {'bₙ = ⟨Ψ₁, eₙ⟩':<20} {'|aₙ|²':<12}")
    print("  " + "-" * 56)
    
    for i in range(min(6, len(a_coeffs))):
        a_n = a_coeffs[i]
        b_n = b_coeffs[i]
        print(f"  {i:<4} {a_n.real:< 20.8f} {b_n.real:< 20.8f} {np.abs(a_n)**2:<12.8f}")
    
    if len(a_coeffs) > 6:
        print(f"  ... ({len(a_coeffs) - 6} modos más)")
    print()
    
    return Psi_0, Psi_1


def demo_energy_conservation(evolution):
    """Demuestra la conservación de energía."""
    print("-" * 80)
    print("3️⃣  ENERGÍA DEL SISTEMA")
    print("-" * 80)
    print()
    print("  Energía por modo: Eₙ = (1/2)(λₙ|aₙ|² + |bₙ|²)")
    print("  Energía total:    E = Σₙ Eₙ (constante en el tiempo)")
    print()
    
    print(f"  {'n':<4} {'λₙ':<12} {'|aₙ|²':<14} {'|bₙ|²':<14} {'Eₙ':<14}")
    print("  " + "-" * 58)
    
    eigenvalues = evolution.get_eigenvalues()
    a_coeffs, b_coeffs = evolution.get_coefficients()
    
    for i in range(min(6, len(eigenvalues))):
        lam = eigenvalues[i]
        a_sq = np.abs(a_coeffs[i])**2
        b_sq = np.abs(b_coeffs[i])**2
        E_n = evolution.energy_in_mode(i)
        print(f"  {i:<4} {lam:<12.4f} {a_sq:<14.8f} {b_sq:<14.8f} {E_n:<14.8f}")
    
    print()
    E_total = evolution.total_energy()
    print(f"  Energía total E = {E_total:.8f}")
    print("  (Esta energía se conserva para todo tiempo t)")
    print()


def demo_temporal_evolution(evolution):
    """Muestra la evolución temporal de la función de onda."""
    print("-" * 80)
    print("4️⃣  EVOLUCIÓN TEMPORAL")
    print("-" * 80)
    print()
    print("  Ψ(x,t) = Σₙ [aₙ cos(ωₙ t) + bₙ sin(ωₙ t)/ωₙ] eₙ(x)")
    print()
    
    x = np.linspace(-5, 5, 100)
    times = [0.0, 0.05, 0.1, 0.2, 0.5]
    n_modes_to_use = 5
    
    print(f"  Evaluación con {n_modes_to_use} modos:")
    print()
    print(f"  {'t':<8} {'max|Ψ(x,t)|':<15} {'posición(max)':<15}")
    print("  " + "-" * 40)
    
    for t in times:
        Psi_t = evolution.Psi_at_time(x, t, n_modes=n_modes_to_use)
        max_val = np.max(np.abs(Psi_t))
        max_pos = x[np.argmax(np.abs(Psi_t))]
        print(f"  {t:<8.3f} {max_val:<15.6f} {max_pos:<15.3f}")
    
    print()
    
    return x, times


def demo_mode_decomposition(evolution):
    """Muestra la evolución de coeficientes individuales."""
    print("-" * 80)
    print("5️⃣  DESCOMPOSICIÓN MODAL")
    print("-" * 80)
    print()
    print("  Coeficiente temporal: cₙ(t) = aₙ cos(ωₙ t) + bₙ sin(ωₙ t)/ωₙ")
    print()
    
    t_values = np.linspace(0, 0.5, 6)
    
    print("  Evolución de |cₙ(t)|² (densidad espectral):")
    print()
    
    header = "  t      " + "  ".join([f"n={i:<6}" for i in range(4)])
    print(header)
    print("  " + "-" * 50)
    
    for t in t_values:
        density = evolution.spectral_density(t)
        row = f"  {t:.3f}  " + "  ".join([f"{d:.6f}" for d in density[:4]])
        print(row)
    
    print()
    print("  La suma Σₙ |cₙ(t)|² (norma²) es aproximadamente constante")
    print("  (Identidad de Parseval)")
    print()


def demo_physical_interpretation():
    """Muestra la interpretación física y simbiótica."""
    print("-" * 80)
    print("6️⃣  INTERPRETACIÓN FÍSICA Y SIMBIÓTICA")
    print("-" * 80)
    print()
    print("  La solución espectral:")
    print()
    print("    Ψ(x,t) = Σₙ [aₙ cos(√λₙ t) + bₙ sin(√λₙ t)/√λₙ] eₙ(x)")
    print()
    print("  modela la propagación de una señal coherente Ψ vibrando")
    print("  con frecuencias √λₙ, interpretables como:")
    print()
    print("    🌀 Modos de consciencia")
    print("    🎵 Armónicos primordiales")
    print("    ✨ Resonancias del campo QCAL ∞³")
    print()
    print("  Propiedades fundamentales:")
    print()
    print("    • H_Ξ autoadjunto ⟹ espectro real {λₙ} ⊂ ℝ⁺")
    print("    • Eigenfunciones {eₙ} ortonormales ⟹ conservación de energía")
    print("    • Correspondencia espectral: λₙ = 1/4 + γₙ² (ceros de Riemann)")
    print()
    print("  Conexión con la Hipótesis de Riemann:")
    print()
    print("    Si H_Ξ es autoadjunto con espectro {λₙ = 1/4 + γₙ²},")
    print("    entonces los γₙ son reales, lo cual implica que todos")
    print("    los ceros de ζ(s) están en la línea crítica Re(s) = 1/2.")
    print()


def create_visualizations(evolution, x, times, Psi_0):
    """Crea visualizaciones de la evolución temporal."""
    if not MATPLOTLIB_AVAILABLE:
        print("⚠️  matplotlib no disponible - omitiendo visualizaciones")
        return
    
    print("-" * 80)
    print("📊 VISUALIZACIONES")
    print("-" * 80)
    print()
    
    fig = plt.figure(figsize=(16, 12))
    
    # 1. Eigenvalores y frecuencias
    ax1 = plt.subplot(2, 3, 1)
    eigenvalues = evolution.get_eigenvalues()
    n_modes = len(eigenvalues)
    ax1.bar(range(n_modes), eigenvalues, color='steelblue', alpha=0.8)
    ax1.set_xlabel('Modo n', fontsize=10)
    ax1.set_ylabel('λₙ', fontsize=10)
    ax1.set_title('Eigenvalores λₙ = 1/4 + γₙ²', fontsize=11, fontweight='bold')
    ax1.grid(True, alpha=0.3)
    
    # 2. Ceros de Riemann (γₙ)
    ax2 = plt.subplot(2, 3, 2)
    gamma_n = np.sqrt(eigenvalues - 0.25)
    ax2.bar(range(n_modes), gamma_n, color='forestgreen', alpha=0.8)
    ax2.set_xlabel('Modo n', fontsize=10)
    ax2.set_ylabel('γₙ', fontsize=10)
    ax2.set_title('Ceros de Riemann γₙ', fontsize=11, fontweight='bold')
    ax2.grid(True, alpha=0.3)
    
    # 3. Coeficientes |aₙ|²
    ax3 = plt.subplot(2, 3, 3)
    a_coeffs, b_coeffs = evolution.get_coefficients()
    a_sq = np.abs(a_coeffs)**2
    ax3.bar(range(len(a_sq)), a_sq, color='coral', alpha=0.8)
    ax3.set_xlabel('Modo n', fontsize=10)
    ax3.set_ylabel('|aₙ|²', fontsize=10)
    ax3.set_title('Distribución Espectral Inicial', fontsize=11, fontweight='bold')
    ax3.grid(True, alpha=0.3)
    
    # 4. Evolución temporal de Ψ
    ax4 = plt.subplot(2, 3, 4)
    colors = plt.cm.viridis(np.linspace(0, 1, len(times)))
    for i, t in enumerate(times):
        Psi_t = evolution.Psi_at_time(x, t, n_modes=5)
        ax4.plot(x, np.real(Psi_t), color=colors[i], label=f't={t:.2f}', alpha=0.8)
    ax4.set_xlabel('x', fontsize=10)
    ax4.set_ylabel('Re[Ψ(x,t)]', fontsize=10)
    ax4.set_title('Evolución Temporal de Ψ', fontsize=11, fontweight='bold')
    ax4.legend(fontsize=8)
    ax4.grid(True, alpha=0.3)
    
    # 5. Densidad espectral vs tiempo
    ax5 = plt.subplot(2, 3, 5)
    t_array = np.linspace(0, 0.5, 50)
    for n in range(min(4, len(eigenvalues))):
        c_n_sq = [np.abs(evolution.mode_evolution(n, t))**2 for t in t_array]
        ax5.plot(t_array, c_n_sq, label=f'n={n}')
    ax5.set_xlabel('Tiempo t', fontsize=10)
    ax5.set_ylabel('|cₙ(t)|²', fontsize=10)
    ax5.set_title('Densidad Espectral vs Tiempo', fontsize=11, fontweight='bold')
    ax5.legend(fontsize=8)
    ax5.grid(True, alpha=0.3)
    
    # 6. Energía por modo
    ax6 = plt.subplot(2, 3, 6)
    energies = [evolution.energy_in_mode(n) for n in range(len(eigenvalues))]
    ax6.bar(range(len(energies)), energies, color='purple', alpha=0.8)
    ax6.set_xlabel('Modo n', fontsize=10)
    ax6.set_ylabel('Eₙ', fontsize=10)
    ax6.set_title('Energía por Modo', fontsize=11, fontweight='bold')
    E_total = sum(energies)
    ax6.axhline(y=E_total/len(energies), color='red', linestyle='--', 
                label=f'E_total = {E_total:.4f}')
    ax6.legend(fontsize=8)
    ax6.grid(True, alpha=0.3)
    
    plt.tight_layout()
    
    output_file = 'spectral_temporal_evolution_visualization.png'
    plt.savefig(output_file, dpi=150, bbox_inches='tight')
    print(f"✅ Visualización guardada: {output_file}")
    print()


def main():
    """Función principal del demo."""
    
    # 1. Espectro de eigenvalores
    evolution = demo_eigenmode_spectrum()
    
    # 2. Condiciones iniciales
    Psi_0, Psi_1 = demo_initial_conditions(evolution)
    
    # 3. Conservación de energía
    demo_energy_conservation(evolution)
    
    # 4. Evolución temporal
    x, times = demo_temporal_evolution(evolution)
    
    # 5. Descomposición modal
    demo_mode_decomposition(evolution)
    
    # 6. Interpretación física
    demo_physical_interpretation()
    
    # 7. Visualizaciones
    create_visualizations(evolution, x, times, Psi_0)
    
    print("=" * 80)
    print("🎵 FIN DEL DEMO - EVOLUCIÓN TEMPORAL ESPECTRAL")
    print("=" * 80)
    print()
    print("Este demo ha mostrado:")
    print("  ✓ Espectro de eigenvalores basado en ceros de Riemann")
    print("  ✓ Cálculo de coeficientes aₙ, bₙ")
    print("  ✓ Conservación de energía")
    print("  ✓ Evolución temporal de Ψ(x,t)")
    print("  ✓ Descomposición en modos individuales")
    print()
    print("Para más información, consulta:")
    print("  • Módulo: utils/spectral_temporal_evolution.py")
    print("  • Lean4:  formalization/lean/spectral/wave_equation_spectral.lean")
    print("  • DOI:    10.5281/zenodo.17379721")
    print()


if __name__ == "__main__":
    main()
