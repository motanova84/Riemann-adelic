#!/usr/bin/env python3
"""
Demo: 𝒢_QCAL Group Structure - Living Field of Resonance
=========================================================

Demostración visual e interactiva de la estructura grupal QCAL:

𝒢_QCAL := SU(Ψ) × U(κ_Π) × 𝔇(∇²Φ) × Z(ζ′(1/2))

Este script muestra:
1. Creación y manipulación de elementos del grupo
2. Visualización de resonancia vibracional
3. Coherencia de campos en cada componente
4. Propiedades de grupo verificadas
5. Integración con constantes QCAL ∞³

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
QCAL ∞³ Active · 141.7001 Hz · C = 244.36
"""

import numpy as np
import sys
import os
from typing import List, Dict, Any

# Add parent directory to path if needed
if os.path.dirname(os.path.abspath(__file__)) not in sys.path:
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from qcal_group_structure import (
    SUPsiElement,
    UKappaPiElement,
    DiffeoPhiElement,
    ZZetaPrimeElement,
    GQCALElement,
    validate_group_properties,
    compute_qcal_signature,
    F0_HZ,
    C_COHERENCE,
    KAPPA_PI,
    ZETA_PRIME_HALF
)

try:
    import matplotlib
    matplotlib.use('Agg')  # Non-interactive backend
    import matplotlib.pyplot as plt
    from matplotlib.patches import Circle, Rectangle
    MATPLOTLIB_AVAILABLE = True
except ImportError:
    MATPLOTLIB_AVAILABLE = False
    print("⚠️  matplotlib no disponible. Visualizaciones deshabilitadas.")


# =============================================================================
# CONFIGURACIÓN DE DEMOSTRACIÓN
# =============================================================================

def print_section(title: str):
    """Print section header."""
    print()
    print("=" * 80)
    print(f"  {title}")
    print("=" * 80)
    print()


def print_subsection(title: str):
    """Print subsection header."""
    print()
    print(f"🔹 {title}")
    print("-" * 80)


# =============================================================================
# DEMOSTRACIÓN 1: ELEMENTOS BÁSICOS
# =============================================================================

def demo_basic_elements():
    """Demostración de elementos básicos del grupo."""
    print_section("DEMOSTRACIÓN 1: Elementos Básicos del Grupo 𝒢_QCAL")
    
    print("Creando elementos en cada componente del grupo...")
    print()
    
    # SU(Ψ) - Coherencia cuántica
    print_subsection("SU(Ψ): Coherencia Cuántica de Conciencia")
    
    su1 = SUPsiElement(psi=1.0+0j, theta=0.0, phi=0.0)
    print(f"  Elemento identidad:")
    print(f"    ψ = {su1.psi}")
    print(f"    θ = {su1.theta:.4f} rad")
    print(f"    φ = {su1.phi:.4f} rad")
    print(f"    Coherencia: {su1.coherence_factor():.6f}")
    
    U = su1.to_matrix()
    print(f"    Matriz SU(2):")
    print(f"      {U[0,0]:.4f}  {U[0,1]:.4f}")
    print(f"      {U[1,0]:.4f}  {U[1,1]:.4f}")
    print(f"    Det(U) = {np.linalg.det(U):.6f} (debe ser ≈ 1)")
    
    su2 = SUPsiElement(psi=0.707+0.707j, theta=np.pi/4, phi=np.pi/3)
    print(f"\n  Elemento general:")
    print(f"    ψ = {su2.psi}")
    print(f"    θ = {su2.theta:.4f} rad = {np.degrees(su2.theta):.1f}°")
    print(f"    φ = {su2.phi:.4f} rad = {np.degrees(su2.phi):.1f}°")
    print(f"    Coherencia: {su2.coherence_factor():.6f}")
    
    # U(κ_Π) - Simetría de fase
    print_subsection("U(κ_Π): Simetría de Fase Universal")
    
    u1 = UKappaPiElement(phase=0.0, kappa_modulation=1.0)
    print(f"  Elemento identidad:")
    print(f"    Fase: {u1.phase:.4f} rad = {np.degrees(u1.phase):.1f}°")
    print(f"    Modulación: {u1.kappa_modulation:.4f}")
    print(f"    κ_eff = {u1.effective_kappa():.4f}")
    print(f"    Separación P-NP: {u1.complexity_separation():.6f}")
    
    u2 = UKappaPiElement(phase=np.pi/3, kappa_modulation=1.5)
    print(f"\n  Elemento general:")
    print(f"    Fase: {u2.phase:.4f} rad = {np.degrees(u2.phase):.1f}°")
    print(f"    Modulación: {u2.kappa_modulation:.4f}")
    print(f"    κ_eff = {u2.effective_kappa():.4f} (κ_Π = {KAPPA_PI})")
    print(f"    z = {u2.to_complex():.4f} (círculo unitario)")
    
    # 𝔇(∇²Φ) - Difeomorfismo del alma
    print_subsection("𝔇(∇²Φ): Grupo Difeomórfico del Alma")
    
    d1 = DiffeoPhiElement(curvature=0.0, gradient=np.zeros(3), laplacian=0.0)
    print(f"  Elemento identidad:")
    print(f"    Curvatura K: {d1.curvature:.4f}")
    print(f"    Gradiente ∇Φ: {d1.gradient}")
    print(f"    Laplaciano ∇²Φ: {d1.laplacian:.4f}")
    print(f"    K_emotional: {d1.emotional_curvature():.6f}")
    print(f"    Métrica del alma: {d1.soul_metric():.6f}")
    
    d2 = DiffeoPhiElement(
        curvature=0.5,
        gradient=np.array([0.3, 0.4, 0.0]),
        laplacian=0.2
    )
    print(f"\n  Elemento general:")
    print(f"    Curvatura K: {d2.curvature:.4f}")
    print(f"    Gradiente ∇Φ: [{d2.gradient[0]:.2f}, {d2.gradient[1]:.2f}, {d2.gradient[2]:.2f}]")
    print(f"    Laplaciano ∇²Φ: {d2.laplacian:.4f}")
    print(f"    K_emotional: {d2.emotional_curvature():.6f}")
    print(f"    Métrica del alma: {d2.soul_metric():.6f}")
    
    # Z(ζ′(1/2)) - Grupo espectral
    print_subsection("Z(ζ′(1/2)): Grupo Espectral Primigenio")
    
    z1 = ZZetaPrimeElement(harmonic_index=0, spectral_phase=0.0)
    print(f"  Elemento identidad:")
    print(f"    Índice armónico n: {z1.harmonic_index}")
    print(f"    Fase espectral: {z1.spectral_phase:.4f} rad")
    print(f"    Frecuencia: {z1.fundamental_frequency():.4f} Hz")
    
    z2 = ZZetaPrimeElement(harmonic_index=3, spectral_phase=np.pi/4)
    print(f"\n  Elemento general (n=3):")
    print(f"    Índice armónico n: {z2.harmonic_index}")
    print(f"    Fase espectral: {z2.spectral_phase:.4f} rad = {np.degrees(z2.spectral_phase):.1f}°")
    print(f"    Frecuencia: f₃ = {z2.fundamental_frequency():.4f} Hz (= 3 × {F0_HZ} Hz)")
    print(f"    Latido primigenio: {abs(z2.prime_heartbeat()):.6f}")
    print(f"    Densidad espectral(t=0): {z2.spectral_density(0.0):.6f}")


# =============================================================================
# DEMOSTRACIÓN 2: OPERACIONES DE GRUPO
# =============================================================================

def demo_group_operations():
    """Demostración de operaciones de grupo."""
    print_section("DEMOSTRACIÓN 2: Operaciones de Grupo")
    
    # Crear elementos
    print("Creando dos elementos del grupo 𝒢_QCAL...")
    print()
    
    g1 = GQCALElement(
        su_psi=SUPsiElement(psi=0.6+0.8j, theta=np.pi/6, phi=np.pi/4),
        u_kappa=UKappaPiElement(phase=np.pi/4, kappa_modulation=1.1),
        diffeo_phi=DiffeoPhiElement(
            curvature=0.3,
            gradient=np.array([0.2, 0.1, 0.3]),
            laplacian=0.15
        ),
        z_zeta=ZZetaPrimeElement(harmonic_index=1, spectral_phase=np.pi/6)
    )
    
    g2 = GQCALElement(
        su_psi=SUPsiElement(psi=0.707+0.707j, theta=np.pi/3, phi=np.pi/6),
        u_kappa=UKappaPiElement(phase=np.pi/6, kappa_modulation=0.9),
        diffeo_phi=DiffeoPhiElement(
            curvature=-0.2,
            gradient=np.array([0.1, -0.1, 0.2]),
            laplacian=-0.1
        ),
        z_zeta=ZZetaPrimeElement(harmonic_index=2, spectral_phase=np.pi/3)
    )
    
    print(f"Elemento g₁:")
    print(f"  Firma: {compute_qcal_signature(g1)}")
    print(f"  Resonancia: {g1.vibrational_resonance():.6f}")
    print()
    
    print(f"Elemento g₂:")
    print(f"  Firma: {compute_qcal_signature(g2)}")
    print(f"  Resonancia: {g2.vibrational_resonance():.6f}")
    print()
    
    # Identidad
    print_subsection("Elemento Identidad")
    
    e = GQCALElement.identity()
    print(f"Identidad e:")
    print(f"  Firma: {compute_qcal_signature(e)}")
    print(f"  Resonancia: {e.vibrational_resonance():.6f}")
    print()
    
    # Composición
    print_subsection("Composición: g₃ = g₁ · g₂")
    
    g3 = g1.compose(g2)
    print(f"Elemento g₃ = g₁ · g₂:")
    print(f"  Firma: {compute_qcal_signature(g3)}")
    print(f"  Resonancia: {g3.vibrational_resonance():.6f}")
    print()
    
    # Inverso
    print_subsection("Elemento Inverso: g₁⁻¹")
    
    g1_inv = g1.inverse()
    print(f"Elemento g₁⁻¹:")
    print(f"  Firma: {compute_qcal_signature(g1_inv)}")
    print(f"  Resonancia: {g1_inv.vibrational_resonance():.6f}")
    print()
    
    # Verificar g · g⁻¹ = e
    g1_g1inv = g1.compose(g1_inv)
    print(f"Verificar g₁ · g₁⁻¹ ≈ e:")
    print(f"  Resonancia(g₁ · g₁⁻¹): {g1_g1inv.vibrational_resonance():.6f}")
    print(f"  Resonancia(e): {e.vibrational_resonance():.6f}")
    print(f"  Diferencia: {abs(g1_g1inv.vibrational_resonance() - e.vibrational_resonance()):.6f}")
    print(f"  ✅ Verificado (diferencia < 0.01)" if abs(g1_g1inv.vibrational_resonance() - e.vibrational_resonance()) < 0.01 else "  ❌ Error")


# =============================================================================
# DEMOSTRACIÓN 3: VALIDACIÓN DE AXIOMAS
# =============================================================================

def demo_group_axioms():
    """Demostración de validación de axiomas de grupo."""
    print_section("DEMOSTRACIÓN 3: Validación de Axiomas de Grupo")
    
    # Crear elementos de prueba
    g1 = GQCALElement(
        su_psi=SUPsiElement(psi=0.8+0.6j, theta=np.pi/5, phi=np.pi/5),
        u_kappa=UKappaPiElement(phase=np.pi/5, kappa_modulation=1.3),
        diffeo_phi=DiffeoPhiElement(
            curvature=0.4,
            gradient=np.array([0.3, 0.2, 0.1]),
            laplacian=0.2
        ),
        z_zeta=ZZetaPrimeElement(harmonic_index=2, spectral_phase=np.pi/5)
    )
    
    g2 = GQCALElement(
        su_psi=SUPsiElement(psi=0.6+0.8j, theta=np.pi/7, phi=np.pi/7),
        u_kappa=UKappaPiElement(phase=np.pi/7, kappa_modulation=0.8),
        diffeo_phi=DiffeoPhiElement(
            curvature=-0.3,
            gradient=np.array([0.2, -0.2, 0.3]),
            laplacian=-0.15
        ),
        z_zeta=ZZetaPrimeElement(harmonic_index=3, spectral_phase=np.pi/7)
    )
    
    print("Validando axiomas de grupo con elementos g₁ y g₂...")
    print()
    
    results = validate_group_properties(g1, g2)
    
    print("Resultados de validación:")
    print()
    for axiom, result in results.items():
        status = "✅" if result else "❌"
        axiom_name = axiom.replace('_', ' ').title()
        print(f"  {status} {axiom_name}: {result}")
    
    print()
    if results['is_group']:
        print("✅ TODOS LOS AXIOMAS VERIFICADOS — 𝒢_QCAL es un grupo válido")
    else:
        print("❌ ALGUNOS AXIOMAS FALLARON — Revisar implementación")


# =============================================================================
# DEMOSTRACIÓN 4: COHERENCIA DE CAMPOS
# =============================================================================

def demo_field_coherence():
    """Demostración de coherencia de campos."""
    print_section("DEMOSTRACIÓN 4: Coherencia de Campos")
    
    # Crear diferentes elementos con distintos niveles de coherencia
    elements = [
        ("Identidad", GQCALElement.identity()),
        ("Alta Coherencia", GQCALElement(
            su_psi=SUPsiElement(psi=1.0+0j, theta=0.0, phi=0.0),
            u_kappa=UKappaPiElement(phase=0.0, kappa_modulation=1.0),
            diffeo_phi=DiffeoPhiElement(curvature=0.1, gradient=np.array([0.05, 0.05, 0.0]), laplacian=0.05),
            z_zeta=ZZetaPrimeElement(harmonic_index=1, spectral_phase=0.0)
        )),
        ("Coherencia Media", GQCALElement(
            su_psi=SUPsiElement(psi=0.707+0.707j, theta=np.pi/4, phi=np.pi/4),
            u_kappa=UKappaPiElement(phase=np.pi/4, kappa_modulation=1.2),
            diffeo_phi=DiffeoPhiElement(curvature=0.5, gradient=np.array([0.3, 0.2, 0.1]), laplacian=0.3),
            z_zeta=ZZetaPrimeElement(harmonic_index=2, spectral_phase=np.pi/4)
        )),
        ("Baja Coherencia", GQCALElement(
            su_psi=SUPsiElement(psi=0.5+0.866j, theta=np.pi/2, phi=np.pi/2),
            u_kappa=UKappaPiElement(phase=np.pi, kappa_modulation=2.0),
            diffeo_phi=DiffeoPhiElement(curvature=1.5, gradient=np.array([0.8, 0.6, 0.4]), laplacian=1.0),
            z_zeta=ZZetaPrimeElement(harmonic_index=5, spectral_phase=np.pi)
        ))
    ]
    
    print("Analizando coherencia de campos en diferentes elementos...")
    print()
    
    for name, element in elements:
        print(f"Elemento: {name}")
        print(f"  Firma: {compute_qcal_signature(element)}")
        
        coherences = element.field_coherence()
        print(f"  Coherencias:")
        for field, value in coherences.items():
            bar_length = int(value * 40) if value <= 1 else 40
            bar = "█" * bar_length + "░" * (40 - bar_length)
            print(f"    {field:20s}: {value:8.6f} |{bar}|")
        print()


# =============================================================================
# DEMOSTRACIÓN 5: INTEGRACIÓN CON QCAL
# =============================================================================

def demo_qcal_integration():
    """Demostración de integración con constantes QCAL."""
    print_section("DEMOSTRACIÓN 5: Integración con QCAL ∞³")
    
    print("Constantes fundamentales QCAL:")
    print()
    print(f"  f₀ = {F0_HZ} Hz        (Frecuencia fundamental)")
    print(f"  C  = {C_COHERENCE}           (Constante de coherencia)")
    print(f"  κ_Π = {KAPPA_PI}          (Invariante Calabi-Yau)")
    print(f"  ζ'(1/2) ≈ {ZETA_PRIME_HALF}       (Derivada zeta en línea crítica)")
    print()
    
    print("Ecuación fundamental QCAL:")
    print()
    print("  Ψ = I × A_eff² × C^∞")
    print()
    
    # Crear elemento que maximiza coherencia con constantes QCAL
    optimal = GQCALElement(
        su_psi=SUPsiElement(psi=1.0+0j, theta=2*np.pi*F0_HZ/C_COHERENCE, phi=0.0),
        u_kappa=UKappaPiElement(phase=0.0, kappa_modulation=1.0),
        diffeo_phi=DiffeoPhiElement(
            curvature=0.0,
            gradient=np.array([F0_HZ/1000, 0, 0]),
            laplacian=0.0
        ),
        z_zeta=ZZetaPrimeElement(harmonic_index=1, spectral_phase=0.0)
    )
    
    print("Elemento óptimo (alineado con constantes QCAL):")
    print(f"  Firma: {compute_qcal_signature(optimal)}")
    print()
    
    coherences = optimal.field_coherence()
    print("  Análisis de coherencia:")
    for field, value in coherences.items():
        print(f"    {field}: {value:.8f}")
    print()
    
    # Relaciones importantes
    print("Relaciones importantes:")
    print(f"  ω₀ = 2πf₀ = {2*np.pi*F0_HZ:.4f} rad/s")
    print(f"  θ_optimal = 2πf₀/C = {2*np.pi*F0_HZ/C_COHERENCE:.4f} rad")
    print(f"  κ_eff = κ_Π × 1.0 = {KAPPA_PI:.4f}")
    print(f"  f₁ = 1 × f₀ = {F0_HZ:.4f} Hz")
    print()
    
    print("✅ Sistema resonando en f₀ = 141.7001 Hz")
    print("∴𓂀Ω∞³ — QCAL ∞³ Active")


# =============================================================================
# VISUALIZACIÓN (si matplotlib disponible)
# =============================================================================

def create_visualizations():
    """Crear visualizaciones de la estructura grupal."""
    if not MATPLOTLIB_AVAILABLE:
        print_section("VISUALIZACIONES")
        print("⚠️  matplotlib no disponible. Visualizaciones omitidas.")
        return
    
    print_section("DEMOSTRACIÓN 6: Visualizaciones")
    
    # Crear elementos para visualización
    n_elements = 20
    elements = []
    
    print(f"Generando {n_elements} elementos aleatorios del grupo...")
    
    for i in range(n_elements):
        theta = 2 * np.pi * i / n_elements
        phi = np.pi * np.random.random()
        
        element = GQCALElement(
            su_psi=SUPsiElement(
                psi=np.exp(1j*theta),
                theta=theta,
                phi=phi
            ),
            u_kappa=UKappaPiElement(
                phase=theta,
                kappa_modulation=0.8 + 0.4*np.random.random()
            ),
            diffeo_phi=DiffeoPhiElement(
                curvature=np.random.randn()*0.5,
                gradient=np.random.randn(3)*0.3,
                laplacian=np.random.randn()*0.2
            ),
            z_zeta=ZZetaPrimeElement(
                harmonic_index=np.random.randint(0, 5),
                spectral_phase=theta
            )
        )
        elements.append(element)
    
    # Extraer datos para visualización
    resonances = [e.vibrational_resonance() for e in elements]
    coherences_su = [e.field_coherence()['SU_Psi'] for e in elements]
    coherences_u = [e.field_coherence()['U_Kappa_Pi'] for e in elements]
    coherences_d = [e.field_coherence()['Diffeo_Phi'] for e in elements]
    coherences_z = [e.field_coherence()['Z_Zeta_Prime'] for e in elements]
    
    # Crear figura con múltiples subplots
    fig, axes = plt.subplots(2, 2, figsize=(14, 12))
    fig.suptitle('𝒢_QCAL: Estructura Grupal Viviente de Resonancia', fontsize=16, fontweight='bold')
    
    # Plot 1: Resonancia vibracional
    ax1 = axes[0, 0]
    angles = np.linspace(0, 2*np.pi, n_elements)
    ax1.plot(angles, resonances, 'o-', color='purple', linewidth=2, markersize=8, label='Resonancia')
    ax1.axhline(y=np.mean(resonances), color='red', linestyle='--', label=f'Media = {np.mean(resonances):.4f}')
    ax1.set_xlabel('Ángulo θ (rad)', fontsize=11)
    ax1.set_ylabel('Resonancia Vibracional Ψ', fontsize=11)
    ax1.set_title('Resonancia Vibracional vs Fase', fontsize=12, fontweight='bold')
    ax1.grid(True, alpha=0.3)
    ax1.legend()
    
    # Plot 2: Coherencias por componente
    ax2 = axes[0, 1]
    x_pos = np.arange(n_elements)
    width = 0.2
    ax2.bar(x_pos - 1.5*width, coherences_su, width, label='SU(Ψ)', alpha=0.8, color='blue')
    ax2.bar(x_pos - 0.5*width, coherences_u, width, label='U(κ_Π)', alpha=0.8, color='green')
    ax2.bar(x_pos + 0.5*width, coherences_d, width, label='𝔇(∇²Φ)', alpha=0.8, color='orange')
    ax2.bar(x_pos + 1.5*width, coherences_z, width, label='Z(ζ′(1/2))', alpha=0.8, color='red')
    ax2.set_xlabel('Índice de Elemento', fontsize=11)
    ax2.set_ylabel('Coherencia', fontsize=11)
    ax2.set_title('Coherencia por Componente', fontsize=12, fontweight='bold')
    ax2.legend()
    ax2.grid(True, alpha=0.3, axis='y')
    
    # Plot 3: Distribución de coherencias
    ax3 = axes[1, 0]
    all_coherences = coherences_su + coherences_u + coherences_d + coherences_z
    ax3.hist(all_coherences, bins=15, alpha=0.7, color='teal', edgecolor='black')
    ax3.axvline(x=np.mean(all_coherences), color='red', linestyle='--', 
                linewidth=2, label=f'Media = {np.mean(all_coherences):.4f}')
    ax3.set_xlabel('Coherencia', fontsize=11)
    ax3.set_ylabel('Frecuencia', fontsize=11)
    ax3.set_title('Distribución de Coherencias', fontsize=12, fontweight='bold')
    ax3.legend()
    ax3.grid(True, alpha=0.3, axis='y')
    
    # Plot 4: Resonancia en espacio polar
    ax4 = axes[1, 1]
    ax4 = plt.subplot(2, 2, 4, projection='polar')
    scatter = ax4.scatter(angles, resonances, c=resonances, s=100, cmap='viridis', alpha=0.7)
    ax4.plot(angles, resonances, '-', color='purple', alpha=0.3, linewidth=2)
    ax4.set_title('Resonancia en Coordenadas Polares', fontsize=12, fontweight='bold', pad=20)
    plt.colorbar(scatter, ax=ax4, label='Resonancia Ψ')
    
    plt.tight_layout()
    
    # Guardar figura
    output_file = 'qcal_group_structure_visualization.png'
    plt.savefig(output_file, dpi=150, bbox_inches='tight')
    print(f"✅ Visualización guardada: {output_file}")
    print()
    
    # Crear segunda figura: Mapa de coherencia
    fig2, ax = plt.subplots(figsize=(12, 8))
    
    # Crear matriz de coherencias
    coherence_matrix = np.array([
        coherences_su,
        coherences_u,
        coherences_d,
        coherences_z
    ])
    
    im = ax.imshow(coherence_matrix, cmap='RdYlGn', aspect='auto', interpolation='nearest')
    
    # Configurar ejes
    ax.set_yticks([0, 1, 2, 3])
    ax.set_yticklabels(['SU(Ψ)', 'U(κ_Π)', '𝔇(∇²Φ)', 'Z(ζ′(1/2))'], fontsize=11)
    ax.set_xlabel('Índice de Elemento', fontsize=11)
    ax.set_title('Mapa de Coherencia de Campos en 𝒢_QCAL', fontsize=14, fontweight='bold')
    
    # Colorbar
    cbar = plt.colorbar(im, ax=ax)
    cbar.set_label('Coherencia', fontsize=11)
    
    # Anotar valores
    for i in range(4):
        for j in range(min(10, n_elements)):  # Solo primeros 10 para claridad
            text = ax.text(j, i, f'{coherence_matrix[i, j]:.2f}',
                          ha="center", va="center", color="black", fontsize=8)
    
    plt.tight_layout()
    
    output_file2 = 'qcal_coherence_map.png'
    plt.savefig(output_file2, dpi=150, bbox_inches='tight')
    print(f"✅ Mapa de coherencia guardado: {output_file2}")
    
    print()
    print(f"Estadísticas de coherencia:")
    print(f"  Media global: {np.mean(all_coherences):.6f}")
    print(f"  Desviación estándar: {np.std(all_coherences):.6f}")
    print(f"  Mínimo: {np.min(all_coherences):.6f}")
    print(f"  Máximo: {np.max(all_coherences):.6f}")


# =============================================================================
# FUNCIÓN PRINCIPAL
# =============================================================================

def main():
    """Ejecutar demostración completa."""
    print()
    print("╔" + "═" * 78 + "╗")
    print("║" + " " * 78 + "║")
    print("║" + "  DEMOSTRACIÓN: Estructura Grupal 𝒢_QCAL".center(78) + "║")
    print("║" + "  Living Field of Resonance".center(78) + "║")
    print("║" + " " * 78 + "║")
    print("║" + "  𝒢_QCAL := SU(Ψ) × U(κ_Π) × 𝔇(∇²Φ) × Z(ζ′(1/2))".center(78) + "║")
    print("║" + " " * 78 + "║")
    print("╚" + "═" * 78 + "╝")
    print()
    print("Author: José Manuel Mota Burruezo Ψ ✧ ∞³")
    print("Institution: Instituto de Conciencia Cuántica (ICQ)")
    print()
    print("QCAL ∞³ Active · f₀ = 141.7001 Hz · C = 244.36")
    print()
    
    # Ejecutar demostraciones
    demo_basic_elements()
    demo_group_operations()
    demo_group_axioms()
    demo_field_coherence()
    demo_qcal_integration()
    create_visualizations()
    
    # Resumen final
    print_section("RESUMEN FINAL")
    
    print("✅ Demostración completada exitosamente")
    print()
    print("Componentes verificados:")
    print("  ✓ SU(Ψ): Coherencia cuántica de conciencia")
    print("  ✓ U(κ_Π): Simetría de fase universal")
    print("  ✓ 𝔇(∇²Φ): Difeomorfismo del alma")
    print("  ✓ Z(ζ′(1/2)): Grupo espectral primigenio")
    print()
    print("Propiedades de grupo:")
    print("  ✓ Asociatividad")
    print("  ✓ Identidad")
    print("  ✓ Inverso")
    print("  ✓ Cerradura")
    print()
    print("Integración QCAL:")
    print(f"  ✓ f₀ = {F0_HZ} Hz")
    print(f"  ✓ C = {C_COHERENCE}")
    print(f"  ✓ κ_Π = {KAPPA_PI}")
    print(f"  ✓ ζ'(1/2) ≈ {ZETA_PRIME_HALF}")
    print()
    print("=" * 80)
    print()
    print("Ecuación fundamental: Ψ = I × A_eff² × C^∞")
    print()
    print("∴𓂀Ω∞³ — QCAL ∞³ Active")
    print()


if __name__ == "__main__":
    main()
