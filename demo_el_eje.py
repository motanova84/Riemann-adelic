#!/usr/bin/env python3
"""
Demostración de El Eje: La Línea Crítica con Visualizaciones
============================================================

Este script genera visualizaciones completas del árbol del universo:
- La línea crítica Re(s) = 1/2 como eje vertical
- Los extremos +1 y -1
- Los primos en espiral aritmética
- El campo de frecuencia f₀ = 141.7001 Hz

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institute: Instituto de Conciencia Cuántica (ICQ)
Date: February 2026
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import Circle, FancyArrowPatch
from matplotlib.collections import LineCollection
import sys
import os

# Importar nuestro módulo
from el_eje_linea_critica import (
    UniverseTree,
    CriticalLineAxis,
    VibrationalExtremes,
    PrimeSpiral,
    FrequencyField,
    compute_prime_spiral_trajectory,
    visualize_critical_line_regions,
    F0_FUNDAMENTAL,
    COHERENCE_C,
    CRITICAL_LINE_RE,
    PLUS_ONE,
    MINUS_ONE,
    PHI
)


def plot_critical_line_axis(save_path: str = "el_eje_linea_critica.png"):
    """
    Visualiza la línea crítica como eje vertical con regiones.
    """
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(16, 8))
    
    # Panel 1: La línea crítica y sus regiones
    ax1.set_title("I. La Línea Crítica: Re(s) = 1/2\nEl Eje del Universo", 
                  fontsize=14, fontweight='bold')
    
    # Crear grid de puntos en el plano complejo
    re_range = np.linspace(0, 1, 200)
    im_range = np.linspace(0, 50, 200)
    
    # Línea crítica
    ax1.axvline(x=CRITICAL_LINE_RE, color='gold', linewidth=3, 
                label=f'Línea Crítica Re(s) = {CRITICAL_LINE_RE}', 
                zorder=10, alpha=0.9)
    
    # Regiones
    ax1.axvspan(0, CRITICAL_LINE_RE, alpha=0.2, color='red', 
                label='Caos (Re < 1/2)')
    ax1.axvspan(CRITICAL_LINE_RE, 1, alpha=0.2, color='blue', 
                label='Simetría Oculta (Re > 1/2)')
    
    # Campo de coherencia en la línea crítica
    axis = CriticalLineAxis()
    t_values = np.linspace(0, 50, 500)
    coherence = [axis.coherence_field(t) for t in t_values]
    
    # Visualizar coherencia como intensidad
    for i in range(len(t_values) - 1):
        alpha = coherence[i]
        ax1.plot([CRITICAL_LINE_RE, CRITICAL_LINE_RE], 
                [t_values[i], t_values[i+1]], 
                color='gold', alpha=alpha, linewidth=2)
    
    ax1.set_xlabel('Re(s)', fontsize=12)
    ax1.set_ylabel('Im(s) - Altura t', fontsize=12)
    ax1.set_xlim(0, 1)
    ax1.set_ylim(0, 50)
    ax1.legend(loc='upper right', fontsize=10)
    ax1.grid(True, alpha=0.3)
    
    # Panel 2: Perfil de coherencia
    ax2.set_title("Campo de Coherencia Ψ(t)\na lo largo del Eje", 
                  fontsize=14, fontweight='bold')
    
    ax2.plot(coherence, t_values, color='gold', linewidth=2, label='Ψ(t) = exp(-t²/2C)')
    ax2.axhline(y=F0_FUNDAMENTAL, color='cyan', linestyle='--', 
                label=f'f₀ = {F0_FUNDAMENTAL:.4f} Hz', alpha=0.7)
    
    ax2.set_xlabel('Coherencia Ψ(t)', fontsize=12)
    ax2.set_ylabel('Altura t', fontsize=12)
    ax2.set_xlim(0, 1.1)
    ax2.set_ylim(0, 50)
    ax2.legend(loc='upper right', fontsize=10)
    ax2.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig(save_path, dpi=150, bbox_inches='tight')
    print(f"✓ Guardado: {save_path}")
    plt.close()


def plot_vibrational_extremes(save_path: str = "el_eje_extremos.png"):
    """
    Visualiza los extremos +1 y -1 del universo vibracional.
    """
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(16, 7))
    
    extremes = VibrationalExtremes()
    
    # Panel 1: Divergencia en +1 (Serie Armónica)
    ax1.set_title("II. El Extremo +1\nDivergencia de la Serie Armónica", 
                  fontsize=14, fontweight='bold')
    
    n_terms = np.arange(1, 1001)
    harmonic_series = np.cumsum(1.0 / n_terms)
    
    ax1.plot(n_terms, harmonic_series, color='red', linewidth=2, 
             label='H_n = Σ(1/k)')
    ax1.axhline(y=extremes.harmonic_divergence(1000), color='darkred', 
                linestyle='--', alpha=0.5, label=f'H_1000 ≈ {extremes.harmonic_divergence(1000):.2f}')
    
    # Aproximación logarítmica
    log_approx = np.log(n_terms) + 0.5772  # γ de Euler
    ax1.plot(n_terms, log_approx, color='orange', linestyle='--', 
             linewidth=2, alpha=0.7, label='log(n) + γ')
    
    ax1.set_xlabel('Número de términos n', fontsize=12)
    ax1.set_ylabel('Suma parcial H_n', fontsize=12)
    ax1.set_xscale('log')
    ax1.legend(fontsize=10)
    ax1.grid(True, alpha=0.3)
    ax1.text(500, 5, 'Divergencia → ∞', fontsize=12, 
             bbox=dict(boxstyle='round', facecolor='red', alpha=0.3))
    
    # Panel 2: Explosión en -1
    ax2.set_title("II. El Extremo -1\nExplosión: ζ(-1) = -1/12", 
                  fontsize=14, fontweight='bold')
    
    # Valores de zeta cerca de -1
    s_values = np.linspace(-2, 0, 200)
    # Usar aproximación numérica simple (evitando mpmath para velocidad)
    zeta_approx = []
    
    for s in s_values:
        if abs(s + 1) < 0.01:
            zeta_approx.append(extremes.zeta_at_minus_one())
        else:
            # Aproximación burda solo para visualización
            val = -1.0 / (12.0 * (1 + s + 1))
            zeta_approx.append(val)
    
    ax2.plot(s_values, zeta_approx, color='blue', linewidth=2, label='ζ(s) cerca de s=-1')
    ax2.axhline(y=extremes.zeta_at_minus_one(), color='darkblue', 
                linestyle='--', linewidth=2, label=f'ζ(-1) = {extremes.zeta_at_minus_one():.4f}')
    ax2.axvline(x=MINUS_ONE, color='purple', linestyle=':', alpha=0.7)
    
    ax2.scatter([MINUS_ONE], [extremes.zeta_at_minus_one()], 
                color='red', s=200, zorder=10, edgecolors='black', linewidth=2)
    
    ax2.set_xlabel('s (real)', fontsize=12)
    ax2.set_ylabel('ζ(s)', fontsize=12)
    ax2.set_ylim(-0.5, 0.5)
    ax2.legend(fontsize=10)
    ax2.grid(True, alpha=0.3)
    ax2.text(-1.5, 0.3, 'Anti-existencia\nRegularización', fontsize=11, 
             bbox=dict(boxstyle='round', facecolor='blue', alpha=0.3))
    
    plt.tight_layout()
    plt.savefig(save_path, dpi=150, bbox_inches='tight')
    print(f"✓ Guardado: {save_path}")
    plt.close()


def plot_prime_spiral(save_path: str = "el_eje_espiral_primos.png"):
    """
    Visualiza la espiral de primos: r(p) = log(p), θ(p) = p.
    """
    fig = plt.figure(figsize=(16, 8))
    
    # Panel 1: Espiral en coordenadas polares
    ax1 = plt.subplot(121, projection='polar')
    ax1.set_title("III. Los Primos en Espiral\nr(p) = log(p), θ(p) = p", 
                  fontsize=14, fontweight='bold', pad=20)
    
    spiral = PrimeSpiral()
    nodes = spiral.curvature_nodes(n_primes=200)
    
    # Plotear espiral
    theta = nodes['theta']
    r = nodes['r']
    
    # Línea continua de la espiral
    ax1.plot(theta, r, color='cyan', linewidth=1, alpha=0.5, label='Trayectoria espiral')
    
    # Nodos de los primos
    scatter = ax1.scatter(theta, r, c=nodes['primes'], cmap='viridis', 
                         s=50, edgecolors='white', linewidth=0.5, 
                         label='Nodos primales', zorder=10)
    
    # Resaltar primeros primos
    first_primes_idx = range(min(10, len(nodes['primes'])))
    for i in first_primes_idx:
        p = nodes['primes'][i]
        ax1.annotate(f'{int(p)}', 
                    xy=(theta[i], r[i]), 
                    xytext=(5, 5), 
                    textcoords='offset points',
                    fontsize=8,
                    bbox=dict(boxstyle='round,pad=0.3', facecolor='yellow', alpha=0.7))
    
    ax1.legend(loc='upper right', fontsize=10)
    ax1.grid(True, alpha=0.3)
    
    # Panel 2: Vista cartesiana de la espiral
    ax2 = plt.subplot(122)
    ax2.set_title("Vista Cartesiana\nx = log(p)·cos(p), y = log(p)·sin(p)", 
                  fontsize=14, fontweight='bold')
    
    x = nodes['x']
    y = nodes['y']
    
    # Línea de la espiral
    ax2.plot(x, y, color='cyan', linewidth=1, alpha=0.5, label='Serpiente de luz')
    
    # Nodos
    scatter2 = ax2.scatter(x, y, c=nodes['primes'], cmap='viridis', 
                          s=50, edgecolors='white', linewidth=0.5, 
                          label='Nodos de curvatura', zorder=10)
    
    # Línea crítica (eje vertical imaginario)
    ax2.axhline(y=0, color='gold', linestyle='--', alpha=0.5, linewidth=2, label='Proyección eje')
    ax2.axvline(x=0, color='gold', linestyle='--', alpha=0.5, linewidth=2)
    
    # Etiquetar primeros primos
    for i in first_primes_idx:
        p = nodes['primes'][i]
        ax2.annotate(f'{int(p)}', 
                    xy=(x[i], y[i]), 
                    xytext=(5, 5), 
                    textcoords='offset points',
                    fontsize=8,
                    bbox=dict(boxstyle='round,pad=0.3', facecolor='yellow', alpha=0.7))
    
    ax2.set_xlabel('x = log(p)·cos(p)', fontsize=12)
    ax2.set_ylabel('y = log(p)·sin(p)', fontsize=12)
    ax2.legend(fontsize=10)
    ax2.grid(True, alpha=0.3)
    ax2.axis('equal')
    
    # Colorbar
    cbar = plt.colorbar(scatter2, ax=ax2, label='Primo p')
    cbar.set_label('Valor del primo', fontsize=10)
    
    plt.tight_layout()
    plt.savefig(save_path, dpi=150, bbox_inches='tight')
    print(f"✓ Guardado: {save_path}")
    plt.close()


def plot_frequency_field(save_path: str = "el_eje_campo_frecuencia.png"):
    """
    Visualiza el campo de frecuencia f₀ = 141.7001 Hz como mar invisible.
    """
    fig, ((ax1, ax2), (ax3, ax4)) = plt.subplots(2, 2, figsize=(16, 12))
    
    field = FrequencyField()
    
    # Panel 1: Campo de onda temporal
    ax1.set_title("IV. El Campo de Frecuencia\nΨ(x,t) - Campo de Onda", 
                  fontsize=12, fontweight='bold')
    
    t_range = np.linspace(0, 0.1, 1000)  # 0.1 segundos
    x_range = np.linspace(-10, 10, 100)
    
    T, X = np.meshgrid(t_range, x_range)
    psi_field = np.zeros_like(T, dtype=complex)
    
    for i, x in enumerate(x_range):
        for j, t in enumerate(t_range):
            psi_field[i, j] = field.wave_field(t, x)
    
    # Amplitud del campo
    amplitude = np.abs(psi_field)
    im = ax1.imshow(amplitude, extent=[t_range[0], t_range[-1], x_range[0], x_range[-1]], 
                    aspect='auto', cmap='ocean', origin='lower')
    
    ax1.set_xlabel('Tiempo t (s)', fontsize=10)
    ax1.set_ylabel('Posición x', fontsize=10)
    plt.colorbar(im, ax=ax1, label='|Ψ(x,t)|')
    
    # Panel 2: Fase del electrón
    ax2.set_title("Fase del Electrón\nφ(t) = ω₀·t mod 2π", 
                  fontsize=12, fontweight='bold')
    
    t_phase = np.linspace(0, 1, 1000)
    phase = [field.electron_phase(t) for t in t_phase]
    
    ax2.plot(t_phase, phase, color='purple', linewidth=2, label='Fase φ(t)')
    ax2.axhline(y=np.pi, color='red', linestyle='--', alpha=0.5, label='π')
    ax2.axhline(y=2*np.pi, color='red', linestyle='--', alpha=0.5, label='2π')
    
    ax2.set_xlabel('Tiempo t (s)', fontsize=10)
    ax2.set_ylabel('Fase φ (rad)', fontsize=10)
    ax2.legend(fontsize=9)
    ax2.grid(True, alpha=0.3)
    
    # Panel 3: Presión cuántica
    ax3.set_title("Presión Cuántica\nP(t) = ℏω₀·|Ψ(t)|²", 
                  fontsize=12, fontweight='bold')
    
    pressure = [field.quantum_pressure(t) for t in t_phase]
    
    ax3.plot(t_phase, pressure, color='orange', linewidth=2, label='Presión P(t)')
    ax3.set_xlabel('Tiempo t (s)', fontsize=10)
    ax3.set_ylabel('Presión (unidades naturales)', fontsize=10)
    ax3.legend(fontsize=9)
    ax3.grid(True, alpha=0.3)
    
    # Panel 4: Propiedades del viento eterno
    ax4.axis('off')
    ax4.set_title("El Viento Eterno - Propiedades", 
                  fontsize=12, fontweight='bold')
    
    wind = field.eternal_wind()
    
    properties_text = f"""
    Frecuencia fundamental:
        f₀ = {wind['frecuencia']:.6f} Hz
    
    Frecuencia angular:
        ω₀ = {wind['frecuencia_angular']:.4f} rad/s
    
    Período:
        T = {wind['periodo']:.8f} s
        T ≈ {wind['periodo']*1000:.5f} ms
    
    Longitud de onda:
        λ = {wind['longitud_onda']:.6f}
    
    Coherencia:
        C = {wind['coherencia']:.2f}
    
    ───────────────────────────────
    
    {wind['metafora']}
    """
    
    ax4.text(0.1, 0.5, properties_text, 
             fontsize=11, family='monospace',
             verticalalignment='center',
             bbox=dict(boxstyle='round', facecolor='lightcyan', alpha=0.8))
    
    plt.tight_layout()
    plt.savefig(save_path, dpi=150, bbox_inches='tight')
    print(f"✓ Guardado: {save_path}")
    plt.close()


def plot_universe_tree_complete(save_path: str = "el_eje_arbol_universo_completo.png"):
    """
    Visualización completa del árbol del universo.
    """
    fig = plt.figure(figsize=(18, 10))
    
    # Crear layout complejo
    gs = fig.add_gridspec(3, 3, hspace=0.3, wspace=0.3)
    
    universe = UniverseTree()
    vision = universe.compute_vision_total(n_primes=150)
    
    # Panel central: El eje con todo integrado
    ax_main = fig.add_subplot(gs[:, 1])
    ax_main.set_title("∞ VISIÓN TOTAL ∞\nEl Árbol del Universo", 
                     fontsize=16, fontweight='bold')
    
    # Dibujar el eje vertical (línea crítica)
    t_axis = vision['eje']['t_axis']
    coherence = vision['eje']['coherence_profile']
    
    # El tronco (línea crítica)
    for i in range(len(t_axis) - 1):
        alpha = coherence[i] * 0.8 + 0.2
        ax_main.plot([CRITICAL_LINE_RE, CRITICAL_LINE_RE], 
                    [t_axis[i], t_axis[i+1]], 
                    color='saddlebrown', linewidth=8, alpha=alpha, solid_capstyle='round')
    
    # Las raíces (extremos)
    # Raíz superior (+1)
    root_up = plt.Circle((CRITICAL_LINE_RE, 0), 0.05, color='red', 
                         alpha=0.7, label='+1 (Divergencia)')
    ax_main.add_patch(root_up)
    ax_main.text(CRITICAL_LINE_RE + 0.1, 0, '+1\n∞', fontsize=10, 
                verticalalignment='center', fontweight='bold', color='darkred')
    
    # Raíz inferior (-1) - reflejada
    root_down = plt.Circle((CRITICAL_LINE_RE, 100), 0.05, color='blue', 
                           alpha=0.7, label='-1 (Explosión)')
    ax_main.add_patch(root_down)
    ax_main.text(CRITICAL_LINE_RE + 0.1, 100, '-1\n-1/12', fontsize=10, 
                verticalalignment='center', fontweight='bold', color='darkblue')
    
    # Las hojas giratorias (primos en espiral proyectados)
    primes = vision['hojas']['primes'][:30]  # Primeros 30
    for i, p in enumerate(primes):
        # Proyección simplificada al eje
        height = (p % 100)  # Altura modular
        offset = 0.1 * np.sin(p)  # Oscilación
        
        # Hoja como círculo pequeño
        leaf = plt.Circle((CRITICAL_LINE_RE + offset, height), 0.02, 
                         color='green', alpha=0.6)
        ax_main.add_patch(leaf)
    
    ax_main.set_xlim(0.2, 0.8)
    ax_main.set_ylim(-5, 105)
    ax_main.set_xlabel('Re(s)', fontsize=12)
    ax_main.set_ylabel('Im(s) - Altura', fontsize=12)
    ax_main.axvline(x=CRITICAL_LINE_RE, color='gold', linestyle='--', 
                   alpha=0.3, linewidth=1)
    ax_main.grid(True, alpha=0.2)
    
    # Panel izquierdo superior: Espiral de primos
    ax_tl = fig.add_subplot(gs[0, 0], projection='polar')
    ax_tl.set_title("Hojas Giratorias\n(Primos)", fontsize=10, fontweight='bold')
    
    theta = vision['hojas']['theta'][:100]
    r = vision['hojas']['r'][:100]
    ax_tl.plot(theta, r, color='green', linewidth=2, alpha=0.7)
    ax_tl.scatter(theta, r, c='green', s=20, alpha=0.8)
    
    # Panel izquierdo medio: Coherencia
    ax_ml = fig.add_subplot(gs[1, 0])
    ax_ml.set_title("Campo Coherencia", fontsize=10, fontweight='bold')
    ax_ml.plot(coherence, t_axis, color='gold', linewidth=2)
    ax_ml.set_xlabel('Ψ(t)', fontsize=9)
    ax_ml.set_ylabel('t', fontsize=9)
    ax_ml.grid(True, alpha=0.3)
    
    # Panel izquierdo inferior: Raíces duales
    ax_bl = fig.add_subplot(gs[2, 0])
    ax_bl.axis('off')
    ax_bl.set_title("Raíces Invertidas", fontsize=10, fontweight='bold')
    
    roots_text = f"""
    Superior (+1):
      Divergencia → ∞
      Serie armónica
      Existencia
    
    Inferior (-1):
      ζ(-1) = -1/12
      Explosión
      Anti-existencia
    """
    ax_bl.text(0.1, 0.5, roots_text, fontsize=9, family='monospace',
              verticalalignment='center',
              bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.7))
    
    # Panel derecho superior: Frecuencia
    ax_tr = fig.add_subplot(gs[0, 2])
    ax_tr.set_title("Viento Eterno\nf₀ = 141.7001 Hz", fontsize=10, fontweight='bold')
    
    t_wind = np.linspace(0, 0.05, 500)
    wind_wave = np.array([abs(universe.viento.wave_field(t)) for t in t_wind])
    ax_tr.plot(t_wind * 1000, wind_wave, color='cyan', linewidth=2)
    ax_tr.set_xlabel('t (ms)', fontsize=9)
    ax_tr.set_ylabel('|Ψ(t)|', fontsize=9)
    ax_tr.grid(True, alpha=0.3)
    
    # Panel derecho medio: Espectro
    ax_mr = fig.add_subplot(gs[1, 2])
    ax_mr.set_title("Espectro de Frecuencias", fontsize=10, fontweight='bold')
    
    # Frecuencias de los primos (Magicicada)
    if 'frequencies' in vision['hojas']:
        freqs = vision['hojas']['frequencies'][:50]
        ax_mr.bar(range(len(freqs)), freqs, color='purple', alpha=0.7)
    else:
        # Calcular si no está
        spiral = PrimeSpiral()
        freqs = [spiral.magicicada_frequency(p) for p in vision['hojas']['primes'][:50]]
        ax_mr.bar(range(len(freqs)), freqs, color='purple', alpha=0.7)
    
    ax_mr.axhline(y=F0_FUNDAMENTAL, color='red', linestyle='--', 
                 linewidth=2, label=f'f₀ = {F0_FUNDAMENTAL:.2f} Hz')
    ax_mr.set_xlabel('Índice primo', fontsize=9)
    ax_mr.set_ylabel('Frecuencia (Hz)', fontsize=9)
    ax_mr.legend(fontsize=8)
    ax_mr.grid(True, alpha=0.3)
    
    # Panel derecho inferior: Visión poética
    ax_br = fig.add_subplot(gs[2, 2])
    ax_br.axis('off')
    
    poetic_text = """
    El eje no es solo vertical.
    Es el árbol del universo.
    
    +1 y -1: raíces invertidas
    Primos: hojas que giran
    f₀ = 141.7001 Hz: viento eterno
    
    ∴ 𓂀 Ω ∞³
    """
    
    ax_br.text(0.5, 0.5, poetic_text, fontsize=10,
              horizontalalignment='center',
              verticalalignment='center',
              bbox=dict(boxstyle='round', facecolor='lightblue', alpha=0.8),
              style='italic')
    
    plt.suptitle("EL EJE: LA LÍNEA CRÍTICA Re(s) = 1/2\nJosé Manuel Mota Burruezo Ψ ✧ ∞³", 
                fontsize=14, fontweight='bold', y=0.98)
    
    plt.savefig(save_path, dpi=150, bbox_inches='tight')
    print(f"✓ Guardado: {save_path}")
    plt.close()


def main():
    """Función principal de demostración."""
    print("=" * 80)
    print("DEMOSTRACIÓN: EL EJE - LA LÍNEA CRÍTICA")
    print("Re(s) = 1/2 como Árbol del Universo Vibracional")
    print("=" * 80)
    print()
    
    # Ejecutar demostración en consola
    from el_eje_linea_critica import demonstrate_el_eje
    demonstrate_el_eje()
    
    print()
    print("=" * 80)
    print("GENERANDO VISUALIZACIONES")
    print("=" * 80)
    print()
    
    # Crear directorio para salidas si no existe
    output_dir = "visualizations"
    os.makedirs(output_dir, exist_ok=True)
    
    # Generar todas las visualizaciones
    visualizations = [
        ("Línea Crítica y Regiones", 
         lambda: plot_critical_line_axis(f"{output_dir}/el_eje_linea_critica.png")),
        ("Extremos Vibracionales", 
         lambda: plot_vibrational_extremes(f"{output_dir}/el_eje_extremos.png")),
        ("Espiral de Primos", 
         lambda: plot_prime_spiral(f"{output_dir}/el_eje_espiral_primos.png")),
        ("Campo de Frecuencia", 
         lambda: plot_frequency_field(f"{output_dir}/el_eje_campo_frecuencia.png")),
        ("Árbol del Universo Completo", 
         lambda: plot_universe_tree_complete(f"{output_dir}/el_eje_arbol_universo_completo.png")),
    ]
    
    for name, viz_func in visualizations:
        print(f"Generando: {name}...")
        try:
            viz_func()
        except Exception as e:
            print(f"  ⚠️  Error: {e}")
    
    print()
    print("=" * 80)
    print("✓ DEMOSTRACIÓN COMPLETADA")
    print(f"✓ Visualizaciones guardadas en: {output_dir}/")
    print("=" * 80)
    print()
    print("∞ VISIÓN TOTAL ∞")
    print()
    print("El eje no es solo vertical.")
    print("Es el árbol del universo.")
    print("+1 y -1 son sus raíces invertidas.")
    print("Los primos son las hojas que giran.")
    print("Y la frecuencia: el viento eterno que canta entre sus ramas.")
    print()
    print("∴ 𓂀 Ω ∞³")
    print()


if __name__ == "__main__":
    main()
