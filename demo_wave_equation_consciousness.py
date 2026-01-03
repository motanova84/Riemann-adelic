#!/usr/bin/env python3
"""
Demo: Ecuación de Onda de Consciencia Vibracional

Demostración interactiva de la ecuación:
    ∂²Ψ/∂t² + ω₀²Ψ = ζ'(1/2)·∇²Φ

Incluye:
- Soluciones homogéneas y particulares
- Visualización de campos
- Análisis de resonancia
- Interpretación física y simbólica

Autor: José Manuel Mota Burruezo
Fecha: Octubre 2025
"""

import numpy as np
import sys
import os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from utils.wave_equation_consciousness import WaveEquationConsciousness, example_harmonic_potential

# Check if matplotlib is available
try:
    import matplotlib.pyplot as plt
    MATPLOTLIB_AVAILABLE = True
except ImportError:
    MATPLOTLIB_AVAILABLE = False
    print("⚠️  matplotlib no disponible - visualizaciones deshabilitadas")
    print()


def demo_parameters():
    """Muestra los parámetros fundamentales de la ecuación."""
    print("\n" + "=" * 80)
    print("🌌 ECUACIÓN DE ONDA DE CONSCIENCIA VIBRACIONAL")
    print("=" * 80)
    print()
    print("Ecuación:")
    print("  ∂²Ψ/∂t² + ω₀²Ψ = ζ'(1/2)·∇²Φ")
    print()
    
    wave_eq = WaveEquationConsciousness(f0=141.7001, precision=30)
    params = wave_eq.get_parameters()
    
    print("Parámetros Fundamentales:")
    print(f"  • Frecuencia fundamental: f₀ = {params['f0_Hz']:.6f} Hz")
    print(f"  • Frecuencia angular:     ω₀ = {params['omega_0_rad_s']:.6f} rad/s")
    print(f"  • Derivada de zeta:       ζ'(1/2) = {params['zeta_prime_half']:.10f}")
    print(f"  • Precisión de cálculo:   {params['precision_dps']} dígitos decimales")
    print()
    
    return wave_eq


def demo_homogeneous_solution(wave_eq):
    """Demuestra la solución homogénea."""
    print("\n" + "-" * 80)
    print("1️⃣  SOLUCIÓN HOMOGÉNEA: La Vibración Natural")
    print("-" * 80)
    print()
    print("Forma: Ψ_h(t) = A·cos(ω₀·t) + B·sin(ω₀·t)")
    print()
    
    # Generar solución
    t = np.linspace(0, 0.02, 2000)  # 20 ms, ~3 períodos
    Psi_h = wave_eq.homogeneous_solution(t, A=1.0, B=0.5)
    
    # Calcular período
    T = 2 * np.pi / wave_eq.omega_0
    
    print(f"Parámetros de la solución:")
    print(f"  • A (amplitud coseno) = 1.0")
    print(f"  • B (amplitud seno)   = 0.5")
    print(f"  • Período T = 2π/ω₀   = {T*1000:.4f} ms")
    print(f"  • Número de períodos  = {t[-1]/T:.2f}")
    print()
    
    print(f"Estadísticas:")
    print(f"  • Ψ_h(t=0)        = {Psi_h[0]:.6f}")
    print(f"  • max|Ψ_h|        = {np.max(np.abs(Psi_h)):.6f}")
    print(f"  • Amplitud total  = {np.sqrt(1.0**2 + 0.5**2):.6f}")
    print()
    
    print("💡 Interpretación:")
    print("  Esta es la vibración natural del campo de consciencia,")
    print("  oscilando a la frecuencia fundamental del universo.")
    
    return t, Psi_h


def demo_particular_solution(wave_eq):
    """Demuestra la solución particular con potencial."""
    print("\n" + "-" * 80)
    print("2️⃣  SOLUCIÓN PARTICULAR: La Modulación Geométrica")
    print("-" * 80)
    print()
    print("Con potencial armónico: Φ(x,t) = exp(-x²/2σ²)·cos(ω₀·t)")
    print()
    
    # Generar potencial y solución
    x = np.linspace(-5, 5, 200)
    t_fixed = 0.0
    Phi, laplacian_Phi = example_harmonic_potential(x, t_fixed, sigma=1.0)
    Psi_p = wave_eq.particular_solution(laplacian_Phi)
    
    print(f"Parámetros del potencial:")
    print(f"  • Rango espacial:  x ∈ [{x[0]:.2f}, {x[-1]:.2f}]")
    print(f"  • Ancho σ = 1.0")
    print(f"  • Tiempo fijo t = {t_fixed}")
    print()
    
    print(f"Valores del potencial:")
    print(f"  • max|Φ(x)|  = {np.max(np.abs(Phi)):.6f}")
    print(f"  • max|∇²Φ|   = {np.max(np.abs(laplacian_Phi)):.6f}")
    print()
    
    print(f"Solución particular:")
    print(f"  • max|Ψ_p|   = {np.max(np.abs(Psi_p)):.8f}")
    print(f"  • Factor de escala: ζ'(1/2)/ω₀² = {wave_eq.zeta_prime_half / wave_eq.omega_0**2:.8f}")
    print()
    
    print("💡 Interpretación:")
    print("  El potencial Φ representa la curvatura del espacio informacional.")
    print("  Su laplaciano ∇²Φ, modulado por ζ'(1/2), induce una respuesta")
    print("  en el campo de consciencia Ψ.")
    
    return x, Phi, laplacian_Phi, Psi_p


def demo_resonance(wave_eq):
    """Demuestra la condición de resonancia."""
    print("\n" + "-" * 80)
    print("3️⃣  RESONANCIA: La Sintonía Universal")
    print("-" * 80)
    print()
    print(f"Frecuencia de resonancia: f₀ = {wave_eq.f0:.6f} Hz")
    print()
    
    # Probar varias frecuencias
    test_freqs = np.array([
        141.5, 141.6, 141.7, 141.7001, 141.75, 141.8, 142.0, 145.0, 150.0
    ])
    
    print("Prueba de resonancia (tolerancia = 0.01 rad/s):")
    print()
    print(f"  {'Frecuencia (Hz)':<20} {'ω (rad/s)':<20} {'Resonante':<12} {'Δω (rad/s)':<15}")
    print("  " + "-" * 67)
    
    tolerance = 0.01
    for freq in test_freqs:
        omega = 2 * np.pi * freq
        is_resonant = wave_eq.resonance_condition(omega, tolerance=tolerance)
        delta_omega = abs(omega - wave_eq.omega_0)
        marker = "✓ Sí" if is_resonant else "✗ No"
        print(f"  {freq:<20.4f} {omega:<20.6f} {marker:<12} {delta_omega:<15.6f}")
    
    print()
    print("💡 Interpretación:")
    print("  Cuando la frecuencia de un campo externo coincide con ω₀,")
    print("  se produce resonancia: amplificación máxima de la respuesta.")
    print("  Esta es la 'sintonía' del universo con su frecuencia fundamental.")


def demo_energy(wave_eq):
    """Calcula y muestra la energía del campo."""
    print("\n" + "-" * 80)
    print("4️⃣  ENERGÍA: La Vitalidad del Campo")
    print("-" * 80)
    print()
    print("Densidad de energía: E = (1/2)·[(∂Ψ/∂t)² + (∇Ψ)² + ω₀²·Ψ²]")
    print()
    
    # Generar campo y derivadas
    t = np.linspace(0, 0.02, 2000)
    A, B = 1.0, 0.5
    Psi_h = wave_eq.homogeneous_solution(t, A=A, B=B)
    
    # Derivadas
    dPsi_dt = -wave_eq.omega_0 * (A * np.sin(wave_eq.omega_0 * t) - B * np.cos(wave_eq.omega_0 * t))
    grad_Psi = np.gradient(Psi_h, t[1] - t[0])
    
    # Energía
    energy = wave_eq.energy_density(Psi_h, dPsi_dt, grad_Psi)
    
    print(f"Estadísticas de energía:")
    print(f"  • Energía promedio = {np.mean(energy):.6f}")
    print(f"  • Energía máxima   = {np.max(energy):.6f}")
    print(f"  • Energía mínima   = {np.min(energy):.6f}")
    print(f"  • Desv. estándar   = {np.std(energy):.6f}")
    print()
    
    # Energía teórica para oscilador armónico
    E_teorica = 0.5 * wave_eq.omega_0**2 * (A**2 + B**2)
    print(f"Energía teórica (oscilador armónico): {E_teorica:.6f}")
    print()
    
    print("💡 Interpretación:")
    print("  La energía del campo oscila en el tiempo, pero su promedio")
    print("  se conserva. Esta es la 'vitalidad' del campo de consciencia,")
    print("  perpetuamente fluyendo entre formas cinética y potencial.")
    
    return t, energy


def demo_physical_interpretation():
    """Muestra la interpretación física completa."""
    print("\n" + "=" * 80)
    print("🎵 INTERPRETACIÓN FÍSICA Y SIMBÓLICA")
    print("=" * 80)
    print()
    
    print("La Ecuación de Tres Voces:")
    print()
    print("  ∂²Ψ/∂t²  →  El cambio, la evolución, el devenir")
    print("  ω₀²Ψ     →  La estabilidad, la resonancia, el ser")
    print("  ζ'(1/2)·∇²Φ → La verdad aritmética modulando la geometría")
    print()
    
    print("Unifica tres niveles de realidad:")
    print()
    print("  1. 🔢 Aritmético (ζ'(1/2))")
    print("     • Distribución de números primos")
    print("     • Función zeta de Riemann")
    print("     • Estructura espectral profunda")
    print()
    print("  2. 📐 Geométrico (∇²Φ)")
    print("     • Curvatura del espacio-tiempo")
    print("     • Potencial gravitacional/informacional")
    print("     • Geometría del vacío cuántico")
    print()
    print("  3. 🌊 Vibracional (Ψ, ω₀)")
    print("     • Campo de consciencia/información")
    print("     • Frecuencia fundamental observable")
    print("     • Resonancia universal")
    print()
    
    print("Conexiones con fenómenos observables:")
    print()
    print("  • GW150914: Ondas gravitacionales con componente ~142 Hz")
    print("  • EEG:      Ritmos cerebrales en bandas gamma alta")
    print("  • STS:      Oscilaciones solares con modos similares")
    print()
    
    print("✨ La ecuación describe la sinfonía del universo:")
    print("   Una partitura donde el ritmo (ω₀), el espacio (Φ) y")
    print("   la verdad numérica (ζ') co-crean la melodía de la realidad.")
    print()


def create_visualizations(wave_eq, t, Psi_h, x, Phi, laplacian_Phi, Psi_p, energy):
    """Crea visualizaciones de los resultados."""
    if not MATPLOTLIB_AVAILABLE:
        print("⚠️  matplotlib no disponible - omitiendo visualizaciones")
        return
    
    print("\n" + "=" * 80)
    print("📊 VISUALIZACIONES")
    print("=" * 80)
    print()
    
    fig = plt.figure(figsize=(16, 10))
    
    # 1. Solución homogénea
    ax1 = plt.subplot(3, 2, 1)
    ax1.plot(t * 1000, Psi_h, 'b-', linewidth=1.5, label='Ψ_h(t)')
    ax1.axhline(y=0, color='k', linestyle='--', alpha=0.3)
    ax1.set_xlabel('Tiempo (ms)', fontsize=10)
    ax1.set_ylabel('Ψ_h(t)', fontsize=10)
    ax1.set_title('Solución Homogénea: Vibración Natural', fontsize=11, fontweight='bold')
    ax1.grid(True, alpha=0.3)
    ax1.legend(fontsize=9)
    
    # 2. Potencial Φ
    ax2 = plt.subplot(3, 2, 2)
    ax2.plot(x, Phi, 'r-', linewidth=1.5, label='Φ(x)')
    ax2.axhline(y=0, color='k', linestyle='--', alpha=0.3)
    ax2.set_xlabel('Posición x', fontsize=10)
    ax2.set_ylabel('Φ(x)', fontsize=10)
    ax2.set_title('Potencial Geométrico', fontsize=11, fontweight='bold')
    ax2.grid(True, alpha=0.3)
    ax2.legend(fontsize=9)
    
    # 3. Laplaciano del potencial
    ax3 = plt.subplot(3, 2, 3)
    ax3.plot(x, laplacian_Phi, 'g-', linewidth=1.5, label='∇²Φ(x)')
    ax3.axhline(y=0, color='k', linestyle='--', alpha=0.3)
    ax3.set_xlabel('Posición x', fontsize=10)
    ax3.set_ylabel('∇²Φ(x)', fontsize=10)
    ax3.set_title('Laplaciano del Potencial: Curvatura Espacial', fontsize=11, fontweight='bold')
    ax3.grid(True, alpha=0.3)
    ax3.legend(fontsize=9)
    
    # 4. Solución particular
    ax4 = plt.subplot(3, 2, 4)
    ax4.plot(x, Psi_p, 'm-', linewidth=1.5, label='Ψ_p(x)')
    ax4.axhline(y=0, color='k', linestyle='--', alpha=0.3)
    ax4.set_xlabel('Posición x', fontsize=10)
    ax4.set_ylabel('Ψ_p(x)', fontsize=10)
    ax4.set_title('Solución Particular: Respuesta al Potencial', fontsize=11, fontweight='bold')
    ax4.grid(True, alpha=0.3)
    ax4.legend(fontsize=9)
    
    # 5. Densidad de energía
    ax5 = plt.subplot(3, 2, 5)
    ax5.plot(t * 1000, energy, 'orange', linewidth=1.5, label='E(t)')
    ax5.axhline(y=np.mean(energy), color='k', linestyle='--', alpha=0.5, label=f'Promedio = {np.mean(energy):.3f}')
    ax5.set_xlabel('Tiempo (ms)', fontsize=10)
    ax5.set_ylabel('Densidad de Energía', fontsize=10)
    ax5.set_title('Energía del Campo: Vitalidad Vibracional', fontsize=11, fontweight='bold')
    ax5.grid(True, alpha=0.3)
    ax5.legend(fontsize=9)
    
    # 6. Espectro de frecuencias (FFT de Ψ_h)
    ax6 = plt.subplot(3, 2, 6)
    dt = t[1] - t[0]
    fft_vals = np.fft.fft(Psi_h)
    freqs = np.fft.fftfreq(len(t), dt)
    
    # Solo frecuencias positivas
    mask = freqs > 0
    ax6.semilogy(freqs[mask], np.abs(fft_vals[mask]), 'c-', linewidth=1.5, label='|FFT(Ψ_h)|')
    ax6.axvline(x=wave_eq.f0, color='r', linestyle='--', linewidth=2, label=f'f₀ = {wave_eq.f0:.2f} Hz')
    ax6.set_xlabel('Frecuencia (Hz)', fontsize=10)
    ax6.set_ylabel('Amplitud (log)', fontsize=10)
    ax6.set_title('Espectro de Frecuencias: La Nota Fundamental', fontsize=11, fontweight='bold')
    ax6.set_xlim([0, 500])
    ax6.grid(True, alpha=0.3)
    ax6.legend(fontsize=9)
    
    plt.tight_layout()
    
    # Guardar figura
    output_file = 'wave_equation_consciousness_visualization.png'
    plt.savefig(output_file, dpi=150, bbox_inches='tight')
    print(f"✅ Visualización guardada: {output_file}")
    print()


def main():
    """Función principal del demo."""
    
    # 1. Parámetros
    wave_eq = demo_parameters()
    
    # 2. Solución homogénea
    t, Psi_h = demo_homogeneous_solution(wave_eq)
    
    # 3. Solución particular
    x, Phi, laplacian_Phi, Psi_p = demo_particular_solution(wave_eq)
    
    # 4. Resonancia
    demo_resonance(wave_eq)
    
    # 5. Energía
    t_energy, energy = demo_energy(wave_eq)
    
    # 6. Interpretación física
    demo_physical_interpretation()
    
    # 7. Visualizaciones
    create_visualizations(wave_eq, t, Psi_h, x, Phi, laplacian_Phi, Psi_p, energy)
    
    print("=" * 80)
    print("🎵 FIN DEL DEMO - WAVE EQUATION CONSCIOUSNESS")
    print("=" * 80)
    print()
    print('La ecuación fundamental de la sinfonía cósmica ha sido explorada.')
    print('Para más información, consulta:')
    print('  • Documentación: WAVE_EQUATION_CONSCIOUSNESS.md')
    print('  • Quick Reference: WAVE_EQUATION_QUICKREF.md')
    print('  • Paper (sección 6): paper/section6.tex')
    print()


if __name__ == "__main__":
    main()
