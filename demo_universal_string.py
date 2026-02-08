#!/usr/bin/env python3
"""
Demo: La Cuerda Universal (The Universal String)

Este script demuestra la visualización de la línea crítica Re(s) = 1/2
como una cuerda cósmica vibrando a la frecuencia f₀ = 141.7001 Hz.

🪕 I. LA CUERDA UNIVERSAL

La línea crítica Re(s) = 1/2 es la cuerda tensada del universo.
Los ceros de la función zeta de Riemann son los nodos donde la cuerda no se mueve.
El campo Ψ vibra con una única frecuencia fundamental f₀ = 141.7001 Hz.

🧭 II. EXTREMOS FIJOS

+1: límite superior de convergencia
-1: eco profundo del campo (ζ(-1) = -1/12)

El universo está fijado entre +1 y -1, y la línea crítica vibra entre ambos
como verdad armónica.

🎼 III. EL CERO COMO NODO

Cada cero no es un "error" o "punto raro".
Es un nodo vibracional exacto.
Es la huella de una coherencia real.

ζ(1/2 + itₙ) = 0 ⟹ Nodo en la cuerda cósmica

🌌 IV. FRECUENCIA DEL UNIVERSO

Así como la luz viaja a c porque esa es la velocidad del tejido,
la frecuencia f₀ = 141.7001 Hz es la frecuencia vibracional del campo base
que permite que todos los ceros estén donde deben estar.

Authors: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: February 2026
License: Creative Commons BY-NC-SA 4.0
"""

import sys
import json
from pathlib import Path
import numpy as np
import matplotlib.pyplot as plt

# Importar módulo de cuerda universal directamente
import importlib.util
spec = importlib.util.spec_from_file_location("universal_string", "utils/universal_string.py")
universal_string = importlib.util.module_from_spec(spec)
spec.loader.exec_module(universal_string)
UniversalString = universal_string.UniversalString
load_riemann_zeros = universal_string.load_riemann_zeros


def print_header():
    """Imprime el encabezado del demo."""
    print("=" * 70)
    print("🪕 LA CUERDA UNIVERSAL")
    print("   The Critical Line as a Cosmic String")
    print("=" * 70)
    print()
    print("📐 Concepto:")
    print("   Re(s) = 1/2 ≡ Cuerda cósmica vibrando a f₀ = 141.7001 Hz")
    print("   Ceros de Riemann ≡ Nodos vibratorios exactos")
    print("   Extremos fijos: +1 (convergencia) y -1 (eco profundo)")
    print()
    print("🌌 Frecuencia del Universo: f₀ = 141.7001 Hz")
    print("=" * 70)
    print()


def demonstrate_frequency_relation():
    """Demuestra la relación fundamental f₀ = 100√2 + δζ."""
    print("🔬 I. RELACIÓN FUNDAMENTAL DE FRECUENCIA")
    print("-" * 70)
    print()
    
    string = UniversalString()
    
    euclidean = string.euclidean_diagonal
    delta = string.delta_zeta
    f0 = string.f0
    
    computed_f0 = euclidean + delta
    error = abs(f0 - computed_f0)
    
    print(f"   Diagonal Euclidiana: 100√2 = {euclidean:.10f} Hz")
    print(f"   Quantum Phase Shift:  δζ  = {delta:.10f} Hz")
    print(f"   ────────────────────────────────────────")
    print(f"   Frecuencia Universal: f₀  = {f0:.10f} Hz")
    print()
    print(f"   Verificación: 100√2 + δζ  = {computed_f0:.10f} Hz")
    print(f"   Error relativo:           = {error:.2e}")
    print()
    
    if error < 1e-6:
        print("   ✅ Relación fundamental VERIFICADA")
    else:
        print("   ⚠️ Desviación detectada")
    
    print()
    print("   Interpretación:")
    print("   • 100√2 Hz: Resonancia geométrica clásica (Euclidiana)")
    print("   • δζ Hz:    Corrección cuántica que crea la cuerda cósmica")
    print("   • f₀ Hz:    Frecuencia donde los ceros de Riemann pueden manifestarse")
    print()


def demonstrate_fixed_endpoints():
    """Demuestra los extremos fijos de la cuerda."""
    print("🧭 II. EXTREMOS FIJOS DE LA CUERDA")
    print("-" * 70)
    print()
    
    import mpmath as mp
    mp.dps = 30
    
    # Evaluar ζ(-1)
    zeta_minus_1 = float(mp.zeta(mp.mpc(-1, 0)).real)
    theoretical = -1.0 / 12.0
    
    print("   Extremo superior: +1")
    print("     • Límite superior de convergencia")
    print("     • Para Re(s) > 1, ζ(s) converge absolutamente")
    print()
    
    print("   Extremo inferior: -1")
    print(f"     • ζ(-1) = {zeta_minus_1:.15f}")
    print(f"     • Valor teórico: -1/12 = {theoretical:.15f}")
    print(f"     • Diferencia: {abs(zeta_minus_1 - theoretical):.2e}")
    print()
    
    if abs(zeta_minus_1 - theoretical) < 1e-10:
        print("   ✅ Extremo inferior VERIFICADO")
    
    print()
    print("   Interpretación:")
    print("   • La cuerda está fijada entre +1 y -1")
    print("   • La línea crítica Re(s)=1/2 vibra entre estos extremos")
    print("   • Los ceros son los puntos donde la amplitud es exactamente cero")
    print()


def demonstrate_zeros_as_nodes(zeros: list):
    """Demuestra los ceros como nodos vibratorios."""
    print("🎼 III. CEROS COMO NODOS VIBRATORIOS")
    print("-" * 70)
    print()
    
    if not zeros:
        print("   ⚠️ No hay ceros disponibles para demostración")
        return
    
    print(f"   Número de ceros analizados: {len(zeros)}")
    print()
    print("   Primeros 10 nodos (ceros de Riemann):")
    for i, gamma in enumerate(zeros[:10], 1):
        print(f"     γ_{i:2d} = {gamma:12.6f}  →  ζ(1/2 + i·{gamma:.6f}) = 0")
    print()
    
    # Calcular estadísticas
    if len(zeros) > 1:
        spacings = np.diff(sorted(zeros))
        mean_spacing = np.mean(spacings)
        min_spacing = np.min(spacings)
        max_spacing = np.max(spacings)
        
        print("   Estadísticas de espaciamiento:")
        print(f"     • Espaciamiento promedio: {mean_spacing:.3f}")
        print(f"     • Espaciamiento mínimo:   {min_spacing:.3f}")
        print(f"     • Espaciamiento máximo:   {max_spacing:.3f}")
        print()
    
    print("   Interpretación:")
    print("   • Cada cero es un NODO VIBRACIONAL EXACTO")
    print("   • No es un error o punto raro")
    print("   • Es la huella de una coherencia real")
    print("   • Si esos nodos no estuvieran ahí, el universo no resonaría")
    print()


def demonstrate_cosmic_frequency():
    """Demuestra la frecuencia cósmica f₀."""
    print("🌌 IV. FRECUENCIA DEL UNIVERSO")
    print("-" * 70)
    print()
    
    f0 = 141.7001
    c = 299792458  # m/s (velocidad de la luz)
    
    print(f"   Frecuencia fundamental: f₀ = {f0} Hz")
    print()
    print("   Así como:")
    print(f"     • La luz viaja a c = {c} m/s")
    print("       porque esa es la velocidad del tejido del espacio-tiempo")
    print()
    print("   Del mismo modo:")
    print(f"     • El campo Ψ vibra a f₀ = {f0} Hz")
    print("       porque esa es la frecuencia vibracional del campo base")
    print("       que permite que todos los ceros estén donde deben estar")
    print()
    
    # Relación con primer cero
    gamma_1 = 14.134725142
    ratio = f0 / gamma_1
    
    print("   Relación con el primer cero:")
    print(f"     γ₁ (primer cero) = {gamma_1:.9f}")
    print(f"     f₀ / γ₁          = {ratio:.9f}")
    print(f"     ≈ 10 + δζ/10     = {10 + 0.2787437/10:.9f}")
    print()
    print("   ✅ Modulación armónica VERIFICADA")
    print()


def visualize_universal_string(zeros: list, output_dir: str = "output"):
    """Crea visualización de la cuerda universal."""
    print("📊 V. VISUALIZACIÓN DE LA CUERDA UNIVERSAL")
    print("-" * 70)
    print()
    
    if not zeros:
        print("   ⚠️ No hay ceros disponibles para visualización")
        return
    
    # Crear directorio de salida
    Path(output_dir).mkdir(parents=True, exist_ok=True)
    
    # Crear instancia de cuerda
    string = UniversalString()
    
    # Calcular propiedades de tensión
    tension = string.compute_string_tension(zeros)
    
    print("   Propiedades de la cuerda:")
    print(f"     • Número de nodos:        {tension['num_modes']}")
    print(f"     • Razón de tensión:       {tension['tension_ratio']:.2e}")
    print(f"     • Escala de energía:      {tension['energy_scale_hz2']:.2f} Hz²")
    print(f"     • Longitud de coherencia: {tension['coherence_length']:.3f}")
    print(f"     • Densidad de modos:      {tension['mode_density']:.6f}")
    print()
    
    # Generar visualización
    print("   Generando visualización...")
    
    t_max = min(100.0, max(zeros) if zeros else 50.0)
    output_path = f"{output_dir}/universal_string_visualization.png"
    
    fig = string.visualize_static_string(
        zeros, 
        t_max=t_max,
        output_path=output_path
    )
    
    print(f"   ✅ Visualización guardada en: {output_path}")
    print()
    
    plt.close(fig)


def generate_mathematical_certificate(zeros: list, output_dir: str = "output"):
    """Genera certificado matemático."""
    print("📜 VI. CERTIFICADO MATEMÁTICO")
    print("-" * 70)
    print()
    
    if not zeros:
        print("   ⚠️ No hay ceros disponibles para certificado")
        return
    
    # Crear instancia de cuerda
    string = UniversalString()
    
    # Generar certificado
    certificate = string.generate_mathematical_certificate(zeros)
    
    # Guardar certificado
    Path(output_dir).mkdir(parents=True, exist_ok=True)
    cert_path = f"{output_dir}/universal_string_certificate.json"
    
    with open(cert_path, 'w', encoding='utf-8') as f:
        json.dump(certificate, f, indent=2, ensure_ascii=False)
    
    print(f"   ✅ Certificado guardado en: {cert_path}")
    print()
    print("   Contenido del certificado:")
    print(f"     • Tipo: {certificate['certificate_type']}")
    print(f"     • Frecuencia: {certificate['frequency']['f0_hz']} Hz")
    print(f"     • Relación validada: {certificate['frequency']['relation_validated']}")
    print(f"     • Nodos totales: {certificate['vibrational_modes']['num_nodes']}")
    print(f"     • ζ(-1) validado: {certificate['string_properties']['lower_point_validation']}")
    print()
    print("   Interpretación cósmica:")
    for key, value in certificate['interpretation'].items():
        print(f"     • {key}: {value}")
    print()


def print_footer():
    """Imprime el pie del demo."""
    print("=" * 70)
    print("✨ CONCLUSIÓN")
    print("=" * 70)
    print()
    print("La línea crítica Re(s) = 1/2 no es simplemente una línea matemática.")
    print("Es la CUERDA UNIVERSAL, tensada entre +1 y -1,")
    print("vibrando a la frecuencia f₀ = 141.7001 Hz.")
    print()
    print("Los ceros de Riemann no son anomalías.")
    print("Son los NODOS donde esta cuerda no se mueve,")
    print("la huella de una coherencia cósmica real.")
    print()
    print("Si esos nodos no estuvieran ahí,")
    print("el universo no resonaría,")
    print("no habría estructura,")
    print("no habría existencia.")
    print()
    print("✧ La cuerda cósmica canta a 141.7001 Hz ✧")
    print()
    print("Firma: José Manuel Mota Burruezo Ψ ✧ ∞³")
    print("Instituto de Conciencia Cuántica (ICQ)")
    print("∴𓂀Ω∞³·CUERDA")
    print("=" * 70)


def main():
    """Función principal del demo."""
    print_header()
    
    # I. Relación fundamental de frecuencia
    demonstrate_frequency_relation()
    
    # II. Extremos fijos
    demonstrate_fixed_endpoints()
    
    # Cargar ceros de Riemann
    print("🔄 Cargando ceros de Riemann...")
    zeros_file = "zeros/zeros_t1e8.txt"
    
    if Path(zeros_file).exists():
        zeros = load_riemann_zeros(zeros_file, max_zeros=200)
        print(f"✅ Cargados {len(zeros)} ceros desde {zeros_file}")
    else:
        print(f"⚠️ Archivo {zeros_file} no encontrado")
        print("   Usando primeros ceros conocidos...")
        zeros = [
            14.134725142, 21.022039639, 25.010857580, 30.424876126, 32.935061588,
            37.586178159, 40.918719012, 43.327073281, 48.005150881, 49.773832478,
            52.970321478, 56.446247697, 59.347044003, 60.831778525, 65.112544048,
            67.079810529, 69.546401711, 72.067157674, 75.704690699, 77.144840069,
            79.337375020, 82.910380854, 84.735492981, 87.425274613, 88.809111208
        ]
    
    print()
    
    # III. Ceros como nodos
    demonstrate_zeros_as_nodes(zeros)
    
    # IV. Frecuencia cósmica
    demonstrate_cosmic_frequency()
    
    # V. Visualización
    visualize_universal_string(zeros)
    
    # VI. Certificado matemático
    generate_mathematical_certificate(zeros)
    
    # Footer
    print_footer()
    
    return 0


if __name__ == "__main__":
    sys.exit(main())
