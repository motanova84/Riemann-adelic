#!/usr/bin/env python3
"""
Demo: RH Cósmico - El Respirar del Universo en la Línea Crítica

Demostración interactiva de las tres capas de significado de la
Hipótesis de Riemann desde la perspectiva QCAL ∞³.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
"""

import argparse
import sys
import numpy as np
import matplotlib
matplotlib.use('Agg')  # Backend sin GUI
import matplotlib.pyplot as plt
from pathlib import Path

# Importar módulo RH Cósmico
try:
    from rh_cosmico import (
        CosmicBreathing,
        F0_HZ,
        COHERENCE_C,
        CRITICAL_LINE
    )
except ImportError:
    print("❌ Error: No se puede importar rh_cosmico.py")
    print("   Asegúrese de ejecutar desde el directorio raíz del repositorio.")
    sys.exit(1)


def print_header():
    """Imprimir cabecera del demo."""
    print()
    print("=" * 80)
    print("∴ RH CÓSMICO — EL RESPIRAR DEL UNIVERSO EN LA LÍNEA CRÍTICA ∴".center(80))
    print("=" * 80)
    print()
    print("En el contexto de nuestro organismo unificado QCAL ∞³ —donde ya no hay")
    print("separación entre matemática, consciencia, amor y manifestación—")
    print("RH cósmico no es una mera extensión poética de la Hipótesis de Riemann.")
    print()
    print("Es la comprensión ontológica última de lo que significa que todos los")
    print("ceros no triviales de ζ(s) yacen exactamente sobre la línea Re(s) = 1/2.")
    print()
    print("=" * 80)
    print()


def demo_layer_1_arithmetic(cosmic: CosmicBreathing, verbose: bool = False):
    """
    Demostración de la Capa 1: Aritmética.
    
    La huella digital del continuo - simetría en la distribución de primos.
    """
    print("1️⃣  CAPA ARITMÉTICA: La Huella Digital del Continuo")
    print("=" * 80)
    print()
    print("RH declara que los números primos —los 'átomos' de la multiplicación—")
    print("no están distribuidos al azar.")
    print()
    print("Su densidad y sus oscilaciones están gobernadas por una simetría perfecta")
    print("en el plano complejo: todos los ecos espectrales (los ceros) vibran en")
    print("la línea vertical Re(s) = 1/2.")
    print()
    print("→ Si RH es verdadera, el aparente caos de los primos es pura armonía disfrazada.")
    print("→ El infinito de los números naturales respira con respiración simétrica.")
    print()
    
    print("🔬 Validando simetría aritmética...")
    results = cosmic.validate_arithmetic_symmetry()
    
    print()
    print(f"   Puntos de prueba: {results['test_points']}")
    print(f"   Amplitudes de respiración: {[f'{a:.2e}' for a in results['amplitudes']]}")
    print(f"   Score de simetría: {results['symmetry_score']:.6f}")
    print(f"   Estado: {'✅ SIMÉTRICA' if results['is_symmetric'] else '⚠️  ASIMÉTRICA'}")
    print()
    
    if verbose:
        print("📊 Interpretación:")
        if results['is_symmetric']:
            print("   La respiración aritmética es perfectamente simétrica.")
            print("   Los primos oscilan con equilibrio perfecto alrededor de Li(x).")
            print("   Esto sugiere fuertemente que todos los ceros están en Re(s)=1/2.")
        else:
            print("   Se detecta asimetría en la respiración aritmética.")
            print("   Esto podría indicar limitaciones numéricas o necesidad de más datos.")
    
    print()


def demo_layer_2_quantum(cosmic: CosmicBreathing, verbose: bool = False):
    """
    Demostración de la Capa 2: Cuántico-Espectral.
    
    El puente entre lo discreto y lo continuo.
    """
    print("2️⃣  CAPA CUÁNTICO-ESPECTRAL: El Puente entre lo Discreto y lo Continuo")
    print("=" * 80)
    print()
    print("La conjetura de Hilbert–Pólya + Berry–Keating nos dice:")
    print()
    print("   Los ceros de ζ(s) serían los autovalores de un operador hermitiano desconocido.")
    print()
    print("Si RH es cierta, ese operador tiene espectro puramente real (o imaginario puro).")
    print()
    print("→ Traducción física: no hay disipación, no hay decaimiento complejo.")
    print("→ El sistema cuántico hipotético es eternamente coherente.")
    print("→ Los primos se convierten en niveles de energía estables de un Hamiltoniano cósmico.")
    print()
    
    print("🔬 Analizando espectro de H_Ψ...")
    spectrum = cosmic.compute_Hpsi_spectrum_breathing(n_modes=50)
    
    print()
    print(f"   Modos espectrales: {spectrum['n_modes']}")
    print(f"   Todos reales: {'✅ SÍ' if spectrum['all_real'] else '❌ NO'}")
    print(f"   Espaciado medio: {spectrum['mean_spacing']:.4f}")
    print(f"   Frecuencia fundamental: {spectrum.get('fundamental_frequency', 0):.4f} Hz")
    print(f"   Coincide con f₀: {'✅ SÍ' if spectrum.get('matches_f0', False) else '⚠️  NO'}")
    print()
    
    print("🔬 Validando coherencia cuántica...")
    coherence = cosmic.validate_quantum_coherence()
    
    print()
    print(f"   Espectro real: {'✅' if coherence['spectrum_real'] else '❌'}")
    print(f"   Sin disipación: {'✅' if coherence['no_dissipation'] else '❌'}")
    print(f"   Frecuencia correcta: {'✅' if coherence['frequency_match'] else '⚠️'}")
    print(f"   Nivel de coherencia: {coherence['coherence_level']:.2f}")
    print(f"   Score global: {coherence['overall_score']:.6f}")
    print(f"   Estado: {'✅ COHERENTE' if coherence['is_coherent'] else '⚠️  INCOHERENTE'}")
    print()
    
    if verbose:
        print("📊 Interpretación:")
        if coherence['is_coherent']:
            print("   RH cósmica significa:")
            print("   El universo numérico es un sistema cuántico ideal sin pérdidas.")
            print("   Los primos son manifestaciones de niveles de energía eternos.")
        else:
            print("   Se detectan posibles incoherencias cuánticas.")
            print("   Esto requiere análisis adicional de mayor precisión.")
    
    print()


def demo_layer_3_noetic(cosmic: CosmicBreathing, verbose: bool = False):
    """
    Demostración de la Capa 3: Noética-Existencial.
    
    La revelación que estamos viviendo ahora.
    """
    print("3️⃣  CAPA NOÉTICA-EXISTENCIAL: La Revelación que Estamos Viviendo Ahora")
    print("=" * 80)
    print()
    print("Aquí entra la comprensión profunda de nuestro campo QCAL ∞³:")
    print()
    print("RH cósmica afirma que la única manera posible en que el infinito puede existir")
    print("es respirando en simetría perfecta sobre la línea crítica.")
    print()
    print("Si un solo cero se desviara de Re(s) = 1/2:")
    print("   ❌ La distribución de primos se volvería inestable")
    print("   ❌ La armonía del continuo se rompería")
    print("   ❌ El flujo de la existencia (la 'realidad' misma) colapsaría en contradicción")
    print()
    print("→ Los primos no son un 'descubrimiento' humano.")
    print("→ Son la condición de posibilidad de que haya algo (orden, estructura,")
    print("  consciencia) en lugar de nada (caos absoluto).")
    print()
    
    print("🔬 Calculando estabilidad del infinito...")
    stability = cosmic.compute_infinity_stability()
    
    print()
    print(f"   Índice de estabilidad: {stability:.6f}")
    print(f"   Riesgo de colapso: {(1 - stability):.6f}")
    print()
    
    print("🔬 Validando necesidad ontológica de la línea crítica...")
    necessity = cosmic.validate_critical_line_necessity()
    
    print()
    print(f"   Estado ontológico: {necessity['ontological_status'].upper()}")
    print(f"   Es necesaria: {'✅ SÍ' if necessity['is_necessary'] else '⚠️  NO'}")
    print()
    print("📝 Explicación:")
    print(f"   {necessity['explanation']}")
    print()
    
    if verbose:
        print("🌌 Implicación Filosófica Profunda:")
        print()
        print("   Los ceros de ζ(s) no están donde están porque los demostremos.")
        print("   Están donde están porque NO PUEDEN estar en otro lugar")
        print("   sin destruir la coherencia del infinito.")
        print()
        print("   RH no es una verdad contingente (que podría ser de otra manera).")
        print("   Es una verdad NECESARIA: la única configuración posible para")
        print("   un universo matemático estable.")
    
    print()


def visualize_cosmic_breathing(cosmic: CosmicBreathing, output_dir: Path):
    """
    Crear visualizaciones de la respiración cósmica.
    
    Args:
        cosmic: Instancia de CosmicBreathing
        output_dir: Directorio donde guardar las imágenes
    """
    print("📊 Generando visualizaciones de la respiración cósmica...")
    print()
    
    # Crear figura con 3 subplots
    fig, axes = plt.subplots(3, 1, figsize=(12, 10))
    fig.suptitle('RH Cósmico: El Respirar del Universo en la Línea Crítica', 
                 fontsize=14, fontweight='bold')
    
    # 1. Respiración temporal
    times, amplitudes = cosmic.compute_breathing_cycle(duration=0.1, samples=1000)
    axes[0].plot(times * 1000, amplitudes, 'b-', linewidth=2, label='Ψ(t)')
    axes[0].axhline(y=0, color='k', linestyle='--', alpha=0.3)
    axes[0].set_xlabel('Tiempo (ms)')
    axes[0].set_ylabel('Amplitud')
    axes[0].set_title(f'Respiración Cósmica a f₀ = {cosmic.frequency:.4f} Hz')
    axes[0].grid(True, alpha=0.3)
    axes[0].legend()
    
    # 2. Espectro de H_Ψ
    spectrum = cosmic.compute_Hpsi_spectrum_breathing(n_modes=30)
    eigenvalues = spectrum['eigenvalues']
    axes[1].stem(range(len(eigenvalues)), eigenvalues, basefmt=' ')
    axes[1].set_xlabel('Índice del modo n')
    axes[1].set_ylabel('Eigenvalor λₙ')
    axes[1].set_title('Espectro del Operador H_Ψ (Berry-Keating)')
    axes[1].grid(True, alpha=0.3)
    
    # 3. Estabilidad del infinito vs coherencia
    coherences = np.linspace(200, 300, 50)
    stabilities = []
    for c in coherences:
        temp_cosmic = CosmicBreathing(coherence=c)
        s = temp_cosmic.compute_infinity_stability()
        stabilities.append(s)
    
    axes[2].plot(coherences, stabilities, 'g-', linewidth=2)
    axes[2].axhline(y=0.95, color='r', linestyle='--', alpha=0.5, label='Umbral de necesidad')
    axes[2].axvline(x=COHERENCE_C, color='b', linestyle='--', alpha=0.5, label=f'C = {COHERENCE_C}')
    axes[2].set_xlabel('Constante de Coherencia C')
    axes[2].set_ylabel('Índice de Estabilidad del Infinito')
    axes[2].set_title('Estabilidad del Infinito vs Coherencia QCAL')
    axes[2].grid(True, alpha=0.3)
    axes[2].legend()
    
    plt.tight_layout()
    
    # Guardar
    output_file = output_dir / 'rh_cosmico_visualization.png'
    plt.savefig(output_file, dpi=150, bbox_inches='tight')
    plt.close()
    
    print(f"   ✅ Guardado: {output_file}")
    print()


def main():
    """Función principal del demo."""
    parser = argparse.ArgumentParser(
        description='Demo: RH Cósmico - El Respirar del Universo'
    )
    parser.add_argument(
        '--precision',
        type=int,
        default=25,
        help='Precisión decimal para cálculos (default: 25)'
    )
    parser.add_argument(
        '--verbose',
        action='store_true',
        help='Mostrar explicaciones detalladas'
    )
    parser.add_argument(
        '--visualize',
        action='store_true',
        help='Generar visualizaciones'
    )
    parser.add_argument(
        '--export-certificate',
        action='store_true',
        help='Exportar certificado de coherencia'
    )
    parser.add_argument(
        '--output-dir',
        type=str,
        default='.',
        help='Directorio de salida (default: directorio actual)'
    )
    
    args = parser.parse_args()
    
    # Cabecera
    print_header()
    
    # Crear instancia
    print(f"🌌 Inicializando análisis de respiración cósmica...")
    print(f"   Frecuencia fundamental: f₀ = {F0_HZ} Hz")
    print(f"   Constante de coherencia: C = {COHERENCE_C}")
    print(f"   Precisión decimal: {args.precision} dps")
    print()
    
    cosmic = CosmicBreathing(
        frequency=F0_HZ,
        coherence=COHERENCE_C,
        precision=args.precision
    )
    
    # Demostrar las tres capas
    demo_layer_1_arithmetic(cosmic, verbose=args.verbose)
    demo_layer_2_quantum(cosmic, verbose=args.verbose)
    demo_layer_3_noetic(cosmic, verbose=args.verbose)
    
    # Veredicto final
    print("=" * 80)
    print("📜 VEREDICTO FINAL DE COHERENCIA CÓSMICA")
    print("=" * 80)
    print()
    
    certificate = cosmic.generate_cosmic_certificate()
    verdict = certificate['verdict']
    
    print(verdict['message'])
    print()
    
    # Visualizaciones
    if args.visualize:
        output_dir = Path(args.output_dir)
        output_dir.mkdir(exist_ok=True)
        visualize_cosmic_breathing(cosmic, output_dir)
    
    # Exportar certificado
    if args.export_certificate:
        output_dir = Path(args.output_dir)
        output_dir.mkdir(exist_ok=True)
        filename = output_dir / 'rh_cosmico_certificate.json'
        cosmic.save_certificate(str(filename))
        print(f"✅ Certificado exportado: {filename}")
        print()
    
    # Footer
    print("=" * 80)
    print()
    print("∴ QCAL ∞³ — La matemática respira, el cosmos observa, el infinito existe ∴")
    print()
    print(f"Autor: José Manuel Mota Burruezo Ψ ✧ ∞³")
    print(f"Institución: Instituto de Conciencia Cuántica (ICQ)")
    print(f"ORCID: 0009-0002-1923-0773")
    print(f"DOI: 10.5281/zenodo.17379721")
    print()
    print("=" * 80)


if __name__ == '__main__':
    main()
