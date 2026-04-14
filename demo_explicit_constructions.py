#!/usr/bin/env python3
"""
Demo script showing the explicit GL(1) construction and spectral operators
integrated with the existing Riemann Hypothesis validation framework.
"""

import sys
import numpy as np
import matplotlib.pyplot as plt
from foundational_gl1 import ExplicitGL1Construction
from spectral_operators import ExplicitTraceClassOperator, AdelicSpectralConstruction

# Import existing validation utilities
try:
    from validate_explicit_formula import simulate_delta_s
    from utils.mellin import truncated_gaussian, f1, f2
    VALIDATION_AVAILABLE = True
except ImportError:
    print("Warning: Existing validation modules not available")
    VALIDATION_AVAILABLE = False

def demo_gl1_explicit_construction():
    """
    Demonstrate the explicit GL(1) construction without assuming ζ(s).
    """
    print("🎯 DEMO: Construcción Explícita GL(1)")
    print("=" * 50)
    
    # Create GL(1) constructor
    gl1_constructor = ExplicitGL1Construction()
    
    # Test with different values of s
    s_values = [1.5, 2.0, 2.5, 3.0, 4.0]
    traces = []
    
    print("Calculando trazas explícitas para diferentes valores de s:")
    for s in s_values:
        trace = gl1_constructor.verify_trace_identity_gl1(s)
        traces.append(trace)
        print(f"s = {s}: traza = {trace:.6f}")
        print("-" * 30)
    
    # Plot the results
    plt.figure(figsize=(10, 6))
    plt.plot(s_values, traces, 'bo-', linewidth=2, markersize=8)
    plt.xlabel('s')
    plt.ylabel('Traza GL(1) explícita')
    plt.title('Comportamiento de la traza GL(1) explícita')
    plt.grid(True, alpha=0.3)
    plt.savefig('gl1_explicit_traces.png', dpi=150, bbox_inches='tight')
    # plt.show()  # Disabled for headless environment
    
    return s_values, traces

def demo_spectral_operators():
    """
    Demonstrate explicit construction of trace class operators.
    """
    print("\n🔬 DEMO: Operadores Espectrales Explícitos")
    print("=" * 50)
    
    # Create spectral operator
    operator = ExplicitTraceClassOperator(dimension=100)
    primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
    weights = [1.0 / (1 + 0.1 * i) for i in range(len(primes))]
    
    # Build the explicit operator
    print("Construyendo operador explícito...")
    matrix = operator.build_explicit_operator(primes, weights)
    
    # Compute properties
    trace = operator.compute_explicit_trace()
    eigenvalues = operator.compute_eigenvalues_explicit()
    is_trace_class, nuclear_norm = operator.verify_trace_class_property()
    
    print(f"Traza del operador: {trace:.6f}")
    print(f"Norma nuclear: {nuclear_norm:.6f}")
    print(f"¿Es de clase traza?: {is_trace_class}")
    print(f"Rango espectral: [{np.min(eigenvalues):.4f}, {np.max(eigenvalues):.4f}]")
    
    # Plot spectral density
    bin_centers, hist = operator.explicit_spectral_density()
    
    plt.figure(figsize=(10, 6))
    plt.bar(bin_centers, hist, width=np.diff(bin_centers)[0]*0.8, alpha=0.7)
    plt.xlabel('Valor propio')
    plt.ylabel('Densidad espectral')
    plt.title('Densidad espectral del operador explícito')
    plt.grid(True, alpha=0.3)
    plt.savefig('spectral_density.png', dpi=150, bbox_inches='tight')
    # plt.show()  # Disabled for headless environment
    
    return operator, eigenvalues

def demo_adelic_construction():
    """
    Demonstrate the adelic spectral construction.
    """
    print("\n🌐 DEMO: Construcción Espectral Adélica")
    print("=" * 50)
    
    # Setup adelic construction
    primes = [2, 3, 5, 7, 11]
    arch_data = np.pi / 2  # Archimedean contribution
    
    adelic_constructor = AdelicSpectralConstruction(primes, arch_data)
    
    # Build local operators
    print("Construyendo operadores locales...")
    local_operators = adelic_constructor.build_local_operators()
    
    # Compute global trace formula
    print("Calculando fórmula de trazas global...")
    global_trace, local_traces = adelic_constructor.compute_global_trace_formula()
    
    print(f"\nResultados de la construcción adélica:")
    print(f"Traza global: {global_trace:.6f}")
    print("Trazas locales por primo:")
    for p, trace in local_traces.items():
        print(f"  Primo {p}: {trace:.6f}")
    
    return adelic_constructor, global_trace, local_traces

def demo_connection_to_existing_validation():
    """
    Show how the new constructions connect to existing validation.
    """
    if not VALIDATION_AVAILABLE:
        print("\n⚠️  Validación existente no disponible")
        return
    
    print("\n🔗 DEMO: Conexión con Validación Existente")
    print("=" * 50)
    
    # Use existing validation to generate some eigenvalues
    try:
        eigenvalues, imaginary_parts, _ = simulate_delta_s(50, precision=15)
        print(f"Valores propios simulados: {len(eigenvalues)}")
        print(f"Partes imaginarias derivadas: {len(imaginary_parts)}")
        
        # Compare with our explicit construction
        operator = ExplicitTraceClassOperator(dimension=50)
        primes = [2, 3, 5, 7, 11]
        weights = [1.0, 0.8, 0.6, 0.4, 0.2]
        
        operator.build_explicit_operator(primes, weights)
        our_eigenvalues = operator.compute_eigenvalues_explicit()
        
        # Plot comparison
        plt.figure(figsize=(12, 5))
        
        plt.subplot(1, 2, 1)
        plt.hist(eigenvalues, bins=20, alpha=0.7, label='Simulación existente')
        plt.xlabel('Valor propio')
        plt.ylabel('Frecuencia')
        plt.title('Eigenvalores: Simulación existente')
        plt.legend()
        
        plt.subplot(1, 2, 2)
        plt.hist(our_eigenvalues, bins=20, alpha=0.7, label='Construcción explícita', color='orange')
        plt.xlabel('Valor propio')
        plt.ylabel('Frecuencia')
        plt.title('Eigenvalores: Construcción explícita')
        plt.legend()
        
        plt.tight_layout()
        plt.savefig('eigenvalue_comparison.png', dpi=150, bbox_inches='tight')
        # plt.show()  # Disabled for headless environment
        
        print("Comparación de eigenvalores guardada en eigenvalue_comparison.png")
        
    except Exception as e:
        print(f"Error en la conexión con validación existente: {e}")

def main():
    """
    Main demonstration function.
    """
    print("🚀 DEMO COMPLETO: Construcciones Explícitas para RH")
    print("=" * 60)
    print("Este demo muestra las construcciones explícitas implementadas")
    print("sin asumir la función zeta de Riemann de manera circular.")
    print("=" * 60)
    
    # Run all demonstrations
    s_values, traces = demo_gl1_explicit_construction()
    operator, eigenvalues = demo_spectral_operators()
    adelic_constructor, global_trace, local_traces = demo_adelic_construction()
    demo_connection_to_existing_validation()
    
    # Summary
    print("\n📊 RESUMEN DE RESULTADOS")
    print("=" * 50)
    print(f"✅ GL(1) trazas calculadas para {len(s_values)} valores de s")
    print(f"✅ Operador espectral con {len(eigenvalues)} eigenvalores")
    print(f"✅ Construcción adélica con traza global {global_trace:.3e}")
    print(f"✅ {len(local_traces)} operadores locales construidos")
    
    print("\n🎯 Las construcciones son EXPLÍCITAS y no circulares!")
    print("🔬 Todos los cálculos están basados en primeros principios.")
    print("📈 Los gráficos se han guardado como archivos PNG.")

if __name__ == "__main__":
    main()