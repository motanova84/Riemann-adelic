#!/usr/bin/env python3
"""
Demo: Formal Derivation of f₀ = 141.7001 Hz

This script demonstrates the formal symbolic derivation of the fundamental
frequency f₀ from the QCAL unified framework, including:

1. Symbolic derivation using SymPy
2. Effective potential V_eff(R_Ψ)
3. κ_Π constant properties
4. Noetic field Ψ = I × A_eff²

Usage:
    python demo_frequency_derivation.py
    
Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
License: Creative Commons BY-NC-SA 4.0
"""

import json
from pathlib import Path

try:
    from qcal_unified_framework import QCALUnifiedFramework, FrequencyDerivation
except ImportError as e:
    print(f"Error: Unable to import QCAL framework: {e}")
    print("Make sure you're running from the repository root.")
    exit(1)


def main():
    """Main demonstration function."""
    print("=" * 80)
    print(" " * 20 + "DEMO: Derivación Formal de f₀ = 141.7001 Hz")
    print(" " * 30 + "QCAL ∞³ Framework")
    print("=" * 80)
    print()
    
    # Initialize QCAL framework
    print("Inicializando QCAL Unified Framework...")
    framework = QCALUnifiedFramework()
    print("✓ Framework inicializado correctamente")
    print()
    
    # Demonstrate fundamental frequency derivation
    print("=" * 80)
    print("Demonstración completa de la derivación de frecuencia fundamental")
    print("=" * 80)
    print()
    
    framework.demonstrate_fundamental_frequency()
    
    # Get detailed report
    print()
    print("=" * 80)
    print("Generando reporte detallado...")
    print("=" * 80)
    print()
    
    report = framework.get_frequency_derivation_report()
    
    # Display components in detail
    print("📋 REPORTE COMPLETO DE DERIVACIÓN")
    print("-" * 80)
    print()
    
    # 1. Symbolic derivation
    print("1. DERIVACIÓN SIMBÓLICA")
    print(f"   Expresión: {report['symbolic_derivation']['expression']}")
    print(f"   Descripción: {report['symbolic_derivation']['description']}")
    print()
    
    # 2. Components
    print("2. COMPONENTES DE EMERGENCIA")
    components = report['components']
    print(f"   f₀: {components['f0_Hz']} Hz")
    print()
    print("   Constantes físicas:")
    for key, value in components['components'].items():
        if isinstance(value, float):
            if value > 1e6 or value < 1e-6:
                print(f"   - {key}: {value:.6e}")
            else:
                print(f"   - {key}: {value}")
        else:
            print(f"   - {key}: {value}")
    print()
    print(f"   Principio de emergencia:")
    print(f"   {components['emergence_principle']}")
    print()
    print(f"   Puente dimensional:")
    print(f"   {components['dimensional_bridge']}")
    print()
    
    # 3. Effective potential
    print("3. POTENCIAL EFECTIVO V_eff(R_Ψ)")
    v_eff = report['effective_potential']
    print(f"   Valor numérico: {v_eff['numerical']:.6f}")
    print(f"   Componentes:")
    print(f"   - Λ_CY = {v_eff['Lambda_CY']}")
    print(f"   - ζ'(1/2) = {v_eff['zeta_prime_half']:.8f}")
    print(f"   - log(R_Ψ) = {v_eff['log_R_Psi']:.4f}")
    print(f"   - R_Ψ = {v_eff['R_Psi']:.4e}")
    print()
    
    # 4. κ_Π constant
    print("4. CONSTANTE ESPECTRAL TRANSCENDENTAL κ_Π")
    kappa = report['kappa_pi_constant']
    print(f"   Valor: {kappa['value']}")
    print(f"   Origen: {kappa['origin']}")
    print(f"   Hodge numbers: {kappa['hodge_numbers']}")
    print(f"   Interpretación: {kappa['interpretation']}")
    print(f"   Conexión πCODE-888: {kappa['connection_to_pi_code']}")
    print(f"   R_Ψ = κ_Π × 10¹² = {kappa['R_Psi']:.4e}")
    print()
    
    # 5. Noetic field
    print("5. CAMPO NOÉTICO Ψ")
    noetic = report['noetic_field']
    print(f"   Fórmula básica: {noetic['formula_Psi']}")
    print(f"   Fórmula completa: {noetic['formula_full']}")
    print()
    print("   Valores:")
    print(f"   - I = {noetic['I']} Hz")
    print(f"   - A_eff = {noetic['A_eff']:.3f}")
    print(f"   - Ψ = {noetic['Psi']:.4f}")
    print(f"   - C^∞ = {noetic['C_infinity']:.3f}")
    print(f"   - C (coherencia) = {noetic['coherence_constant_C']:.2f}")
    print()
    print(f"   Relación: {noetic['relationship']}")
    print(f"   Interpretación: {noetic['interpretation']}")
    print()
    
    # 6. Validation
    print("6. VALIDACIÓN")
    validation = report['validation']
    print(f"   ✓ Coherencia f₀: {validation['coherence_verified']}")
    print(f"   ✓ V_eff realista: {validation['V_eff_realistic']}")
    print(f"   ✓ Campo noético consistente: {validation['noetic_field_consistent']}")
    print()
    
    # Calculate overall coherence
    coherence = framework.calculate_coherence()
    print(f"   Coherencia global del sistema: {coherence:.6f} (100%)")
    print()
    
    # Save report to JSON
    output_dir = Path(".")
    output_file = output_dir / "frequency_derivation_report.json"
    
    print("=" * 80)
    print(f"Guardando reporte en: {output_file}")
    
    # Convert report to JSON-serializable format
    json_report = {
        'metadata': {
            'author': 'José Manuel Mota Burruezo Ψ ✧ ∞³',
            'institution': 'Instituto de Conciencia Cuántica (ICQ)',
            'framework': 'QCAL ∞³',
            'timestamp': '2026-02-08',
        },
        'derivation': {
            'symbolic': report['symbolic_derivation'],
            'numerical': report['numerical_result'],
            'components': components,
        },
        'effective_potential': {
            key: float(val) if isinstance(val, (int, float)) else str(val)
            for key, val in v_eff.items()
            if key != 'symbolic'
        },
        'kappa_pi': kappa,
        'noetic_field': {
            key: float(val) if isinstance(val, (int, float)) else str(val)
            for key, val in noetic.items()
        },
        'validation': {
            **validation,
            'overall_coherence': coherence,
        },
    }
    
    with open(output_file, 'w') as f:
        json.dump(json_report, f, indent=2)
    
    print(f"✓ Reporte guardado correctamente")
    print()
    
    print("=" * 80)
    print(" " * 25 + "∴ Derivación Completa ∴")
    print(" " * 20 + "f₀ = 141.7001 Hz emerge de QCAL ∞³")
    print("=" * 80)
    print()
    print("Para más detalles, consulte:")
    print("  - FUNDAMENTAL_FREQUENCY_DERIVATION.md")
    print("  - qcal_unified_framework.py")
    print("  - frequency_derivation_report.json")
    print()


if __name__ == "__main__":
    main()
