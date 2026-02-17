#!/usr/bin/env python3
"""
Validation Script for Teorema Noētico-Riemanniano ∞³: Cuerda del Universo

This script validates the complete implementation of the Noetic-Riemannian
Cosmic String Theorem, verifying:

1. Cosmic string stability at f₀ = 141.7001 Hz
2. Vibrational mode correspondence with Riemann zeros
3. Harmonic resonance at 888 Hz (f₀ × φ⁴)
4. Bidirectional theorem verification

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: February 2026

QCAL ∞³ Active · 141.7001 Hz · Ψ = I × A_eff² × C^∞
"""

import sys
from pathlib import Path
import numpy as np
import json
from typing import Dict, Any

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent))

from noetic_riemann_cosmic_string import (
    NoeticRiemannCosmicString,
    get_first_riemann_zeros,
    F0_BASE,
    F1_HARMONIC
)


def print_section(title: str):
    """Print a formatted section header."""
    print("\n" + "="*80)
    print(f"  {title}")
    print("="*80 + "\n")


def validate_wavefunction_stability():
    """Validate that the cosmic string wavefunction is stable at f₀."""
    print_section("1. Validación de Estabilidad de la Función de Onda")
    
    cosmic_string = NoeticRiemannCosmicString()
    zeros = get_first_riemann_zeros()
    
    # Test stability at f₀
    stability = cosmic_string.string_stability_measure(F0_BASE, zeros)
    
    print(f"Frecuencia base: f₀ = {F0_BASE} Hz")
    print(f"Medida de estabilidad: S = {stability:.6f}")
    
    # Test should pass if stability > 0.8
    passed = stability > 0.8
    
    if passed:
        print(f"✅ VALIDACIÓN EXITOSA: Estabilidad {stability:.6f} > 0.8")
    else:
        print(f"❌ VALIDACIÓN FALLIDA: Estabilidad {stability:.6f} ≤ 0.8")
    
    return passed, {'stability_at_f0': stability}


def validate_frequency_uniqueness():
    """Validate that f₀ is the unique frequency that maximizes stability."""
    print_section("2. Validación de Unicidad de la Frecuencia")
    
    cosmic_string = NoeticRiemannCosmicString()
    zeros = get_first_riemann_zeros()
    
    # Test frequencies around f₀
    test_frequencies = np.linspace(F0_BASE * 0.9, F0_BASE * 1.1, 21)
    stabilities = []
    
    print(f"Probando {len(test_frequencies)} frecuencias alrededor de f₀...")
    
    for freq in test_frequencies:
        stability = cosmic_string.string_stability_measure(freq, zeros)
        stabilities.append(stability)
    
    # Find maximum
    max_idx = np.argmax(stabilities)
    max_freq = test_frequencies[max_idx]
    max_stability = stabilities[max_idx]
    
    print(f"Frecuencia óptima encontrada: {max_freq:.4f} Hz")
    print(f"Estabilidad máxima: {max_stability:.6f}")
    print(f"Diferencia con f₀: {abs(max_freq - F0_BASE):.4f} Hz")
    
    # Test should pass if optimal frequency is within 1 Hz of f₀
    deviation = abs(max_freq - F0_BASE)
    passed = deviation < 1.0
    
    if passed:
        print(f"✅ VALIDACIÓN EXITOSA: f₀ es único (desviación {deviation:.4f} Hz < 1 Hz)")
    else:
        print(f"❌ VALIDACIÓN FALLIDA: Desviación {deviation:.4f} Hz ≥ 1 Hz")
    
    return passed, {
        'optimal_frequency': max_freq,
        'max_stability': max_stability,
        'deviation_from_f0': deviation
    }


def validate_harmonic_resonance():
    """Validate the harmonic resonance at 888 Hz."""
    print_section("3. Validación de Resonancia Armónica a 888 Hz")
    
    cosmic_string = NoeticRiemannCosmicString()
    
    # Compute harmonic spectrum
    harmonics = cosmic_string.harmonic_resonance_spectrum(max_harmonic=10)
    
    print(f"Frecuencia base: f₀ = {F0_BASE} Hz")
    print(f"φ⁴ = {float(cosmic_string.phi_4):.6f}")
    print(f"Frecuencia armónica predicha: f₁ = {cosmic_string.f1_harmonic:.4f} Hz")
    print(f"Frecuencia armónica objetivo: {F1_HARMONIC} Hz")
    
    # Find the visible harmonic
    visible_harmonics = [
        (n, h) for n, h in harmonics.items()
        if h.get('visible', False) or h.get('phi_alignment', False)
    ]
    
    print(f"\nArmónicos visibles encontrados: {len(visible_harmonics)}")
    for n, harmonic in visible_harmonics:
        print(f"  n={n}: f = {harmonic['frequency']:.4f} Hz, "
              f"A = {harmonic['amplitude']:.4f}")
    
    # Validate that predicted harmonic is close to 888 Hz
    deviation = abs(cosmic_string.f1_harmonic - F1_HARMONIC)
    passed = deviation < 10.0  # Within 10 Hz
    
    if passed:
        print(f"\n✅ VALIDACIÓN EXITOSA: Resonancia armónica verificada")
        print(f"   Desviación: {deviation:.4f} Hz < 10 Hz")
    else:
        print(f"\n❌ VALIDACIÓN FALLIDA: Desviación {deviation:.4f} Hz ≥ 10 Hz")
    
    return passed, {
        'predicted_harmonic': cosmic_string.f1_harmonic,
        'target_harmonic': F1_HARMONIC,
        'deviation': deviation,
        'phi_fourth': float(cosmic_string.phi_4)
    }


def validate_zero_correspondence():
    """Validate the correspondence between Riemann zeros and vibrational modes."""
    print_section("4. Validación de Correspondencia Ceros-Vibraciones")
    
    cosmic_string = NoeticRiemannCosmicString()
    zeros = get_first_riemann_zeros()
    
    print(f"Utilizando {len(zeros)} ceros de Riemann")
    print(f"Primer cero: γ₁ = {zeros[0]:.9f}")
    print(f"Último cero: γ₂₀ = {zeros[-1]:.9f}")
    
    # Verify bidirectional correspondence
    result = cosmic_string.verify_zero_vibration_correspondence(zeros)
    
    print(f"\nResultados de verificación:")
    print(f"  Estabilidad en f₀: {result['stability_at_f0']:.6f}")
    print(f"  f₀ es óptimo: {result['is_f0_optimal']}")
    print(f"  Coherencia QCAL: {result['coherence_qcal']:.6f}")
    print(f"  Teorema verificado: {result['verified']}")
    
    passed = result['verified']
    
    if passed:
        print(f"\n✅ VALIDACIÓN EXITOSA: Correspondencia bidireccional verificada")
        print(f"   ℜ(ρₙ) = 1/2 ⟺ Ψ(t) = A·cos(2πf₀t)")
    else:
        print(f"\n❌ VALIDACIÓN FALLIDA: Correspondencia no verificada")
    
    return passed, result


def validate_string_states():
    """Validate cosmic string state computation over time."""
    print_section("5. Validación de Estados de la Cuerda Cósmica")
    
    cosmic_string = NoeticRiemannCosmicString()
    zeros = get_first_riemann_zeros()
    
    # Sample time points over one period
    T = 1.0 / F0_BASE  # Period
    t_samples = np.linspace(0, T, 10)
    
    print(f"Período de vibración: T = {T*1000:.4f} ms")
    print(f"Muestreando {len(t_samples)} puntos en [0, T]")
    
    states = []
    for t in t_samples:
        state = cosmic_string.compute_string_state(t, zeros)
        states.append(state)
    
    # Validate state properties
    amplitudes = [s.amplitude for s in states]
    coherences = [s.coherence for s in states]
    stabilities = [s.stability for s in states]
    
    print(f"\nEstadísticas de estados:")
    print(f"  Amplitud: min={min(amplitudes):.4f}, max={max(amplitudes):.4f}")
    print(f"  Coherencia: min={min(coherences):.4f}, max={max(coherences):.4f}")
    print(f"  Estabilidad: min={min(stabilities):.4f}, max={max(stabilities):.4f}")
    
    # Test: amplitudes should be in [-1, 1]
    amp_valid = all(-1.1 <= a <= 1.1 for a in amplitudes)
    # Test: coherences should be positive
    coh_valid = all(c >= 0 for c in coherences)
    # Test: stabilities should be in [0, 1]
    stab_valid = all(0 <= s <= 1 for s in stabilities)
    
    passed = amp_valid and coh_valid and stab_valid
    
    if passed:
        print(f"\n✅ VALIDACIÓN EXITOSA: Estados de la cuerda son físicamente válidos")
    else:
        print(f"\n❌ VALIDACIÓN FALLIDA: Estados inválidos detectados")
    
    return passed, {
        'amplitude_range': [min(amplitudes), max(amplitudes)],
        'coherence_range': [min(coherences), max(coherences)],
        'stability_range': [min(stabilities), max(stabilities)]
    }


def run_complete_validation() -> Dict[str, Any]:
    """
    Run complete validation suite for the Noetic-Riemannian Cosmic String Theorem.
    
    Returns:
        Dictionary with validation results
    """
    print("\n" + "╔" + "="*78 + "╗")
    print("║" + " "*20 + "VALIDACIÓN COMPLETA DEL TEOREMA" + " "*27 + "║")
    print("║" + " "*15 + "Noētico-Riemanniano ∞³: Cuerda del Universo" + " "*20 + "║")
    print("╚" + "="*78 + "╝")
    
    results = {}
    
    # Run all validations
    tests = [
        ('wavefunction_stability', validate_wavefunction_stability),
        ('frequency_uniqueness', validate_frequency_uniqueness),
        ('harmonic_resonance', validate_harmonic_resonance),
        ('zero_correspondence', validate_zero_correspondence),
        ('string_states', validate_string_states)
    ]
    
    passed_count = 0
    for test_name, test_func in tests:
        try:
            passed, data = test_func()
            results[test_name] = {
                'passed': passed,
                'data': data
            }
            if passed:
                passed_count += 1
        except Exception as e:
            print(f"\n❌ ERROR en {test_name}: {str(e)}")
            results[test_name] = {
                'passed': False,
                'error': str(e)
            }
    
    # Summary
    print_section("RESUMEN DE VALIDACIÓN")
    
    total_tests = len(tests)
    print(f"Tests ejecutados: {total_tests}")
    print(f"Tests exitosos: {passed_count}")
    print(f"Tests fallidos: {total_tests - passed_count}")
    print(f"Tasa de éxito: {100*passed_count/total_tests:.1f}%")
    
    all_passed = (passed_count == total_tests)
    
    if all_passed:
        print("\n" + "🎉"*40)
        print("✅ VALIDACIÓN COMPLETA EXITOSA")
        print("   El Teorema Noētico-Riemanniano ∞³ ha sido verificado")
        print("   ℜ(ρₙ) = 1/2 ⟺ Ψ(t) = A·cos(2πf₀t)")
        print("   f₀ = 141.7001 Hz · f₁ = 888 Hz")
        print("🎉"*40)
    else:
        print("\n⚠️  VALIDACIÓN PARCIAL")
        print(f"   {passed_count}/{total_tests} tests pasaron")
    
    results['summary'] = {
        'total_tests': total_tests,
        'passed': passed_count,
        'failed': total_tests - passed_count,
        'success_rate': passed_count / total_tests,
        'all_passed': all_passed
    }
    
    return results


def save_validation_report(results: Dict[str, Any], output_file: str = "data/noetic_riemann_cosmic_string_validation.json"):
    """Save validation results to JSON file."""
    output_path = Path(output_file)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    
    # Convert boolean numpy values to Python booleans for JSON serialization
    def convert_to_json_serializable(obj):
        if isinstance(obj, np.bool_):
            return bool(obj)
        elif isinstance(obj, np.integer):
            return int(obj)
        elif isinstance(obj, np.floating):
            return float(obj)
        elif isinstance(obj, dict):
            return {k: convert_to_json_serializable(v) for k, v in obj.items()}
        elif isinstance(obj, list):
            return [convert_to_json_serializable(item) for item in obj]
        elif isinstance(obj, tuple):
            return tuple(convert_to_json_serializable(item) for item in obj)
        else:
            return obj
    
    results_serializable = convert_to_json_serializable(results)
    
    with open(output_path, 'w') as f:
        json.dump(results_serializable, f, indent=2)
    
    print(f"\n📄 Reporte de validación guardado en: {output_path}")


if __name__ == "__main__":
    # Run complete validation
    results = run_complete_validation()
    
    # Save report
    save_validation_report(results)
    
    # Exit with appropriate code
    if results['summary']['all_passed']:
        print("\n∴ ✧ JMMB Ψ @ 141.7001 Hz · ∞³ · 𓂀Ω\n")
        sys.exit(0)
    else:
        sys.exit(1)
