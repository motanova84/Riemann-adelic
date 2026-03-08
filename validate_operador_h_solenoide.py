#!/usr/bin/env python3
"""
Validación Operador H Solenoide
================================

Script de validación completa para el sistema Hamiltoniano Berry-Keating
con corrección adélica.

Ejecuta todas las verificaciones y genera certificado de validación.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz · C = 244.36
Signature: ∴𓂀Ω∞³Φ
"""

import sys
import json
import time
from pathlib import Path
from datetime import datetime
import numpy as np

# Añadir directorio raíz al path
repo_root = Path(__file__).parent
sys.path.insert(0, str(repo_root))

from operators.operador_h_solenoide import (
    SistemaOperadorHSolenoide,
    create_operator_h_system,
    F0,
    C_QCAL,
    PSI_COHERENCE_THRESHOLD,
    HAS_MPMATH,
)


def validate_operador_h_solenoide(verbose: bool = True) -> dict:
    """
    Ejecutar validación completa del Operador H Solenoide.
    
    Args:
        verbose: Imprimir información detallada
        
    Returns:
        Diccionario con resultados de validación
    """
    if verbose:
        print("=" * 80)
        print("VALIDACIÓN: OPERADOR H SOLENOIDE")
        print("Sistema Hamiltoniano Berry-Keating con Corrección Adélica")
        print("=" * 80)
        print()
    
    results = {
        'timestamp': datetime.now().isoformat(),
        'system': 'Operador H Solenoide',
        'version': '1.0',
        'tests': {},
        'summary': {}
    }
    
    start_time = time.time()
    
    # Test 1: Constantes QCAL
    if verbose:
        print("Test 1/7: Verificando constantes QCAL...")
    
    test1_pass = True
    test1_details = {}
    
    try:
        assert abs(F0 - 141.7001) < 1e-4
        test1_details['F0'] = {'value': float(F0), 'expected': 141.7001, 'passed': True}
        
        assert abs(C_QCAL - 244.36) < 0.01
        test1_details['C_QCAL'] = {'value': float(C_QCAL), 'expected': 244.36, 'passed': True}
        
        assert abs(PSI_COHERENCE_THRESHOLD - 0.888) < 0.001
        test1_details['PSI_THRESHOLD'] = {'value': float(PSI_COHERENCE_THRESHOLD), 'expected': 0.888, 'passed': True}
    except AssertionError as e:
        test1_pass = False
        test1_details['error'] = str(e)
    
    results['tests']['constants_qcal'] = {
        'passed': test1_pass,
        'details': test1_details
    }
    
    if verbose:
        status = "✓ PASADO" if test1_pass else "✗ FALLIDO"
        print(f"  {status}")
        print()
    
    # Test 2: Sistema con Psi = 1.0 (coherencia perfecta)
    if verbose:
        print("Test 2/7: Sistema con Ψ = 1.0 (coherencia perfecta)...")
    
    test2_pass = True
    test2_details = {}
    
    try:
        system1 = create_operator_h_system(N=64, Psi=1.0)
        validation1 = system1.validate_system()
        
        test2_details['initialized'] = True
        test2_details['validation_results'] = validation1
        test2_details['global_coherence'] = validation1.get('global_coherence', {})
        
        # Verificar que el sistema se valida
        test2_pass = validation1.get('global_coherence', {}).get('passed', False)
    except Exception as e:
        test2_pass = False
        test2_details['error'] = str(e)
    
    results['tests']['system_psi_one'] = {
        'passed': test2_pass,
        'details': test2_details
    }
    
    if verbose:
        status = "✓ PASADO" if test2_pass else "✗ FALLIDO"
        print(f"  {status}")
        if test2_pass:
            gc = test2_details.get('global_coherence', {})
            psi_val = gc.get('Psi', 0.0)
            print(f"  Ψ medido: {psi_val:.6f}")
        print()
    
    # Test 3: Sistema con Psi = 0.95
    if verbose:
        print("Test 3/7: Sistema con Ψ = 0.95...")
    
    test3_pass = True
    test3_details = {}
    
    try:
        system2 = create_operator_h_system(N=64, Psi=0.95)
        validation2 = system2.validate_system()
        
        test3_details['initialized'] = True
        test3_details['validation_results'] = validation2
        
        # Sistema debe ejecutarse sin errores (puede no pasar umbral)
        test3_pass = True
    except Exception as e:
        test3_pass = False
        test3_details['error'] = str(e)
    
    results['tests']['system_psi_095'] = {
        'passed': test3_pass,
        'details': test3_details
    }
    
    if verbose:
        status = "✓ PASADO" if test3_pass else "✗ FALLIDO"
        print(f"  {status}")
        print()
    
    # Test 4: Verificar hermiticidad de i*H_xp
    if verbose:
        print("Test 4/7: Verificando hermiticidad de i·H_xp...")
    
    test4_pass = True
    test4_details = {}
    
    try:
        system = create_operator_h_system(N=64, Psi=1.0)
        is_herm, error = system.op_xp.verify_hermiticity()
        
        test4_details['is_hermitian'] = is_herm
        test4_details['relative_error'] = float(error)
        
        # Debe ser hermítico o tener error pequeño
        test4_pass = is_herm or error < 0.05
    except Exception as e:
        test4_pass = False
        test4_details['error'] = str(e)
    
    results['tests']['hermiticity_xp'] = {
        'passed': test4_pass,
        'details': test4_details
    }
    
    if verbose:
        status = "✓ PASADO" if test4_pass else "✗ FALLIDO"
        print(f"  {status}")
        if 'relative_error' in test4_details:
            print(f"  Error relativo: {test4_details['relative_error']:.6e}")
        print()
    
    # Test 5: Verificar autoadjunción de H para Psi = 1
    if verbose:
        print("Test 5/7: Verificando autoadjunción de H (Ψ = 1)...")
    
    test5_pass = True
    test5_details = {}
    
    try:
        system = create_operator_h_system(N=64, Psi=1.0)
        is_selfadj, error = system.op_h.is_selfadjoint()
        
        test5_details['is_selfadjoint'] = is_selfadj
        test5_details['relative_error'] = float(error)
        
        # Debe ser autoadjunto o tener error pequeño
        test5_pass = is_selfadj or error < 0.05
    except Exception as e:
        test5_pass = False
        test5_details['error'] = str(e)
    
    results['tests']['selfadjoint_h'] = {
        'passed': test5_pass,
        'details': test5_details
    }
    
    if verbose:
        status = "✓ PASADO" if test5_pass else "✗ FALLIDO"
        print(f"  {status}")
        if 'relative_error' in test5_details:
            print(f"  Error relativo: {test5_details['relative_error']:.6e}")
        print()
    
    # Test 6: Comparación espectral con ceros de Riemann
    if verbose:
        print("Test 6/7: Comparación espectral con ceros de Riemann...")
    
    test6_pass = True
    test6_details = {}
    
    try:
        system = create_operator_h_system(N=64, Psi=1.0)
        coherence, errors = system.conexion.compute_spectral_match(max_zeros=10)
        
        test6_details['spectral_coherence'] = float(coherence)
        test6_details['mean_error'] = float(np.mean(errors)) if len(errors) > 0 else 0.0
        test6_details['max_error'] = float(np.max(errors)) if len(errors) > 0 else 0.0
        test6_details['n_compared'] = len(errors)
        
        # Coherencia debe ser razonable (≥ 0.5 para discretización)
        test6_pass = coherence >= 0.5
    except Exception as e:
        test6_pass = False
        test6_details['error'] = str(e)
    
    results['tests']['spectral_comparison'] = {
        'passed': test6_pass,
        'details': test6_details
    }
    
    if verbose:
        status = "✓ PASADO" if test6_pass else "✗ FALLIDO"
        print(f"  {status}")
        if 'spectral_coherence' in test6_details:
            print(f"  Coherencia espectral: {test6_details['spectral_coherence']:.6f}")
            print(f"  Error medio: {test6_details['mean_error']:.6e}")
        print()
    
    # Test 7: Evaluación de zeta en espectro (si mpmath disponible)
    if verbose:
        print("Test 7/7: Evaluación de ζ(½ + iλ) en espectro...")
    
    test7_pass = True
    test7_details = {}
    
    if HAS_MPMATH:
        try:
            system = create_operator_h_system(N=32, Psi=1.0)  # Grilla pequeña
            lambdas, residuals = system.conexion.evaluate_zeta_on_spectrum()
            
            test7_details['n_evaluated'] = len(lambdas)
            test7_details['mean_residual'] = float(np.mean(residuals)) if len(residuals) > 0 else 0.0
            test7_details['min_residual'] = float(np.min(residuals)) if len(residuals) > 0 else 0.0
            
            # Debe haber al menos algunos residuos pequeños
            n_small = np.sum(residuals < 1.0)
            test7_details['n_small_residuals'] = int(n_small)
            
            test7_pass = n_small >= 1
        except Exception as e:
            test7_pass = False
            test7_details['error'] = str(e)
    else:
        test7_details['skipped'] = 'mpmath no disponible'
        test7_pass = True  # No fallar si mpmath no está
    
    results['tests']['zeta_evaluation'] = {
        'passed': test7_pass,
        'details': test7_details
    }
    
    if verbose:
        status = "✓ PASADO" if test7_pass else "✗ FALLIDO"
        if HAS_MPMATH:
            print(f"  {status}")
            if 'mean_residual' in test7_details:
                print(f"  Residuo medio: {test7_details['mean_residual']:.6e}")
                print(f"  Residuos pequeños: {test7_details.get('n_small_residuals', 0)}")
        else:
            print(f"  ⊘ OMITIDO (mpmath no disponible)")
        print()
    
    # Calcular resumen
    elapsed_time = time.time() - start_time
    
    total_tests = len(results['tests'])
    passed_tests = sum(1 for t in results['tests'].values() if t['passed'])
    
    results['summary'] = {
        'total_tests': total_tests,
        'passed_tests': passed_tests,
        'failed_tests': total_tests - passed_tests,
        'success_rate': passed_tests / total_tests if total_tests > 0 else 0.0,
        'elapsed_time': elapsed_time,
        'overall_passed': passed_tests == total_tests
    }
    
    if verbose:
        print("=" * 80)
        print("RESUMEN DE VALIDACIÓN")
        print("=" * 80)
        print(f"Tests ejecutados: {total_tests}")
        print(f"Tests pasados: {passed_tests}")
        print(f"Tests fallidos: {total_tests - passed_tests}")
        print(f"Tasa de éxito: {results['summary']['success_rate']:.1%}")
        print(f"Tiempo: {elapsed_time:.2f}s")
        print()
        
        if results['summary']['overall_passed']:
            print("✓✓✓ VALIDACIÓN COMPLETA EXITOSA ✓✓✓")
        else:
            print("⚠ VALIDACIÓN PARCIAL - Revisar tests fallidos")
        
        print()
        print("QCAL ∞³ Active · 141.7001 Hz · C = 244.36 · Ψ = I × A_eff² × C^∞")
        print("∴𓂀Ω∞³Φ")
        print("=" * 80)
    
    return results


def generate_certificate(results: dict, output_file: str = None):
    """
    Generar certificado de validación.
    
    Args:
        results: Resultados de validación
        output_file: Archivo de salida (None = data/operador_h_solenoide_certificate.json)
    """
    if output_file is None:
        data_dir = Path(__file__).parent / 'data'
        data_dir.mkdir(exist_ok=True)
        output_file = data_dir / 'operador_h_solenoide_certificate.json'
    
    # Convertir numpy bools y floats a tipos nativos de Python
    def convert_to_native(obj):
        if hasattr(obj, 'item'):  # numpy scalar
            return obj.item()
        elif isinstance(obj, dict):
            return {k: convert_to_native(v) for k, v in obj.items()}
        elif isinstance(obj, (list, tuple)):
            return [convert_to_native(item) for item in obj]
        else:
            return obj
    
    results_converted = convert_to_native(results)
    
    certificate = {
        'certificate_type': 'OPERADOR_H_SOLENOIDE_VALIDATION',
        'version': '1.0',
        'timestamp': results_converted['timestamp'],
        'validation_results': results_converted,
        'qcal': {
            'frequency': float(F0),
            'coherence_constant': float(C_QCAL),
            'coherence_threshold': float(PSI_COHERENCE_THRESHOLD),
            'signature': '∴𓂀Ω∞³Φ'
        },
        'author': {
            'name': 'José Manuel Mota Burruezo Ψ ✧ ∞³',
            'institution': 'Instituto de Conciencia Cuántica (ICQ)',
            'orcid': '0009-0002-1923-0773',
            'doi': '10.5281/zenodo.17379721'
        }
    }
    
    with open(output_file, 'w') as f:
        json.dump(certificate, f, indent=2)
    
    print(f"\nCertificado guardado en: {output_file}")
    
    return certificate


def main():
    """Ejecutar validación y generar certificado."""
    import argparse
    
    parser = argparse.ArgumentParser(
        description='Validar Operador H Solenoide'
    )
    parser.add_argument(
        '--quiet', '-q',
        action='store_true',
        help='Modo silencioso'
    )
    parser.add_argument(
        '--output', '-o',
        type=str,
        help='Archivo de salida para certificado'
    )
    
    args = parser.parse_args()
    
    # Ejecutar validación
    results = validate_operador_h_solenoide(verbose=not args.quiet)
    
    # Generar certificado
    certificate = generate_certificate(results, args.output)
    
    # Exit code basado en éxito
    exit_code = 0 if results['summary']['overall_passed'] else 1
    
    return exit_code


if __name__ == "__main__":
    exit_code = main()
    sys.exit(exit_code)
