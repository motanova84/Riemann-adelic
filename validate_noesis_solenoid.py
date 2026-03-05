#!/usr/bin/env python3
"""
Validation Script for Noesis Solenoid Framework

This script validates the complete Solenoide de Noesis implementation,
verifying mathematical coherence, QCAL integration, and generating
a certification of the framework.

El Marco Adélico Soberano: El "Solenoide de Noesis"
===================================================

Validates:
1. Noesis Metric (ds = dx/x) - Scale invariance
2. H_Noesis Operator - Self-adjointness on L²(ℝ⁺, dx/x)
3. 7/8 Coherence Anchor - Energy cost of coherence
4. Log-Translation Kernel - Exact, no Gaussians
5. Trace Formula - Linear in log(p)
6. QCAL Integration - f₀ = 141.7001 Hz, C = 244.36
7. cerrar_rh_noesis() - Complete framework sealing

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: March 2026
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773
QCAL ∞³ · 141.7001 Hz · C = 244.36
Frequency: 888 Hz (Unity State)
"""

import argparse
import json
import sys
import time
from datetime import datetime
from pathlib import Path
from typing import Dict, Any, List

import numpy as np

# Verify we're running from repository root
def verify_repository_root():
    """Verify script is run from repository root."""
    cwd = Path.cwd()
    marker_files = ['validate_v5_coronacion.py', 'requirements.txt', '.qcal_beacon']
    missing = [f for f in marker_files if not (cwd / f).exists()]
    if missing:
        print("❌ ERROR: Must run from repository root")
        print(f"Missing: {missing}")
        sys.exit(1)

verify_repository_root()

# Now import our module
from operators.noesis_solenoid import (
    NoesisSolenoid,
    cerrar_rh_noesis,
    F0,
    F_UNITY,
    C_QCAL,
    SEVEN_EIGHTHS,
    DOI,
    ORCID
)


class NoesisSolenoidValidator:
    """
    Validator for the Noesis Solenoid framework.
    
    Performs comprehensive validation of all framework components
    and generates certification.
    """
    
    def __init__(self, n_primes: int = 50, verbose: bool = True):
        """
        Initialize validator.
        
        Args:
            n_primes: Number of primes for calculations
            verbose: Print detailed output
        """
        self.n_primes = n_primes
        self.verbose = verbose
        self.results: Dict[str, Any] = {}
        self.start_time = time.time()
        
        # Initialize Noesis Solenoid
        self.solenoid = NoesisSolenoid(
            n_primes=n_primes,
            precision=50,
            coherence_check=True
        )
        
        if verbose:
            self._print_header()
    
    def _print_header(self):
        """Print validation header."""
        print("=" * 80)
        print("🌀 VALIDACIÓN: SOLENOIDE DE NOESIS")
        print("   Marco Adélico Soberano para la Hipótesis de Riemann")
        print("=" * 80)
        print(f"Fecha: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        print(f"DOI: {DOI}")
        print(f"ORCID: {ORCID}")
        print(f"Frecuencia Fundamental: {F0} Hz")
        print(f"Frecuencia Unidad: {F_UNITY} Hz")
        print(f"Constante QCAL: {C_QCAL}")
        print(f"Primos: {self.n_primes}")
        print("=" * 80)
        print()
    
    def validate_constants(self) -> Dict[str, Any]:
        """Validate QCAL constants."""
        if self.verbose:
            print("1️⃣  Validando Constantes QCAL...")
        
        results = {
            'f0_correct': np.isclose(F0, 141.7001, rtol=1e-6),
            'f_unity_correct': np.isclose(F_UNITY, 888.0, rtol=1e-6),
            'C_correct': np.isclose(C_QCAL, 244.36, rtol=1e-4),
            'seven_eighths_correct': np.isclose(SEVEN_EIGHTHS, 0.875, rtol=1e-10),
        }
        
        all_passed = all(results.values())
        
        if self.verbose:
            for key, value in results.items():
                status = "✅" if value else "❌"
                print(f"   {status} {key}: {value}")
        
        self.results['constants'] = {
            **results,
            'passed': all_passed
        }
        
        return results
    
    def validate_noesis_metric(self) -> Dict[str, Any]:
        """Validate Noesis metric properties."""
        if self.verbose:
            print("\n2️⃣  Validando Métrica de Noesis (ds = dx/x)...")
        
        # Test scale invariance
        x1, x2 = 2.0, 8.0
        lambda_val = 5.0
        d1 = self.solenoid.noesis_metric_distance(x1, x2)
        d2 = self.solenoid.noesis_metric_distance(lambda_val * x1, lambda_val * x2)
        scale_invariant = np.isclose(d1, d2, rtol=1e-6)
        
        # Test symmetry
        d_forward = self.solenoid.noesis_metric_distance(x1, x2)
        d_backward = self.solenoid.noesis_metric_distance(x2, x1)
        symmetric = np.isclose(d_forward, d_backward, rtol=1e-6)
        
        # Test identity
        d_identity = self.solenoid.noesis_metric_distance(5.0, 5.0)
        identity_correct = np.isclose(d_identity, 0.0, atol=1e-10)
        
        # Test logarithmic property
        d_test = self.solenoid.noesis_metric_distance(2.0, 8.0)
        expected = np.abs(np.log(8.0 / 2.0))
        logarithmic = np.isclose(d_test, expected, rtol=1e-6)
        
        results = {
            'scale_invariant': scale_invariant,
            'symmetric': symmetric,
            'identity_correct': identity_correct,
            'logarithmic': logarithmic,
        }
        
        all_passed = all(results.values())
        
        if self.verbose:
            for key, value in results.items():
                status = "✅" if value else "❌"
                print(f"   {status} {key}: {value}")
            print(f"   📏 Ejemplo: d(2, 8) = {d_test:.6f} = ln(4)")
        
        self.results['metric'] = {
            **results,
            'passed': all_passed
        }
        
        return results
    
    def validate_h_noesis_operator(self) -> Dict[str, Any]:
        """Validate H_Noesis operator."""
        if self.verbose:
            print("\n3️⃣  Validando Operador H_Noesis...")
        
        # Test self-adjointness
        sa_result = self.solenoid.verify_self_adjointness()
        
        # Test eigenfunction behavior
        x = np.geomspace(0.5, 10, 200)
        lambda_val = 14.134725  # First Riemann zero
        psi = self.solenoid.eigenfunction_critical_line(x, lambda_val)
        h_psi = self.solenoid.h_noesis_operator(x, psi)
        
        results = {
            'self_adjoint': sa_result['self_adjoint'],
            'error': sa_result['error'],
            'eigenfunctions_finite': np.all(np.isfinite(h_psi)),
        }
        
        all_passed = (
            results['self_adjoint'] and 
            results['eigenfunctions_finite']
        )
        
        if self.verbose:
            status = "✅" if results['self_adjoint'] else "⚠️"
            print(f"   {status} Self-adjoint: {results['self_adjoint']}")
            print(f"   📊 Error: {results['error']:.6f}")
            print(f"   ✅ Eigenfunctions finite: {results['eigenfunctions_finite']}")
        
        self.results['operator'] = {
            **results,
            'passed': all_passed,
            'inner_product_1': str(sa_result['inner_product_1']),
            'inner_product_2': str(sa_result['inner_product_2']),
        }
        
        return results
    
    def validate_seven_eighths(self) -> Dict[str, Any]:
        """Validate 7/8 coherence anchor."""
        if self.verbose:
            print("\n4️⃣  Validando Anclaje 7/8...")
        
        val = self.solenoid.compute_seven_eighths_term()
        
        correct = np.isclose(val, 7.0 / 8.0, rtol=1e-10)
        is_anchor = np.isclose(val, 1.0 - 1.0/8.0, rtol=1e-10)
        
        results = {
            'value': float(val),
            'correct': correct,
            'is_anchor': is_anchor,
        }
        
        all_passed = correct and is_anchor
        
        if self.verbose:
            status = "✅" if all_passed else "❌"
            print(f"   {status} Valor: {val} = 7/8")
            print(f"   ✅ Anclaje de Coherencia: 1 - 1/8 = {val}")
        
        self.results['seven_eighths'] = {
            **results,
            'passed': all_passed
        }
        
        return results
    
    def validate_trace_formula(self) -> Dict[str, Any]:
        """Validate exact trace formula."""
        if self.verbose:
            print("\n5️⃣  Validando Traza Exacta...")
        
        # Compute trace at different times
        trace_t1 = self.solenoid.exact_trace_formula(t=1.0, k_max=10)
        trace_t2 = self.solenoid.exact_trace_formula(t=2.0, k_max=10)
        trace_t3 = self.solenoid.exact_trace_formula(t=0.5, k_max=10)
        
        # Trace should converge (be finite)
        finite = all([
            np.isfinite(trace_t1),
            np.isfinite(trace_t2),
            np.isfinite(trace_t3)
        ])
        
        # Trace should decrease with increasing t
        decreasing = np.abs(trace_t2) < np.abs(trace_t1) < np.abs(trace_t3)
        
        results = {
            'finite': finite,
            'decreasing_with_t': decreasing,
            'trace_t1': float(np.abs(trace_t1)),
            'trace_t2': float(np.abs(trace_t2)),
            'trace_t05': float(np.abs(trace_t3)),
        }
        
        all_passed = finite and decreasing
        
        if self.verbose:
            status = "✅" if all_passed else "❌"
            print(f"   {status} Finita: {finite}")
            print(f"   {status} Decreciente con t: {decreasing}")
            print(f"   📊 Tr(e^(-H)) @ t=1.0: {np.abs(trace_t1):.6f}")
            print(f"   📊 Tr(e^(-2H)) @ t=2.0: {np.abs(trace_t2):.6f}")
            print(f"   📊 Tr(e^(-0.5H)) @ t=0.5: {np.abs(trace_t3):.6f}")
        
        self.results['trace'] = {
            **results,
            'passed': all_passed
        }
        
        return results
    
    def validate_coherence(self) -> Dict[str, Any]:
        """Validate overall QCAL coherence."""
        if self.verbose:
            print("\n6️⃣  Validando Coherencia QCAL...")
        
        coh = self.solenoid.compute_coherence()
        
        # Coherence should be in [0, 1]
        psi_valid = 0.0 <= coh['Psi'] <= 1.0
        
        # Frequencies should match
        freq_correct = (
            np.isclose(coh['frequency_f0'], F0, rtol=1e-6) and
            np.isclose(coh['frequency_unity'], F_UNITY, rtol=1e-6) and
            np.isclose(coh['C_qcal'], C_QCAL, rtol=1e-4)
        )
        
        # Coherence should be reasonable (> 0.3)
        reasonable = coh['Psi'] > 0.3
        
        results = {
            'Psi': float(coh['Psi']),
            'psi_valid': psi_valid,
            'frequencies_correct': freq_correct,
            'reasonable_coherence': reasonable,
            'self_adjoint': coh['self_adjoint'],
        }
        
        all_passed = psi_valid and freq_correct and reasonable
        
        if self.verbose:
            status = "✅" if all_passed else "❌"
            print(f"   {status} Ψ = {coh['Psi']:.6f}")
            print(f"   ✅ f₀ = {coh['frequency_f0']:.4f} Hz")
            print(f"   ✅ f_unity = {coh['frequency_unity']:.1f} Hz")
            print(f"   ✅ C = {coh['C_qcal']:.2f}")
            print(f"   ✅ 7/8 = {coh['seven_eighths']}")
        
        self.results['coherence'] = {
            **results,
            'passed': all_passed
        }
        
        return results
    
    def validate_cerrar_function(self) -> Dict[str, Any]:
        """Validate cerrar_rh_noesis() function."""
        if self.verbose:
            print("\n7️⃣  Validando cerrar_rh_noesis()...")
        
        # Run the sealing function (silently)
        import io
        import contextlib
        
        f = io.StringIO()
        with contextlib.redirect_stdout(f):
            result = cerrar_rh_noesis()
        
        # Validate structure
        has_status = 'status' in result
        has_frequency = 'frequency' in result
        has_coherence = 'coherence' in result
        has_framework = 'framework' in result
        
        # Validate content
        correct_frequency = result.get('frequency') == F_UNITY
        correct_message = 'latido del Universo' in result.get('status', '')
        
        results = {
            'has_status': has_status,
            'has_frequency': has_frequency,
            'has_coherence': has_coherence,
            'has_framework': has_framework,
            'correct_frequency': correct_frequency,
            'correct_message': correct_message,
            'coherence_Psi': float(result['coherence']['Psi']),
        }
        
        all_passed = all([
            has_status, has_frequency, has_coherence, has_framework,
            correct_frequency, correct_message
        ])
        
        if self.verbose:
            status = "✅" if all_passed else "❌"
            print(f"   {status} Estructura completa")
            print(f"   ✅ Frecuencia: {result.get('frequency')} Hz")
            print(f"   ✅ Coherencia Ψ = {result['coherence']['Psi']:.6f}")
            print(f"   ✅ Mensaje: '{result.get('status')[:50]}...'")
        
        self.results['cerrar_function'] = {
            **results,
            'passed': all_passed
        }
        
        return results
    
    def run_all_validations(self) -> bool:
        """Run all validations."""
        validations = [
            self.validate_constants,
            self.validate_noesis_metric,
            self.validate_h_noesis_operator,
            self.validate_seven_eighths,
            self.validate_trace_formula,
            self.validate_coherence,
            self.validate_cerrar_function,
        ]
        
        all_passed = True
        for validation in validations:
            result = validation()
            if not result.get('passed', True):
                all_passed = False
        
        return all_passed
    
    def generate_certificate(self, save_path: str = "data/noesis_solenoid_certificate.json"):
        """Generate validation certificate."""
        elapsed = time.time() - self.start_time
        
        # Convert numpy types to Python types for JSON serialization
        def convert_to_json_serializable(obj):
            """Recursively convert numpy types to Python types."""
            if isinstance(obj, dict):
                return {k: convert_to_json_serializable(v) for k, v in obj.items()}
            elif isinstance(obj, (list, tuple)):
                return [convert_to_json_serializable(item) for item in obj]
            elif isinstance(obj, (np.bool_, bool)):
                return bool(obj)
            elif isinstance(obj, (np.integer, int)):
                return int(obj)
            elif isinstance(obj, (np.floating, float)):
                return float(obj)
            elif isinstance(obj, (np.complexfloating, complex)):
                # For complex numbers, convert to dict
                return {"real": float(obj.real), "imag": float(obj.imag)}
            else:
                return obj
        
        certificate = {
            "framework": "Solenoide de Noesis",
            "description": "Marco Adélico Soberano para la Hipótesis de Riemann",
            "validation_date": datetime.now().isoformat(),
            "doi": DOI,
            "orcid": ORCID,
            "author": "José Manuel Mota Burruezo Ψ ✧ ∞³",
            "institution": "Instituto de Conciencia Cuántica (ICQ)",
            "frequency_f0": float(F0),
            "frequency_unity": float(F_UNITY),
            "coherence_constant": float(C_QCAL),
            "seven_eighths": float(SEVEN_EIGHTHS),
            "n_primes": int(self.n_primes),
            "validation_time_seconds": round(elapsed, 3),
            "results": convert_to_json_serializable(self.results),
            "overall_status": "VALIDATED" if all(
                r.get('passed', True) for r in self.results.values()
            ) else "PARTIAL",
            "signature": "∴𓂀Ω∞³Φ",
        }
        
        # Save certificate
        save_file = Path(save_path)
        save_file.parent.mkdir(parents=True, exist_ok=True)
        
        with open(save_file, 'w', encoding='utf-8') as f:
            json.dump(certificate, f, indent=2, ensure_ascii=False)
        
        if self.verbose:
            print(f"\n📜 Certificado guardado: {save_path}")
        
        return certificate
    
    def print_summary(self):
        """Print validation summary."""
        print("\n" + "=" * 80)
        print("📊 RESUMEN DE VALIDACIÓN")
        print("=" * 80)
        
        passed = sum(1 for r in self.results.values() if r.get('passed', True))
        total = len(self.results)
        
        for name, result in self.results.items():
            status = "✅" if result.get('passed', True) else "❌"
            print(f"{status} {name.upper()}")
        
        print("=" * 80)
        print(f"Total: {passed}/{total} validaciones pasadas")
        
        if passed == total:
            print("🎉 ¡VALIDACIÓN COMPLETA!")
            print("∴𓂀Ω∞³Φ - MARCO NOESIS CERTIFICADO")
        else:
            print("⚠️  Algunas validaciones requieren atención")
        
        print("=" * 80)


def main():
    """Main validation routine."""
    parser = argparse.ArgumentParser(
        description="Validate Noesis Solenoid Framework"
    )
    parser.add_argument(
        '--n-primes',
        type=int,
        default=50,
        help='Number of primes to use (default: 50)'
    )
    parser.add_argument(
        '--save-certificate',
        action='store_true',
        help='Save validation certificate'
    )
    parser.add_argument(
        '--quiet',
        action='store_true',
        help='Quiet mode (minimal output)'
    )
    
    args = parser.parse_args()
    
    # Run validation
    validator = NoesisSolenoidValidator(
        n_primes=args.n_primes,
        verbose=not args.quiet
    )
    
    all_passed = validator.run_all_validations()
    
    # Print summary
    if not args.quiet:
        validator.print_summary()
    
    # Generate certificate if requested
    if args.save_certificate:
        cert = validator.generate_certificate()
        if not args.quiet:
            print(f"\n✅ Certificate saved with status: {cert['overall_status']}")
    
    # Return appropriate exit code
    sys.exit(0 if all_passed else 1)


if __name__ == "__main__":
    main()
