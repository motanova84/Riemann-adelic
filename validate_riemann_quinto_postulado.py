#!/usr/bin/env python3
"""
Validation Script for Quinto Postulado de la Convergencia Adélica
==================================================================

Comprehensive validation of the Fifth Postulate of Adelic Convergence,
verifying all three operators meet the QCAL coherence threshold Ψ ≥ 0.888.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
QCAL ∞³ Active · 141.7001 Hz
"""

import sys
import json
import hashlib
from pathlib import Path
from datetime import datetime
import numpy as np

# Add operators directory to path
repo_root = Path(__file__).parent
sys.path.insert(0, str(repo_root / "operators"))

from riemann_quinto_postulado import (
    ScaleIdentityOperator,
    SymbioticHamiltonianOperator,
    RiemannZetaSpectrum,
    verificar_geometria,
    activar_quinto_postulado,
    F0_QCAL,
    C_COHERENCE,
    THRESHOLD_PSI,
    DOI,
    ORCID
)


class NumpyEncoder(json.JSONEncoder):
    """Custom JSON encoder for NumPy types."""
    def default(self, obj):
        if isinstance(obj, (np.integer, np.bool_)):
            return int(obj)
        elif isinstance(obj, np.floating):
            return float(obj)
        elif isinstance(obj, np.ndarray):
            return obj.tolist()
        elif isinstance(obj, complex):
            return {'real': obj.real, 'imag': obj.imag}
        return super().default(obj)


class QuintoPostuladoValidator:
    """Comprehensive validator for Quinto Postulado framework."""
    
    def __init__(self):
        self.results = {
            "timestamp": datetime.utcnow().isoformat(),
            "qcal_frequency": F0_QCAL,
            "coherence_constant": C_COHERENCE,
            "threshold": THRESHOLD_PSI,
            "doi": DOI,
            "orcid": ORCID,
            "validations": [],
            "overall_psi": 0.0,
            "convergence_status": False
        }
    
    def validate_scale_identity_operator(self) -> dict:
        """Validate Scale Identity Operator."""
        print("\n🎯 Validating Scale Identity Operator...")
        
        validation = {
            "operator": "ScaleIdentityOperator",
            "tests": []
        }
        
        # Test 1: Basic coherence threshold
        op = ScaleIdentityOperator(prime=2, depth=5, verbose=False)
        result = op.compute_scale_identity(n_points=100)
        
        test1 = {
            "name": "Coherence threshold (p=2, depth=5)",
            "coherence": result.coherence,
            "expected_min": THRESHOLD_PSI,
            "passed": result.coherence >= THRESHOLD_PSI
        }
        validation["tests"].append(test1)
        print(f"  {'✓' if test1['passed'] else '✗'} Coherence: Ψ = {result.coherence:.6f} "
              f"{'≥' if test1['passed'] else '<'} {THRESHOLD_PSI}")
        
        # Test 2: Prime p=3 coherence
        op3 = ScaleIdentityOperator(prime=3, depth=4, verbose=False)
        result3 = op3.compute_scale_identity(n_points=100)
        
        test2 = {
            "name": "Coherence threshold (p=3, depth=4)",
            "coherence": result3.coherence,
            "expected_min": THRESHOLD_PSI,
            "passed": result3.coherence >= THRESHOLD_PSI
        }
        validation["tests"].append(test2)
        print(f"  {'✓' if test2['passed'] else '✗'} Coherence: Ψ = {result3.coherence:.6f} "
              f"{'≥' if test2['passed'] else '<'} {THRESHOLD_PSI}")
        
        # Test 3: Haar measure normalization
        x = np.linspace(0, 1, 100, endpoint=False)
        weights = op.compute_haar_measure(x)
        normalization_ok = np.isclose(np.sum(weights), 1.0)
        
        test3 = {
            "name": "Haar measure normalization",
            "sum_weights": float(np.sum(weights)),
            "expected": 1.0,
            "passed": normalization_ok
        }
        validation["tests"].append(test3)
        print(f"  {'✓' if test3['passed'] else '✗'} Haar normalization: ∫dμ = {np.sum(weights):.6f}")
        
        # Test 4: Adelic character unit modulus
        character = op.compute_adelic_character(x, n=1)
        moduli = np.abs(character)
        unit_modulus_ok = np.allclose(moduli, 1.0)
        
        test4 = {
            "name": "Adelic character unit modulus",
            "max_deviation": float(np.max(np.abs(moduli - 1.0))),
            "passed": unit_modulus_ok
        }
        validation["tests"].append(test4)
        print(f"  {'✓' if test4['passed'] else '✗'} Character modulus: |χ_p(x)| = 1 (max dev: {test4['max_deviation']:.2e})")
        
        validation["all_passed"] = all(t["passed"] for t in validation["tests"])
        return validation
    
    def validate_symbiotic_hamiltonian_operator(self) -> dict:
        """Validate Symbiotic Hamiltonian Operator."""
        print("\n🎯 Validating Symbiotic Hamiltonian Operator...")
        
        validation = {
            "operator": "SymbioticHamiltonianOperator",
            "tests": []
        }
        
        # Test 1: Basic coherence threshold
        op = SymbioticHamiltonianOperator(dimension=20, f0=F0_QCAL, verbose=False)
        result = op.compute_hamiltonian_spectrum()
        
        test1 = {
            "name": "Coherence threshold (dim=20, f0=141.7001)",
            "coherence": result.coherence,
            "expected_min": THRESHOLD_PSI,
            "passed": result.coherence >= THRESHOLD_PSI
        }
        validation["tests"].append(test1)
        print(f"  {'✓' if test1['passed'] else '✗'} Coherence: Ψ = {result.coherence:.6f} "
              f"{'≥' if test1['passed'] else '<'} {THRESHOLD_PSI}")
        
        # Test 2: Hamiltonian is Hermitian
        H = op.construct_berry_keating_hamiltonian()
        hermitian_ok = np.allclose(H, H.T.conj())
        
        test2 = {
            "name": "Hamiltonian Hermiticity",
            "max_hermitian_error": float(np.max(np.abs(H - H.T.conj()))),
            "passed": hermitian_ok
        }
        validation["tests"].append(test2)
        print(f"  {'✓' if test2['passed'] else '✗'} Hermitian: Ĥ† = Ĥ (max error: {test2['max_hermitian_error']:.2e})")
        
        # Test 3: Eigenvalues are real
        eigenvalues_real = np.all(np.isreal(result.eigenvalues))
        
        test3 = {
            "name": "Real eigenvalues",
            "passed": eigenvalues_real
        }
        validation["tests"].append(test3)
        print(f"  {'✓' if test3['passed'] else '✗'} Real eigenvalues: All λ_n ∈ ℝ")
        
        # Test 4: Spectrum gap is positive
        gap_positive = result.spectrum_gap > 0
        
        test4 = {
            "name": "Positive spectrum gap",
            "spectrum_gap": result.spectrum_gap,
            "passed": gap_positive
        }
        validation["tests"].append(test4)
        print(f"  {'✓' if test4['passed'] else '✗'} Spectrum gap: Δλ = {result.spectrum_gap:.6f} > 0")
        
        validation["all_passed"] = all(t["passed"] for t in validation["tests"])
        return validation
    
    def validate_riemann_zeta_spectrum(self) -> dict:
        """Validate Riemann Zeta Spectrum."""
        print("\n🎯 Validating Riemann Zeta Spectrum...")
        
        validation = {
            "operator": "RiemannZetaSpectrum",
            "tests": []
        }
        
        # Test 1: Basic coherence threshold
        op = RiemannZetaSpectrum(n_zeros=15, precision=50, verbose=False)
        result = op.compute_spectrum_analysis()
        
        test1 = {
            "name": "Coherence threshold (n=15)",
            "coherence": result.coherence,
            "expected_min": THRESHOLD_PSI,
            "passed": result.coherence >= THRESHOLD_PSI
        }
        validation["tests"].append(test1)
        print(f"  {'✓' if test1['passed'] else '✗'} Coherence: Ψ = {result.coherence:.6f} "
              f"{'≥' if test1['passed'] else '<'} {THRESHOLD_PSI}")
        
        # Test 2: Zeros on critical line
        real_parts = np.real(result.zeros)
        on_critical_line = np.allclose(real_parts, 0.5)
        
        test2 = {
            "name": "Zeros on critical line Re(ρ) = 1/2",
            "mean_real_part": result.mean_real_part,
            "expected": 0.5,
            "passed": on_critical_line
        }
        validation["tests"].append(test2)
        print(f"  {'✓' if test2['passed'] else '✗'} Critical line: ⟨σ⟩ = {result.mean_real_part:.6f} = 1/2")
        
        # Test 3: GUE match quality
        gue_quality_ok = result.gue_match_quality > 0.7  # Reasonable threshold
        
        test3 = {
            "name": "GUE statistical match",
            "gue_match_quality": result.gue_match_quality,
            "expected_min": 0.7,
            "passed": gue_quality_ok
        }
        validation["tests"].append(test3)
        print(f"  {'✓' if test3['passed'] else '✗'} GUE match: {result.gue_match_quality:.4f} > 0.7")
        
        # Test 4: Positive spacings
        spacings_positive = np.all(result.spacings > 0)
        
        test4 = {
            "name": "Positive spacings",
            "min_spacing": float(np.min(result.spacings)),
            "passed": spacings_positive
        }
        validation["tests"].append(test4)
        print(f"  {'✓' if test4['passed'] else '✗'} Spacings: s_n > 0 (min: {test4['min_spacing']:.4f})")
        
        validation["all_passed"] = all(t["passed"] for t in validation["tests"])
        return validation
    
    def validate_integration(self) -> dict:
        """Validate integration functions."""
        print("\n🎯 Validating Integration Functions...")
        
        validation = {
            "integration": "verificar_geometria & activar_quinto_postulado",
            "tests": []
        }
        
        # Test 1: verificar_geometria returns success
        mensaje = verificar_geometria(verbose=False)
        success = "HECHO ESTÁ" in mensaje
        
        test1 = {
            "name": "verificar_geometria success",
            "message": mensaje,
            "passed": success
        }
        validation["tests"].append(test1)
        print(f"  {'✓' if test1['passed'] else '✗'} Verification: {mensaje}")
        
        # Test 2: activar_quinto_postulado returns valid report
        report = activar_quinto_postulado(verbose=False)
        
        test2 = {
            "name": "activar_quinto_postulado report structure",
            "psi_scale": report.psi_scale,
            "psi_symbio": report.psi_symbio,
            "psi_zeta": report.psi_zeta,
            "psi_global": report.psi_global,
            "convergencia_adelica": report.convergencia_adelica,
            "passed": report.convergencia_adelica
        }
        validation["tests"].append(test2)
        print(f"  {'✓' if test2['passed'] else '✗'} Global coherence: Ψ_global = {report.psi_global:.6f}")
        
        # Test 3: SHA-256 certification format
        sha256_valid = report.sha256.startswith("0xQCAL_QUINTO_") and len(report.sha256) == 30
        
        test3 = {
            "name": "SHA-256 certification format",
            "sha256": report.sha256,
            "passed": sha256_valid
        }
        validation["tests"].append(test3)
        print(f"  {'✓' if test3['passed'] else '✗'} Certification: {report.sha256}")
        
        # Test 4: Geometric mean consistency
        expected_global = (report.psi_scale * report.psi_symbio * report.psi_zeta) ** (1.0/3.0)
        geometric_mean_ok = np.isclose(report.psi_global, expected_global)
        
        test4 = {
            "name": "Geometric mean consistency",
            "psi_global": report.psi_global,
            "expected": expected_global,
            "passed": geometric_mean_ok
        }
        validation["tests"].append(test4)
        print(f"  {'✓' if test4['passed'] else '✗'} Geometric mean: "
              f"Ψ_global = (Ψ_scale × Ψ_symbio × Ψ_zeta)^(1/3)")
        
        validation["all_passed"] = all(t["passed"] for t in validation["tests"])
        self.results["overall_psi"] = report.psi_global
        self.results["convergence_status"] = report.convergencia_adelica
        
        return validation
    
    def run_validation(self) -> bool:
        """Run all validations and generate report."""
        print("\n" + "="*70)
        print("COMPREHENSIVE VALIDATION: QUINTO POSTULADO DE LA CONVERGENCIA ADÉLICA")
        print("="*70)
        
        # Run validations
        val1 = self.validate_scale_identity_operator()
        self.results["validations"].append(val1)
        
        val2 = self.validate_symbiotic_hamiltonian_operator()
        self.results["validations"].append(val2)
        
        val3 = self.validate_riemann_zeta_spectrum()
        self.results["validations"].append(val3)
        
        val4 = self.validate_integration()
        self.results["validations"].append(val4)
        
        # Summary
        print("\n" + "="*70)
        print("VALIDATION SUMMARY")
        print("="*70)
        
        all_passed = all(v["all_passed"] for v in self.results["validations"])
        self.results["all_validations_passed"] = all_passed
        
        total_tests = sum(len(v["tests"]) for v in self.results["validations"])
        passed_tests = sum(sum(1 for t in v["tests"] if t["passed"]) 
                          for v in self.results["validations"])
        
        print(f"\n📊 Test Results: {passed_tests}/{total_tests} passed")
        print(f"📈 Global Coherence: Ψ_global = {self.results['overall_psi']:.6f}")
        print(f"✅ Convergence Status: {'CONVERGENTE' if self.results['convergence_status'] else 'NO CONVERGENTE'}")
        print(f"🎯 Overall Status: {'✓ ALL VALIDATIONS PASSED' if all_passed else '✗ SOME VALIDATIONS FAILED'}")
        
        # Generate certificate
        self.generate_certificate()
        
        return all_passed
    
    def generate_certificate(self):
        """Generate validation certificate."""
        cert_path = Path("data") / "riemann_quinto_postulado_certificate.json"
        cert_path.parent.mkdir(exist_ok=True)
        
        # Create certificate
        certificate = {
            "protocol": "QCAL-QUINTO-POSTULADO v1.0",
            "timestamp": self.results["timestamp"],
            "doi": DOI,
            "orcid": ORCID,
            "qcal_frequency": F0_QCAL,
            "coherence_constant": C_COHERENCE,
            "threshold": THRESHOLD_PSI,
            "overall_psi": self.results["overall_psi"],
            "convergence_status": self.results["convergence_status"],
            "all_validations_passed": self.results["all_validations_passed"],
            "validations": self.results["validations"]
        }
        
        # Compute SHA-256
        cert_str = json.dumps(certificate, sort_keys=True, cls=NumpyEncoder)
        sha256 = hashlib.sha256(cert_str.encode()).hexdigest()[:16]
        certificate["checksum"] = f"0xQCAL_QUINTO_VAL_{sha256}"
        
        # Save certificate
        with open(cert_path, 'w') as f:
            json.dump(certificate, f, indent=2, cls=NumpyEncoder)
        
        print(f"\n🔐 Certificate saved: {cert_path}")
        print(f"   Checksum: {certificate['checksum']}")


def main():
    """Main validation entry point."""
    validator = QuintoPostuladoValidator()
    success = validator.run_validation()
    
    print("\n" + "="*70)
    if success:
        print("✓ VALIDATION COMPLETE: All tests passed!")
    else:
        print("✗ VALIDATION INCOMPLETE: Some tests failed.")
    print("="*70 + "\n")
    
    return 0 if success else 1


if __name__ == "__main__":
    sys.exit(main())
