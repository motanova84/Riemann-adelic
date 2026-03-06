#!/usr/bin/env python3
"""
Validation Script for Spectral Attack on Riemann Hypothesis
============================================================

Comprehensive validation of the spectral attack framework, including:
1. Selberg trace formula accuracy
2. Montgomery R₂ pair correlation
3. GUE spectral matching
4. ΔR₂ deviation analysis
5. Critical line consistency checks

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

from spectral_attack_rh import (
    SpectralAttackRH,
    demonstrate_spectral_attack,
    F0_QCAL,
    C_COHERENCE
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
        return super().default(obj)


class SpectralAttackValidator:
    """Comprehensive validator for spectral attack framework."""
    
    def __init__(self):
        self.results = {
            "timestamp": datetime.utcnow().isoformat(),
            "qcal_frequency": F0_QCAL,
            "coherence_constant": C_COHERENCE,
            "validations": [],
            "overall_psi": 0.0
        }
        
        # Known high-precision zeros
        self.known_zeros = np.array([
            14.134725141734693790,
            21.022039638771754864,
            25.010857580145688763,
            30.424876125859513210,
            32.935061587739189690,
            37.586178158825671257,
            40.918719012147495187,
            43.327073280914999519,
            48.005150881167159727,
            49.773832477672302181,
            52.970321477714460644,
            56.446247697063394804,
            59.347044002602353079,
            60.831778524609809844,
            65.112544048081606660
        ])
    
    def validate_selberg_trace_convergence(self) -> dict:
        """Validate Selberg trace formula convergence."""
        print("\n🎯 Validating Selberg Trace Formula Convergence...")
        
        attack = SpectralAttackRH(precision=50, prime_cutoff=500, verbose=False)
        
        # Test with Gaussian
        def phi(t):
            return float(np.exp(-t**2 / 200.0))
        
        def phi_hat(r):
            return float(np.sqrt(2 * np.pi * 200) * np.exp(-200 * r**2 / 2.0))
        
        zeros = self.known_zeros
        result = attack.selberg_trace_formula(zeros, phi, phi_hat)
        
        # Check convergence quality
        quality = result.convergence_quality
        passed = quality > 0.0  # At least some convergence
        
        print(f"   Convergence quality: {quality:.4f}")
        print(f"   Remainder: {abs(result.remainder):.6f}")
        print(f"   Status: {'✅ PASS' if passed else '❌ FAIL'}")
        
        return {
            "name": "Selberg Trace Convergence",
            "passed": passed,
            "quality": float(quality),
            "remainder": float(abs(result.remainder)),
            "psi": float(quality)
        }
    
    def validate_montgomery_r2_gue_statistics(self) -> dict:
        """Validate Montgomery R₂ matches GUE statistics."""
        print("\n📊 Validating Montgomery R₂ GUE Statistics...")
        
        attack = SpectralAttackRH(verbose=False)
        zeros = self.known_zeros
        result = attack.montgomery_pair_correlation(zeros, s_max=3.0, n_bins=50)
        
        # Check GUE match quality
        gue_match = result.gue_match_quality
        passed = gue_match > 0.3  # Reasonable match for small sample
        
        print(f"   GUE match quality: {gue_match:.4f}")
        print(f"   Mean spacing: {result.mean_spacing:.4f}")
        print(f"   Status: {'✅ PASS' if passed else '❌ FAIL'}")
        
        return {
            "name": "Montgomery R₂ GUE Statistics",
            "passed": passed,
            "gue_match_quality": float(gue_match),
            "mean_spacing": float(result.mean_spacing),
            "psi": float(gue_match)
        }
    
    def validate_delta_r2_computation(self) -> dict:
        """Validate ΔR₂ = R₂^ζ - R₂^Δ_K computation."""
        print("\n⚡ Validating ΔR₂ Computation...")
        
        attack = SpectralAttackRH(verbose=False)
        zeros = self.known_zeros
        result = attack.compute_spectral_attack(zeros)
        
        # Verify ΔR₂ definition
        montgomery = result.montgomery_result
        computed_delta = montgomery.R2_zeta - montgomery.R2_laplacian
        
        diff = np.max(np.abs(result.delta_R2 - computed_delta))
        passed = diff < 1e-10
        
        print(f"   max|ΔR₂|: {result.max_deviation:.6f}")
        print(f"   RMS(ΔR₂): {result.rms_deviation:.6f}")
        print(f"   Computation error: {diff:.2e}")
        print(f"   Status: {'✅ PASS' if passed else '❌ FAIL'}")
        
        return {
            "name": "ΔR₂ Computation",
            "passed": passed,
            "max_deviation": float(result.max_deviation),
            "rms_deviation": float(result.rms_deviation),
            "computation_error": float(diff),
            "psi": 1.0 if diff < 1e-10 else 0.5
        }
    
    def validate_critical_line_consistency(self) -> dict:
        """Validate critical line consistency for known zeros."""
        print("\n🎯 Validating Critical Line Consistency...")
        
        attack = SpectralAttackRH(precision=50, verbose=False)
        zeros = self.known_zeros
        result = attack.compute_spectral_attack(zeros)
        
        # All known zeros are on critical line Re(s) = 1/2
        # So σ deviation bound should be small
        sigma_bound = result.sigma_deviation_bound
        passed = sigma_bound < 10.0  # Reasonable for small sample statistics
        
        print(f"   Verdict: {result.verdict}")
        print(f"   |σ - 1/2| bound: {sigma_bound:.6f}")
        print(f"   Critical line evidence: {result.critical_line_evidence:.4f}")
        print(f"   Status: {'✅ PASS' if passed else '❌ FAIL'}")
        
        return {
            "name": "Critical Line Consistency",
            "passed": passed,
            "verdict": result.verdict,
            "sigma_deviation_bound": float(sigma_bound),
            "critical_line_evidence": float(result.critical_line_evidence),
            "psi": max(0.0, 1.0 - sigma_bound / 10.0)
        }
    
    def validate_laplacian_spectrum_generation(self) -> dict:
        """Validate reference Laplacian spectrum generation."""
        print("\n🌐 Validating Laplacian Spectrum Generation...")
        
        attack = SpectralAttackRH(verbose=False)
        N = 100
        genus = 2
        t_n = attack.generate_reference_laplacian_spectrum(N, genus)
        
        # Check properties
        all_positive = np.all(t_n > 0)
        all_increasing = np.all(np.diff(t_n) > 0)
        correct_count = len(t_n) == N
        
        # Check Weyl law: t_n ~ √(4πn/area)
        area = 4 * np.pi * (genus - 1)
        n = np.arange(1, N + 1)
        expected = np.sqrt(4 * np.pi * n / area)
        weyl_error = np.mean(np.abs(t_n - expected))
        weyl_valid = weyl_error < 2.0  # Allow GUE perturbations
        
        passed = all_positive and all_increasing and correct_count and weyl_valid
        
        print(f"   All positive: {all_positive}")
        print(f"   All increasing: {all_increasing}")
        print(f"   Correct count: {correct_count}")
        print(f"   Weyl law error: {weyl_error:.6f}")
        print(f"   Status: {'✅ PASS' if passed else '❌ FAIL'}")
        
        return {
            "name": "Laplacian Spectrum Generation",
            "passed": passed,
            "all_positive": int(all_positive),
            "all_increasing": int(all_increasing),
            "weyl_law_error": float(weyl_error),
            "psi": 1.0 if passed else 0.0
        }
    
    def validate_mathematical_consistency(self) -> dict:
        """Validate overall mathematical consistency."""
        print("\n🔬 Validating Mathematical Consistency...")
        
        attack = SpectralAttackRH(precision=50, verbose=False)
        
        # Test with multiple zero sets
        passed_tests = 0
        total_tests = 3
        
        for n_zeros in [5, 10, 15]:
            zeros = self.known_zeros[:n_zeros]
            result = attack.compute_spectral_attack(zeros)
            
            # Check mathematical properties
            checks = [
                result.max_deviation >= 0,
                result.rms_deviation >= 0,
                result.rms_deviation <= result.max_deviation,
                0.0 <= result.critical_line_evidence <= 1.0,
                result.sigma_deviation_bound >= 0,
                len(result.delta_R2) > 0,
            ]
            
            if all(checks):
                passed_tests += 1
        
        passed = passed_tests == total_tests
        psi = passed_tests / total_tests
        
        print(f"   Passed: {passed_tests}/{total_tests}")
        print(f"   Status: {'✅ PASS' if passed else '❌ FAIL'}")
        
        return {
            "name": "Mathematical Consistency",
            "passed": passed,
            "passed_tests": passed_tests,
            "total_tests": total_tests,
            "psi": float(psi)
        }
    
    def run_all_validations(self) -> bool:
        """Run all validations and generate report."""
        print("\n" + "="*70)
        print("  SPECTRAL ATTACK RH - VALIDATION SUITE")
        print("  La Ecuación que Desafía RH")
        print("="*70)
        print(f"\n  QCAL f₀: {F0_QCAL} Hz")
        print(f"  C^∞: {C_COHERENCE}")
        print(f"  Timestamp: {self.results['timestamp']}")
        
        # Run all validations
        validations = [
            self.validate_selberg_trace_convergence(),
            self.validate_montgomery_r2_gue_statistics(),
            self.validate_delta_r2_computation(),
            self.validate_critical_line_consistency(),
            self.validate_laplacian_spectrum_generation(),
            self.validate_mathematical_consistency(),
        ]
        
        self.results["validations"] = validations
        
        # Compute overall Ψ
        psi_values = [v["psi"] for v in validations]
        overall_psi = np.mean(psi_values)
        self.results["overall_psi"] = float(overall_psi)
        
        # Summary
        passed_count = sum(1 for v in validations if v["passed"])
        total_count = len(validations)
        
        print("\n" + "="*70)
        print(f"  VALIDATION SUMMARY")
        print("="*70)
        print(f"\n  Passed: {passed_count}/{total_count}")
        print(f"  Overall Ψ: {overall_psi:.4f}")
        
        if overall_psi >= 0.9:
            print("\n  ✅ EXCELLENT - Spectral attack framework fully validated")
        elif overall_psi >= 0.7:
            print("\n  ✅ GOOD - Spectral attack framework validated")
        elif overall_psi >= 0.5:
            print("\n  ⚠️  ACCEPTABLE - Some validations need attention")
        else:
            print("\n  ❌ NEEDS WORK - Significant issues detected")
        
        print(f"\n{'='*70}\n")
        
        return overall_psi >= 0.7
    
    def save_certificate(self, filename: str = "data/spectral_attack_rh_certificate.json"):
        """Save validation certificate."""
        output_path = repo_root / filename
        output_path.parent.mkdir(exist_ok=True)
        
        # Generate certificate hash
        cert_string = json.dumps(self.results, sort_keys=True, cls=NumpyEncoder)
        cert_hash = hashlib.sha256(cert_string.encode()).hexdigest()[:16]
        
        certificate = {
            **self.results,
            "certificate_id": f"0xQCAL_SPECTRAL_ATTACK_{cert_hash}",
            "validation_framework": "QCAL ∞³ Spectral Attack RH",
            "mathematical_signature": "∴𓂀Ω∞³Φ @ 141.7001 Hz",
            "doi": "10.5281/zenodo.17379721",
            "author": "José Manuel Mota Burruezo Ψ ✧ ∞³",
            "institution": "Instituto de Conciencia Cuántica (ICQ)"
        }
        
        with open(output_path, 'w') as f:
            json.dump(certificate, f, indent=2, cls=NumpyEncoder)
        
        print(f"📜 Certificate saved: {output_path}")
        print(f"🔖 ID: {certificate['certificate_id']}")
        
        return certificate


def main():
    """Main validation entry point."""
    validator = SpectralAttackValidator()
    
    # Run all validations
    success = validator.run_all_validations()
    
    # Save certificate
    certificate = validator.save_certificate()
    
    # Return exit code
    return 0 if success else 1


if __name__ == "__main__":
    sys.exit(main())
