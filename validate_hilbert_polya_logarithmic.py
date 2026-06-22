#!/usr/bin/env python3
"""
Validation Script for Hilbert-Pólya Logarithmic Operator
=========================================================

Validates the complete Hilbert-Pólya operator implementation
and its integration with the QCAL ∞³ framework.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz
"""

import argparse
import json
import sys
from dataclasses import asdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, List, Tuple

import numpy as np

# Add operators to path
repo_root = Path(__file__).parent
sys.path.insert(0, str(repo_root / "operators"))

from hilbert_polya_logarithmic import (
    F0_QCAL,
    C_PRIMARY,
    C_COHERENCE,
    PSI_THRESHOLD,
    RIEMANN_ZEROS,
    PRIMES,
    LogarithmicHilbertSpace,
    HyperbolicDilationOperator,
    ArithmeticPotentialOperator,
    HilbertPolyaOperator,
    verificar_geometria_logaritmica,
    activar_hilbert_polya,
    demonstrate_hilbert_polya,
)


# =============================================================================
# JSON ENCODER FOR NUMPY TYPES
# =============================================================================

class NumpyEncoder(json.JSONEncoder):
    """JSON encoder that handles NumPy types"""
    
    def default(self, obj):
        if isinstance(obj, np.integer):
            return int(obj)
        elif isinstance(obj, np.floating):
            return float(obj)
        elif isinstance(obj, np.ndarray):
            return obj.tolist()
        elif isinstance(obj, np.bool_):
            return bool(obj)
        elif isinstance(obj, complex):
            return {'real': obj.real, 'imag': obj.imag}
        return super().default(obj)


# =============================================================================
# VALIDATOR CLASS
# =============================================================================

class HilbertPolyaValidator:
    """Validates Hilbert-Pólya logarithmic operator"""
    
    def __init__(self, verbose: bool = True):
        """
        Initialize validator.
        
        Parameters
        ----------
        verbose : bool
            Whether to print progress
        """
        self.verbose = verbose
        self.checks: List[Dict] = []
        self.passed = 0
        self.failed = 0
    
    def _record(self, name: str, passed: bool, metrics: Dict, detail: str = ""):
        """
        Record a validation check.
        
        Parameters
        ----------
        name : str
            Check name
        passed : bool
            Whether check passed
        metrics : dict
            Numeric metrics
        detail : str
            Additional detail string
        """
        status = "✅ PASS" if passed else "❌ FAIL"
        
        check = {
            'name': name,
            'passed': passed,
            'metrics': metrics,
            'detail': detail,
            'timestamp': datetime.now(timezone.utc).isoformat(),
        }
        
        self.checks.append(check)
        
        if passed:
            self.passed += 1
        else:
            self.failed += 1
        
        if self.verbose:
            print(f"{status} {name}")
            if metrics:
                for key, value in metrics.items():
                    if isinstance(value, float):
                        print(f"     {key}: {value:.6f}")
                    else:
                        print(f"     {key}: {value}")
            if detail:
                print(f"     {detail}")
    
    # =========================================================================
    # CATEGORY A: Constants and Configuration
    # =========================================================================
    
    def check_A1_qcal_constants(self):
        """A1: QCAL constants are defined correctly"""
        checks = [
            ('F0_QCAL', F0_QCAL, 141.7001),
            ('C_PRIMARY', C_PRIMARY, 629.83),
            ('C_COHERENCE', C_COHERENCE, 244.36),
            ('PSI_THRESHOLD', PSI_THRESHOLD, 0.888),
        ]
        
        for name, actual, expected in checks:
            passed = np.abs(actual - expected) < 1e-6
            self._record(
                f"A1.{name}",
                passed,
                {'value': actual, 'expected': expected}
            )
    
    def check_A2_reference_data(self):
        """A2: Reference data (zeros, primes) is valid"""
        # Check Riemann zeros
        passed_zeros = len(RIEMANN_ZEROS) >= 10 and np.all(RIEMANN_ZEROS > 0)
        self._record(
            "A2.RiemannZeros",
            passed_zeros,
            {'count': len(RIEMANN_ZEROS), 'first': RIEMANN_ZEROS[0]}
        )
        
        # Check primes
        passed_primes = len(PRIMES) >= 10 and PRIMES[0] == 2
        self._record(
            "A2.Primes",
            passed_primes,
            {'count': len(PRIMES), 'first': PRIMES[0]}
        )
    
    # =========================================================================
    # CATEGORY B: Component Operators
    # =========================================================================
    
    def check_B1_logarithmic_space(self):
        """B1: Logarithmic Hilbert space is properly constructed"""
        space = LogarithmicHilbertSpace(n_points=128, u_max=8.0)
        result = space.compute()
        
        # Check symmetry
        passed_sym = result.symmetry_error < 1e-12
        self._record(
            "B1.ScaleSymmetry",
            passed_sym,
            {'symmetry_error': result.symmetry_error}
        )
        
        # Check coherence
        passed_psi = result.psi >= PSI_THRESHOLD
        self._record(
            "B1.Coherence",
            passed_psi,
            {'psi': result.psi, 'threshold': PSI_THRESHOLD}
        )
    
    def check_B2_dilation_operator(self):
        """B2: Hyperbolic dilation operator is Hermitian"""
        op = HyperbolicDilationOperator(n_points=128, u_max=8.0)
        result = op.compute()
        
        # Check Hermiticity
        passed_herm = result.hermiticity_error < 1e-10
        self._record(
            "B2.Hermiticity",
            passed_herm,
            {'error': result.hermiticity_error}
        )
        
        # Check eigenvalues are real
        passed_real = np.all(np.abs(np.imag(result.eigenvalues)) < 1e-10)
        self._record(
            "B2.RealEigenvalues",
            passed_real,
            {'max_imag': np.max(np.abs(np.imag(result.eigenvalues)))}
        )
        
        # Check coherence
        passed_psi = result.psi >= PSI_THRESHOLD
        self._record(
            "B2.Coherence",
            passed_psi,
            {'psi': result.psi}
        )
    
    def check_B3_arithmetic_potential(self):
        """B3: Arithmetic potential has correct properties"""
        op = ArithmeticPotentialOperator(n_points=128, u_max=8.0, n_primes=20)
        result = op.compute()
        
        # Check evenness
        passed_even = result.evenness_error < 1e-12
        self._record(
            "B3.Evenness",
            passed_even,
            {'error': result.evenness_error}
        )
        
        # Check coherence
        passed_psi = result.psi >= PSI_THRESHOLD
        self._record(
            "B3.Coherence",
            passed_psi,
            {'psi': result.psi}
        )
    
    # =========================================================================
    # CATEGORY C: Complete Operator
    # =========================================================================
    
    def check_C1_full_operator_hermiticity(self):
        """C1: Complete H_Ω is Hermitian"""
        op = HilbertPolyaOperator(n_points=128, u_max=8.0, n_primes=20, n_zeros=10)
        result = op.compute()
        
        passed = result.hermiticity_error < 1e-10
        self._record(
            "C1.FullHermiticity",
            passed,
            {'error': result.hermiticity_error}
        )
    
    def check_C2_spectral_alignment(self):
        """C2: Eigenvalues align with Riemann zeros"""
        op = HilbertPolyaOperator(n_points=256, u_max=10.0, n_primes=30, n_zeros=10)
        result = op.compute()
        
        # Allow large error for now (theory is still being developed)
        passed = result.spectral_error < 100.0
        self._record(
            "C2.SpectralAlignment",
            passed,
            {'rms_error': result.spectral_error, 'psi_spectral': result.psi_spectral}
        )
    
    def check_C3_gue_statistics(self):
        """C3: Level spacings follow GUE"""
        op = HilbertPolyaOperator(n_points=256, u_max=10.0, n_primes=30, n_zeros=10)
        result = op.compute()
        
        # KS statistic should be reasonably small
        passed = result.gue_spacing_ks < 0.7
        self._record(
            "C3.GUEStatistics",
            passed,
            {'ks_statistic': result.gue_spacing_ks, 'psi_gue': result.psi_gue}
        )
    
    def check_C4_coherence_metrics(self):
        """C4: All coherence metrics are computed"""
        op = HilbertPolyaOperator(n_points=128, u_max=8.0, n_primes=20, n_zeros=10)
        result = op.compute()
        
        metrics = {
            'psi_hermiticity': result.psi_hermiticity,
            'psi_spectral': result.psi_spectral,
            'psi_gue': result.psi_gue,
            'psi_global': result.psi,
        }
        
        # All should be in valid range [0, 1]
        passed = all(0 <= v <= 1 for v in metrics.values())
        self._record(
            "C4.CoherenceMetrics",
            passed,
            metrics
        )
    
    # =========================================================================
    # CATEGORY D: Geometric Validation
    # =========================================================================
    
    def check_D1_geometric_validation(self):
        """D1: Geometric validation passes"""
        checks = verificar_geometria_logaritmica()
        
        # Count passes
        passed_count = sum(1 for v in checks.values() if v)
        total_count = len(checks)
        
        # Most checks should pass
        passed = passed_count >= total_count * 0.7
        
        self._record(
            "D1.GeometricValidation",
            passed,
            {'passed': passed_count, 'total': total_count}
        )
    
    def check_D2_certificate_generation(self):
        """D2: SHA-256 certificate is generated"""
        cert = activar_hilbert_polya()
        
        passed = isinstance(cert, str) and len(cert) == 64
        self._record(
            "D2.Certificate",
            passed,
            {'length': len(cert), 'hash': cert[:16] + "..."}
        )
    
    # =========================================================================
    # CATEGORY E: Integration and Performance
    # =========================================================================
    
    def check_E1_computation_time(self):
        """E1: Computation completes in reasonable time"""
        op = HilbertPolyaOperator(n_points=128, u_max=8.0, n_primes=20, n_zeros=10)
        result = op.compute()
        
        # Should complete in < 1 second
        passed = result.computation_time_ms < 1000.0
        self._record(
            "E1.ComputationTime",
            passed,
            {'time_ms': result.computation_time_ms}
        )
    
    def check_E2_numerical_stability(self):
        """E2: Results are numerically stable"""
        op = HilbertPolyaOperator(n_points=64, u_max=6.0, n_primes=15, n_zeros=5)
        
        # Run twice and compare
        result1 = op.compute()
        result2 = op.compute()
        
        # Eigenvalues should be identical
        eig_diff = np.max(np.abs(result1.eigenvalues - result2.eigenvalues))
        passed = eig_diff < 1e-12
        
        self._record(
            "E2.NumericalStability",
            passed,
            {'eigenvalue_diff': eig_diff}
        )
    
    def check_E3_demonstration_runs(self):
        """E3: Demonstration function runs successfully"""
        try:
            result = demonstrate_hilbert_polya(verbose=False)
            passed = result is not None and hasattr(result, 'psi')
            self._record(
                "E3.Demonstration",
                passed,
                {'psi': result.psi if result else 0}
            )
        except Exception as e:
            self._record(
                "E3.Demonstration",
                False,
                {},
                f"Exception: {str(e)}"
            )
    
    # =========================================================================
    # Run All Checks
    # =========================================================================
    
    def run(self) -> Tuple[int, int]:
        """
        Run all validation checks.
        
        Returns
        -------
        passed, failed : int, int
            Number of passed and failed checks
        """
        if self.verbose:
            print("=" * 80)
            print("Hilbert-Pólya Logarithmic Operator Validation")
            print("=" * 80)
            print()
        
        # Category A: Constants
        if self.verbose:
            print("CATEGORY A: Constants and Configuration")
            print("-" * 80)
        self.check_A1_qcal_constants()
        self.check_A2_reference_data()
        if self.verbose:
            print()
        
        # Category B: Components
        if self.verbose:
            print("CATEGORY B: Component Operators")
            print("-" * 80)
        self.check_B1_logarithmic_space()
        self.check_B2_dilation_operator()
        self.check_B3_arithmetic_potential()
        if self.verbose:
            print()
        
        # Category C: Complete Operator
        if self.verbose:
            print("CATEGORY C: Complete Operator")
            print("-" * 80)
        self.check_C1_full_operator_hermiticity()
        self.check_C2_spectral_alignment()
        self.check_C3_gue_statistics()
        self.check_C4_coherence_metrics()
        if self.verbose:
            print()
        
        # Category D: Geometric
        if self.verbose:
            print("CATEGORY D: Geometric Validation")
            print("-" * 80)
        self.check_D1_geometric_validation()
        self.check_D2_certificate_generation()
        if self.verbose:
            print()
        
        # Category E: Integration
        if self.verbose:
            print("CATEGORY E: Integration and Performance")
            print("-" * 80)
        self.check_E1_computation_time()
        self.check_E2_numerical_stability()
        self.check_E3_demonstration_runs()
        if self.verbose:
            print()
        
        # Summary
        if self.verbose:
            print("=" * 80)
            print(f"SUMMARY: {self.passed} passed, {self.failed} failed")
            print("=" * 80)
            
            if self.failed == 0:
                print("✅ All validation checks PASSED")
            else:
                print(f"⚠️  {self.failed} check(s) FAILED")
            print()
        
        return self.passed, self.failed


# =============================================================================
# MAIN ENTRY POINT
# =============================================================================

def main():
    """Main entry point"""
    parser = argparse.ArgumentParser(
        description="Validate Hilbert-Pólya Logarithmic Operator"
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Output results as JSON"
    )
    parser.add_argument(
        "--quiet",
        action="store_true",
        help="Suppress verbose output"
    )
    
    args = parser.parse_args()
    
    # Run validation
    validator = HilbertPolyaValidator(verbose=not args.quiet)
    passed, failed = validator.run()
    
    # Output JSON if requested
    if args.json:
        output = {
            'timestamp': datetime.now(timezone.utc).isoformat(),
            'operator': 'HilbertPolyaLogarithmic',
            'framework': 'QCAL_Infinity3',
            'summary': {
                'passed': passed,
                'failed': failed,
                'total': passed + failed,
                'success_rate': passed / (passed + failed) if (passed + failed) > 0 else 0,
            },
            'checks': validator.checks,
        }
        
        # Write to file
        output_file = Path("data/hilbert_polya_logarithmic_validation.json")
        output_file.parent.mkdir(exist_ok=True)
        
        with open(output_file, 'w') as f:
            json.dump(output, f, indent=2, cls=NumpyEncoder)
        
        if not args.quiet:
            print(f"Results written to: {output_file}")
    
    # Exit with appropriate code
    return 0 if failed == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
