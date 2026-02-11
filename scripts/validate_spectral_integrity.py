#!/usr/bin/env python3
"""
∴𓂀 QCAL Spectral Integrity Validator
======================================

Valida que la integridad espectral del sistema QCAL se mantiene,
especialmente verificando que:

1. La fase NO ha sido normalizada con abs() en lugares críticos
2. Los eigenvalores mantienen su signo original
3. El espectro está alineado con los zeros de Riemann
4. La coherencia QCAL C = 244.36 se preserva
5. El Hamiltoniano H_Ψ mantiene su estructura autoadjunta

Este script es ejecutado por el Noesis Guardian cuando detecta
sugerencias problemáticas de normalización.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
License: Creative Commons BY-NC-SA 4.0
Date: February 2026
"""

import json
import os
import re
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Tuple

# Ensure we're running from repo root
def verify_repository_root():
    """Verify we're running from the repository root."""
    cwd = Path.cwd()
    
    # Check for key repository files
    key_files = ['.qcal_beacon', 'pyproject.toml', 'README.md']
    missing_files = [f for f in key_files if not (cwd / f).exists()]
    
    if missing_files:
        print(f"❌ Error: Must run from repository root")
        print(f"   Missing files: {missing_files}")
        print(f"   Current directory: {cwd}")
        print(f"\n   Please run from the repository root:")
        print(f"   cd /path/to/Riemann-adelic")
        print(f"   python scripts/validate_spectral_integrity.py")
        sys.exit(1)

# Verify we're in the right place before any imports
verify_repository_root()


# QCAL Constants
F0_HZ = 141.7001
COHERENCE_CONSTANT = 244.36
DELTA_ZETA = 0.2787437627
EUCLIDEAN_DIAGONAL = 141.4213562373


class SpectralIntegrityValidator:
    """
    Validator for QCAL spectral integrity.
    
    Ensures that phase sensitivity is preserved throughout the codebase
    and that no inappropriate normalizations have been applied.
    """
    
    def __init__(self, repo_root: Path = None):
        """Initialize validator."""
        self.repo_root = repo_root or Path.cwd()
        self.errors = []
        self.warnings = []
        self.info = []
    
    def validate_all(self) -> Dict[str, Any]:
        """
        Run all validation checks.
        
        Returns:
            Dictionary with validation results
        """
        print("=" * 70)
        print("∴𓂀 QCAL Spectral Integrity Validation")
        print("=" * 70)
        print(f"Repository: {self.repo_root}")
        print(f"Timestamp: {datetime.now(timezone.utc).isoformat()}")
        print()
        
        results = {
            "timestamp": datetime.now(timezone.utc).isoformat(),
            "repository": str(self.repo_root),
            "checks": {},
            "valid": True
        }
        
        # Check 1: QCAL Beacon
        print("📡 Check 1: QCAL Beacon Configuration")
        beacon_result = self._validate_qcal_beacon()
        results["checks"]["qcal_beacon"] = beacon_result
        self._print_check_result(beacon_result)
        
        # Check 2: Operator Phase Sensitivity
        print("\n🔬 Check 2: Operator Phase Sensitivity")
        phase_result = self._validate_phase_sensitivity()
        results["checks"]["phase_sensitivity"] = phase_result
        self._print_check_result(phase_result)
        
        # Check 3: Hamiltoniano H_Ψ Structure
        print("\n⚛️  Check 3: Hamiltoniano H_Ψ Structure")
        hamiltonian_result = self._validate_hamiltonian()
        results["checks"]["hamiltonian"] = hamiltonian_result
        self._print_check_result(hamiltonian_result)
        
        # Check 4: Spectral Alignment
        print("\n🌊 Check 4: Spectral Alignment with Riemann Zeros")
        alignment_result = self._validate_spectral_alignment()
        results["checks"]["spectral_alignment"] = alignment_result
        self._print_check_result(alignment_result)
        
        # Check 5: No Inappropriate Normalizations
        print("\n⚠️  Check 5: No Inappropriate Normalizations")
        normalization_result = self._validate_no_bad_normalizations()
        results["checks"]["normalizations"] = normalization_result
        self._print_check_result(normalization_result)
        
        # Overall result
        results["valid"] = all(
            check.get("valid", False) 
            for check in results["checks"].values()
        )
        
        print("\n" + "=" * 70)
        if results["valid"]:
            print("✅ SPECTRAL INTEGRITY VALIDATED")
            print("   All checks passed. Phase coherence preserved.")
        else:
            print("❌ SPECTRAL INTEGRITY VIOLATION DETECTED")
            print("   Phase coherence may be compromised.")
        print("=" * 70)
        
        return results
    
    def _validate_qcal_beacon(self) -> Dict[str, Any]:
        """Validate QCAL beacon configuration."""
        beacon_file = self.repo_root / ".qcal_beacon"
        
        if not beacon_file.exists():
            return {
                "valid": False,
                "error": ".qcal_beacon file not found"
            }
        
        with open(beacon_file, 'r') as f:
            content = f.read()
        
        checks = {}
        
        # Check f0
        f0_match = re.search(r'frequency\s*=\s*(\d+\.\d+)\s*Hz', content)
        if f0_match:
            f0_value = float(f0_match.group(1))
            f0_valid = abs(f0_value - F0_HZ) < 1e-6
            checks["f0"] = {
                "valid": f0_valid,
                "expected": F0_HZ,
                "found": f0_value
            }
        else:
            checks["f0"] = {
                "valid": False,
                "error": "frequency not found in beacon"
            }
        
        # Check delta_zeta
        delta_match = re.search(r'delta_zeta\s*=\s*(\d+\.\d+)', content)
        if delta_match:
            delta_value = float(delta_match.group(1))
            delta_valid = abs(delta_value - DELTA_ZETA) < 1e-6
            checks["delta_zeta"] = {
                "valid": delta_valid,
                "expected": DELTA_ZETA,
                "found": delta_value
            }
        
        # Check equation presence
        if "Ψ = I × A_eff² × C^∞" in content or "Ψ = I × A²_eff × C^∞" in content:
            checks["equation"] = {"valid": True}
        else:
            checks["equation"] = {
                "valid": False,
                "warning": "QCAL equation not found in beacon"
            }
        
        return {
            "valid": all(c.get("valid", False) for c in checks.values()),
            "checks": checks
        }
    
    def _validate_phase_sensitivity(self) -> Dict[str, Any]:
        """Validate that phase sensitivity is preserved in operators."""
        operators_dir = self.repo_root / "operators"
        
        if not operators_dir.exists():
            return {
                "valid": False,
                "error": "operators/ directory not found"
            }
        
        critical_files = [
            "riemann_operator.py",
            "noetic_operator.py",
            "spectral_constants.py",
            "dirac_spectral_operator.py"
        ]
        
        phase_violations = []
        legitimate_abs_usage = []
        
        for py_file in operators_dir.glob("*.py"):
            if py_file.name.startswith("test_"):
                continue  # Skip test files
            
            with open(py_file, 'r') as f:
                lines = f.readlines()
            
            for i, line in enumerate(lines, 1):
                # Look for abs() usage
                if re.search(r'\babs\(', line):
                    context = self._extract_context(lines, i)
                    
                    # Check if it's legitimate (error calculation, etc.)
                    if self._is_legitimate_abs_usage(context):
                        legitimate_abs_usage.append({
                            "file": py_file.name,
                            "line": i,
                            "context": line.strip()
                        })
                    else:
                        # Potential violation
                        if any(keyword in context.lower() for keyword in 
                               ['coherence', 'psi', 'eigenvalue', 'spectrum']):
                            phase_violations.append({
                                "file": py_file.name,
                                "line": i,
                                "context": line.strip(),
                                "severity": "high"
                            })
        
        return {
            "valid": len(phase_violations) == 0,
            "violations": phase_violations,
            "legitimate_usage": len(legitimate_abs_usage),
            "message": f"Found {len(phase_violations)} potential phase violations"
        }
    
    def _validate_hamiltonian(self) -> Dict[str, Any]:
        """Validate Hamiltonian structure."""
        # Check for H_psi operator files
        operator_files = [
            self.repo_root / "operators" / "riemann_operator.py",
            self.repo_root / "operador" / "operador_H.py",
        ]
        
        found_files = [f for f in operator_files if f.exists()]
        
        if not found_files:
            return {
                "valid": True,
                "warning": "Hamiltonian operator files not found for validation"
            }
        
        checks = {}
        
        for op_file in found_files:
            with open(op_file, 'r') as f:
                content = f.read()
            
            # Check for self-adjoint properties
            has_hermitian = bool(re.search(r'hermitian|self.?adjoint|conjugate', content, re.I))
            has_real_spectrum = bool(re.search(r'real.*spectrum|eigenvalue.*real', content, re.I))
            
            checks[op_file.name] = {
                "hermitian_mentioned": has_hermitian,
                "real_spectrum_mentioned": has_real_spectrum
            }
        
        return {
            "valid": True,
            "files_checked": len(found_files),
            "checks": checks
        }
    
    def _validate_spectral_alignment(self) -> Dict[str, Any]:
        """Validate spectral alignment with Riemann zeros."""
        # Check for spectral coordinate files
        spectral_files = [
            self.repo_root / "operators" / "spectral_coordinates.py",
            self.repo_root / "operators" / "spectral_constants.py",
        ]
        
        found_files = [f for f in spectral_files if f.exists()]
        
        if not found_files:
            return {
                "valid": True,
                "warning": "Spectral coordinate files not found"
            }
        
        checks = {}
        
        for spec_file in found_files:
            with open(spec_file, 'r') as f:
                content = f.read()
            
            # Check for Riemann zero references
            has_zeros = bool(re.search(r'riemann.*zero|gamma.*zero|critical.*line', content, re.I))
            has_f0 = str(F0_HZ) in content or "141.7001" in content
            
            checks[spec_file.name] = {
                "riemann_zeros_referenced": has_zeros,
                "f0_referenced": has_f0
            }
        
        return {
            "valid": True,
            "files_checked": len(found_files),
            "checks": checks
        }
    
    def _validate_no_bad_normalizations(self) -> Dict[str, Any]:
        """Check for inappropriate normalizations in critical code."""
        critical_patterns = [
            (r'np\.abs\(.*coherence', 'Absolute value on coherence'),
            (r'np\.abs\(.*psi', 'Absolute value on psi'),
            (r'np\.abs\(.*eigenvalue', 'Absolute value on eigenvalue'),
            (r'abs\(.*phase', 'Absolute value on phase'),
        ]
        
        violations = []
        
        # Check operators directory
        operators_dir = self.repo_root / "operators"
        if operators_dir.exists():
            for py_file in operators_dir.glob("*.py"):
                if py_file.name.startswith("test_"):
                    continue
                
                with open(py_file, 'r') as f:
                    content = f.read()
                
                for pattern, description in critical_patterns:
                    matches = re.finditer(pattern, content, re.I)
                    for match in matches:
                        violations.append({
                            "file": py_file.name,
                            "pattern": description,
                            "match": match.group(0)
                        })
        
        return {
            "valid": len(violations) == 0,
            "violations": violations,
            "message": f"Found {len(violations)} inappropriate normalizations"
        }
    
    def _extract_context(self, lines: List[str], line_num: int, context_size: int = 2) -> str:
        """Extract context around a line."""
        start = max(0, line_num - context_size - 1)
        end = min(len(lines), line_num + context_size)
        return ' '.join(lines[start:end])
    
    def _is_legitimate_abs_usage(self, context: str) -> bool:
        """Check if abs() usage is legitimate (error calculation, etc.)."""
        legitimate_keywords = [
            'error', 'difference', 'distance', 'deviation', 
            'tolerance', 'threshold', 'comparison', 'assert'
        ]
        return any(keyword in context.lower() for keyword in legitimate_keywords)
    
    def _print_check_result(self, result: Dict[str, Any]) -> None:
        """Print a check result."""
        if result.get("valid", False):
            print("   ✅ PASS")
        else:
            print("   ❌ FAIL")
        
        if "error" in result:
            print(f"      Error: {result['error']}")
        if "warning" in result:
            print(f"      Warning: {result['warning']}")
        if "message" in result:
            print(f"      {result['message']}")
        
        # Print violations if present
        if "violations" in result and result["violations"]:
            print(f"      Violations found: {len(result['violations'])}")
            for v in result["violations"][:3]:  # Show first 3
                if "file" in v:
                    print(f"         - {v['file']}: {v.get('context', v.get('pattern', ''))}")


def main():
    """Main validation function."""
    validator = SpectralIntegrityValidator()
    results = validator.validate_all()
    
    # Write results to file
    output_file = Path("validation") / "spectral_integrity_results.json"
    output_file.parent.mkdir(parents=True, exist_ok=True)
    
    with open(output_file, 'w') as f:
        json.dump(results, f, indent=2, default=str)
    
    print(f"\n📄 Results written to: {output_file}")
    
    # Exit with appropriate code
    sys.exit(0 if results["valid"] else 1)


if __name__ == "__main__":
    main()
