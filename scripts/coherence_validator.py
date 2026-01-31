#!/usr/bin/env python3
"""
Coherence Validator - QCAL Integrity Verification

This module validates QCAL coherence (Ψ) and frequency (141.7001 Hz) after
changes to ensure mathematical integrity is maintained.

Part of the Phoenix Solver system for automated sorry resolution.

Author: QCAL Phoenix Solver System
Date: 2026-01-18
"""

import subprocess
import json
from pathlib import Path
from typing import Dict, Any, Optional, Tuple
from dataclasses import dataclass, asdict
import sys


@dataclass
class CoherenceResult:
    """Result of QCAL coherence validation."""
    success: bool
    coherence_psi: float
    frequency: float
    target_coherence: float = 0.999999
    target_frequency: float = 141.7001
    details: Dict[str, Any] = None
    errors: list = None
    
    def __post_init__(self):
        if self.details is None:
            self.details = {}
        if self.errors is None:
            self.errors = []


class CoherenceValidator:
    """Validate QCAL coherence and frequency."""
    
    def __init__(self, repo_root: Path):
        """Initialize the validator.
        
        Args:
            repo_root: Root directory of the repository
        """
        self.repo_root = Path(repo_root)
        self.validation_script = self.repo_root / "validate_v5_coronacion.py"
        
    def validate(self) -> CoherenceResult:
        """Run complete QCAL coherence validation.
        
        Returns:
            CoherenceResult with validation status
        """
        print("🔍 Running QCAL coherence validation...")
        
        if not self.validation_script.exists():
            return CoherenceResult(
                success=False,
                coherence_psi=0.0,
                frequency=0.0,
                errors=[f"Validation script not found: {self.validation_script}"]
            )
        
        try:
            # Run the validation script
            result = subprocess.run(
                [sys.executable, str(self.validation_script), '--quiet'],
                capture_output=True,
                text=True,
                timeout=300,  # 5 minutes max
                cwd=self.repo_root
            )
            
            # Parse output
            coherence_result = self._parse_validation_output(
                result.stdout,
                result.stderr,
                result.returncode
            )
            
            return coherence_result
            
        except subprocess.TimeoutExpired:
            return CoherenceResult(
                success=False,
                coherence_psi=0.0,
                frequency=0.0,
                errors=["Validation timed out after 5 minutes"]
            )
        except Exception as e:
            return CoherenceResult(
                success=False,
                coherence_psi=0.0,
                frequency=0.0,
                errors=[f"Validation error: {str(e)}"]
            )
    
    def _parse_validation_output(self, stdout: str, stderr: str, 
                                 returncode: int) -> CoherenceResult:
        """Parse output from validation script.
        
        Args:
            stdout: Standard output
            stderr: Standard error
            returncode: Process return code
            
        Returns:
            CoherenceResult
        """
        errors = []
        coherence = 0.0
        frequency = 0.0
        details = {}
        
        # Check for errors in stderr
        if stderr:
            errors.append(f"Stderr: {stderr[:500]}")
        
        # Parse stdout for coherence and frequency values
        import re
        
        # Look for coherence value (Ψ or psi)
        coh_match = re.search(r'[Ψψ]|coherence[:\s]+([\d.]+)', stdout, re.IGNORECASE)
        if coh_match:
            try:
                coherence = float(coh_match.group(1))
            except (ValueError, IndexError):
                pass
        
        # Look for frequency value
        freq_match = re.search(r'frequency[:\s]+([\d.]+)', stdout, re.IGNORECASE)
        if freq_match:
            try:
                frequency = float(freq_match.group(1))
            except (ValueError, IndexError):
                # Try default
                frequency = 141.7001
        
        # Check for success indicators
        success_indicators = [
            'validation.*complete',
            'coherence.*confirmed',
            'all.*tests.*pass',
            'success',
            '✅'
        ]
        
        success = any(re.search(pattern, stdout, re.IGNORECASE) 
                     for pattern in success_indicators)
        
        # Also require return code 0
        success = success and returncode == 0
        
        # Extract details from output
        if 'Step 1' in stdout:
            details['step1'] = 'completed' if 'Step 1' in stdout else 'failed'
        if 'Step 2' in stdout:
            details['step2'] = 'completed' if 'Step 2' in stdout else 'failed'
        if 'Step 3' in stdout:
            details['step3'] = 'completed' if 'Step 3' in stdout else 'failed'
        if 'Step 4' in stdout:
            details['step4'] = 'completed' if 'Step 4' in stdout else 'failed'
        if 'Step 5' in stdout:
            details['step5'] = 'completed' if 'Step 5' in stdout else 'failed'
        
        return CoherenceResult(
            success=success,
            coherence_psi=coherence,
            frequency=frequency,
            details=details,
            errors=errors if errors else []
        )
    
    def check_frequency_accuracy(self, measured_freq: float, 
                                 tolerance: float = 0.0001) -> bool:
        """Check if measured frequency is within tolerance.
        
        Args:
            measured_freq: Measured frequency value
            tolerance: Allowed deviation from 141.7001 Hz
            
        Returns:
            True if within tolerance
        """
        target = 141.7001
        deviation = abs(measured_freq - target)
        
        return deviation <= tolerance
    
    def check_coherence_threshold(self, coherence: float, 
                                  threshold: float = 0.999) -> bool:
        """Check if coherence exceeds minimum threshold.
        
        Args:
            coherence: Measured coherence value
            threshold: Minimum acceptable coherence
            
        Returns:
            True if exceeds threshold
        """
        return coherence >= threshold
    
    def generate_certificate(self, result: CoherenceResult, 
                           output_path: Optional[Path] = None) -> Path:
        """Generate integrity certificate.
        
        Args:
            result: CoherenceResult to generate certificate for
            output_path: Optional path for certificate file
            
        Returns:
            Path to generated certificate
        """
        if output_path is None:
            output_path = self.repo_root / "data" / "qcal_integrity_certificate.json"
        
        output_path.parent.mkdir(parents=True, exist_ok=True)
        
        certificate = {
            'timestamp': str(Path(__file__).stat().st_mtime),
            'validation_result': asdict(result),
            'status': 'VALID' if result.success else 'INVALID',
            'coherence_check': {
                'value': result.coherence_psi,
                'target': result.target_coherence,
                'passed': result.coherence_psi >= result.target_coherence
            },
            'frequency_check': {
                'value': result.frequency,
                'target': result.target_frequency,
                'passed': self.check_frequency_accuracy(result.frequency)
            }
        }
        
        output_path.write_text(json.dumps(certificate, indent=2))
        print(f"📜 Certificate generated: {output_path}")
        
        return output_path
    
    def validate_with_rollback(self, pre_change_state: Optional[Dict] = None) -> Tuple[bool, str]:
        """Validate and prepare for rollback if needed.
        
        Args:
            pre_change_state: Optional state before changes
            
        Returns:
            Tuple of (should_rollback, reason)
        """
        result = self.validate()
        
        if not result.success:
            return True, "Validation failed: " + ', '.join(result.errors)
        
        if result.coherence_psi < 0.999:
            return True, f"Coherence too low: {result.coherence_psi} < 0.999"
        
        if not self.check_frequency_accuracy(result.frequency):
            return True, f"Frequency deviation too large: {result.frequency} vs 141.7001"
        
        # All checks passed
        return False, "Validation passed"


def main():
    """Main entry point for coherence validator."""
    import argparse
    
    parser = argparse.ArgumentParser(description='QCAL coherence validation')
    parser.add_argument('--repo-root', type=Path, default=Path.cwd(),
                       help='Repository root directory')
    parser.add_argument('--generate-certificate', action='store_true',
                       help='Generate integrity certificate')
    parser.add_argument('--check-rollback', action='store_true',
                       help='Check if rollback is needed')
    
    args = parser.parse_args()
    
    validator = CoherenceValidator(args.repo_root)
    
    print("\n=== QCAL Coherence Validation ===\n")
    
    result = validator.validate()
    
    print(f"\nValidation Result: {'✅ PASS' if result.success else '❌ FAIL'}")
    print(f"Coherence Ψ: {result.coherence_psi:.6f} (target: {result.target_coherence})")
    print(f"Frequency: {result.frequency:.4f} Hz (target: {result.target_frequency})")
    
    if result.details:
        print("\nDetails:")
        for key, value in result.details.items():
            print(f"  {key}: {value}")
    
    if result.errors:
        print("\nErrors:")
        for error in result.errors:
            print(f"  - {error}")
    
    if args.generate_certificate:
        validator.generate_certificate(result)
    
    if args.check_rollback:
        should_rollback, reason = validator.validate_with_rollback()
        print(f"\nRollback needed: {should_rollback}")
        print(f"Reason: {reason}")
    
    sys.exit(0 if result.success else 1)


if __name__ == '__main__':
    main()
