#!/usr/bin/env python3
"""
Lean-REPL Sandbox - Iterative Lean4 Proof Validation

This module provides an isolated environment for testing Lean4 proofs with
automatic error feedback and iterative correction.

Part of the Phoenix Solver system for automated sorry resolution.

Author: QCAL Phoenix Solver System
Date: 2026-01-18
"""

import subprocess
import tempfile
import re
from pathlib import Path
from typing import Optional, Tuple, List
from dataclasses import dataclass


@dataclass
class CompilationResult:
    """Result of a Lean compilation attempt."""
    success: bool
    stdout: str
    stderr: str
    errors: List[str]
    warnings: List[str]


class LeanSandbox:
    """Sandbox environment for testing Lean4 proofs."""
    
    def __init__(self, lean_executable: str = "lake"):
        """Initialize the Lean sandbox.
        
        Args:
            lean_executable: Path to the Lean executable (default: 'lake')
        """
        self.lean_executable = lean_executable
        self.temp_dir = None
        
    def validate_proof(self, lean_code: str, max_iterations: int = 5) -> CompilationResult:
        """Validate a Lean proof with iterative error correction.
        
        Args:
            lean_code: The Lean code to validate
            max_iterations: Maximum number of correction iterations
            
        Returns:
            CompilationResult with final status
        """
        current_code = lean_code
        
        for iteration in range(max_iterations):
            print(f"\n=== Iteration {iteration + 1}/{max_iterations} ===")
            
            result = self._compile_lean_code(current_code)
            
            if result.success:
                print("✅ Compilation successful!")
                return result
            
            print(f"❌ Compilation failed with {len(result.errors)} errors")
            
            # Extract and display errors
            for i, error in enumerate(result.errors[:3], 1):  # Show first 3
                print(f"\nError {i}:")
                print(error)
            
            # In a real implementation, this would call an AI service
            # to correct the code based on error messages
            # For now, we just return the result
            if iteration < max_iterations - 1:
                print("\n⚠️ Auto-correction not implemented yet")
                print("Would call AI service here to fix errors...")
            
            break  # Exit for now since we don't have auto-correction
        
        return result
    
    def _compile_lean_code(self, lean_code: str) -> CompilationResult:
        """Compile Lean code and return results.
        
        Args:
            lean_code: The Lean code to compile
            
        Returns:
            CompilationResult with compilation status
        """
        # Create a temporary directory for the test
        with tempfile.TemporaryDirectory() as tmp_dir:
            tmp_path = Path(tmp_dir)
            lean_file = tmp_path / "Test.lean"
            
            # Write the Lean code
            lean_file.write_text(lean_code, encoding='utf-8')
            
            # Try to compile with lean4
            result = self._run_lean_check(lean_file)
            
            return result
    
    def _run_lean_check(self, lean_file: Path) -> CompilationResult:
        """Run Lean type checker on a file.
        
        Args:
            lean_file: Path to the Lean file
            
        Returns:
            CompilationResult
        """
        try:
            # Try using 'lean' directly for type checking
            cmd = ['lean', str(lean_file)]
            
            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=30,
                cwd=lean_file.parent
            )
            
            # Parse output
            errors = self._parse_errors(result.stderr)
            warnings = self._parse_warnings(result.stderr)
            
            success = result.returncode == 0 and len(errors) == 0
            
            return CompilationResult(
                success=success,
                stdout=result.stdout,
                stderr=result.stderr,
                errors=errors,
                warnings=warnings
            )
            
        except FileNotFoundError:
            # Lean not installed
            return CompilationResult(
                success=False,
                stdout="",
                stderr="Lean executable not found. Please install Lean4.",
                errors=["Lean executable not found"],
                warnings=[]
            )
        except subprocess.TimeoutExpired:
            return CompilationResult(
                success=False,
                stdout="",
                stderr="Compilation timeout",
                errors=["Compilation timed out after 30 seconds"],
                warnings=[]
            )
        except Exception as e:
            return CompilationResult(
                success=False,
                stdout="",
                stderr=str(e),
                errors=[f"Unexpected error: {str(e)}"],
                warnings=[]
            )
    
    def _parse_errors(self, stderr: str) -> List[str]:
        """Parse error messages from Lean stderr.
        
        Args:
            stderr: Standard error output from Lean
            
        Returns:
            List of error messages
        """
        errors = []
        
        # Look for error patterns
        error_pattern = r'error:.*?(?=\n\n|\nerror:|\nwarning:|\Z)'
        matches = re.finditer(error_pattern, stderr, re.DOTALL)
        
        for match in matches:
            errors.append(match.group(0).strip())
        
        # Also look for simple 'error' lines
        for line in stderr.split('\n'):
            if line.strip().startswith('error'):
                if not any(line in e for e in errors):
                    errors.append(line.strip())
        
        return errors
    
    def _parse_warnings(self, stderr: str) -> List[str]:
        """Parse warning messages from Lean stderr.
        
        Args:
            stderr: Standard error output from Lean
            
        Returns:
            List of warning messages
        """
        warnings = []
        
        # Look for warning patterns
        warning_pattern = r'warning:.*?(?=\n\n|\nerror:|\nwarning:|\Z)'
        matches = re.finditer(warning_pattern, stderr, re.DOTALL)
        
        for match in matches:
            warnings.append(match.group(0).strip())
        
        return warnings
    
    def test_lean_installation(self) -> bool:
        """Test if Lean4 is properly installed.
        
        Returns:
            True if Lean is available, False otherwise
        """
        try:
            result = subprocess.run(
                ['lean', '--version'],
                capture_output=True,
                text=True,
                timeout=5
            )
            
            if result.returncode == 0:
                print(f"✅ Lean found: {result.stdout.strip()}")
                return True
            else:
                print("❌ Lean command failed")
                return False
                
        except FileNotFoundError:
            print("❌ Lean not found. Please install Lean4.")
            return False
        except Exception as e:
            print(f"❌ Error checking Lean: {e}")
            return False
    
    def validate_file(self, file_path: Path) -> CompilationResult:
        """Validate an existing Lean file.
        
        Args:
            file_path: Path to the Lean file to validate
            
        Returns:
            CompilationResult
        """
        if not file_path.exists():
            return CompilationResult(
                success=False,
                stdout="",
                stderr=f"File not found: {file_path}",
                errors=[f"File not found: {file_path}"],
                warnings=[]
            )
        
        return self._run_lean_check(file_path)
    
    def extract_error_feedback(self, result: CompilationResult) -> str:
        """Extract actionable feedback from compilation errors.
        
        Args:
            result: CompilationResult from a failed compilation
            
        Returns:
            Formatted feedback string for AI correction
        """
        if result.success:
            return "Compilation successful - no errors to report."
        
        feedback_parts = []
        feedback_parts.append("=== Compilation Errors ===\n")
        
        for i, error in enumerate(result.errors, 1):
            feedback_parts.append(f"Error {i}:")
            feedback_parts.append(error)
            feedback_parts.append("")
            
            # Try to extract specific error types
            if "unknown identifier" in error.lower():
                feedback_parts.append("💡 Suggestion: Check if all identifiers are imported or defined")
            elif "type mismatch" in error.lower():
                feedback_parts.append("💡 Suggestion: Verify type signatures match expected types")
            elif "tactic" in error.lower():
                feedback_parts.append("💡 Suggestion: Check tactic syntax and availability")
            
            feedback_parts.append("")
        
        if result.warnings:
            feedback_parts.append("\n=== Warnings ===\n")
            for i, warning in enumerate(result.warnings, 1):
                feedback_parts.append(f"Warning {i}: {warning}")
        
        return '\n'.join(feedback_parts)


def main():
    """Main entry point for the Lean sandbox."""
    import argparse
    
    parser = argparse.ArgumentParser(description='Lean4 proof validation sandbox')
    parser.add_argument('--test-installation', action='store_true',
                       help='Test Lean installation')
    parser.add_argument('--file', type=Path,
                       help='Validate a specific Lean file')
    parser.add_argument('--code', type=str,
                       help='Validate Lean code string')
    
    args = parser.parse_args()
    
    sandbox = LeanSandbox()
    
    if args.test_installation:
        sandbox.test_lean_installation()
        return
    
    if args.file:
        print(f"\nValidating file: {args.file}")
        result = sandbox.validate_file(args.file)
        print(f"\nResult: {'✅ Success' if result.success else '❌ Failed'}")
        if not result.success:
            print(sandbox.extract_error_feedback(result))
        return
    
    if args.code:
        print("\nValidating Lean code...")
        result = sandbox.validate_proof(args.code)
        print(f"\nResult: {'✅ Success' if result.success else '❌ Failed'}")
        if not result.success:
            print(sandbox.extract_error_feedback(result))
        return
    
    # Default: test installation
    sandbox.test_lean_installation()


if __name__ == '__main__':
    main()
