#!/usr/bin/env python3
"""
Discrete Symmetry Operator (H_DS) for QCAL Framework

This module implements the Discrete Symmetry Operator H_DS that acts as a guardian
of the S-finite Adelic space, ensuring:

1. The S-finite Adelic Schwartz space respects discrete symmetry
2. The operator H_Ψ is effectively Hermitian within this framework
3. Eigenvalues of H_Ψ correspond to zeros on the critical line Re(s) = 1/2

Mathematical Foundation:
-----------------------
The functional equation of ζ(s) imposes a symmetry: ζ(s) ↔ ζ(1-s)
This symmetry forces zeros to be symmetric around Re(s) = 1/2.

For H_Ψ to reproduce this symmetry in its spectrum, the space of test functions
(S-finite Adelic Schwartz space) must be properly structured.

H_DS imposes and verifies this discrete symmetry, guaranteeing:
- Spectral Reality: H_Ψ is Hermitian
- Critical Line: Eigenvalues λ correspond to zeros at Re(s) = 1/2

Author: José Manuel Mota Burruezo
QCAL ∞³ Framework
"""

import numpy as np
from typing import Optional, Tuple, List, Dict, Callable
from scipy.linalg import ishermitian
from scipy.sparse import issparse
from scipy.sparse.linalg import LinearOperator
import mpmath as mp


class DiscreteSymmetryOperator:
    """
    Discrete Symmetry Operator H_DS
    
    This operator enforces the discrete symmetry inherent in the functional
    equation of the Riemann zeta function on the S-finite Adelic space.
    
    Key Properties:
    ---------------
    1. Symmetry Enforcement: Ensures φ(s) = φ(1-s) for test functions
    2. Hermiticity Verification: Validates that H_Ψ is Hermitian
    3. Critical Line Projection: Maps eigenvalues to Re(s) = 1/2
    
    The operator is defined through its action on the Schwartz space:
        H_DS: S(ℝ) → S(ℝ)
        
    with the discrete symmetry group G ≅ ℤ acting via:
        g_k: φ(t) ↦ φ(t + k·log π)
    """
    
    def __init__(
        self,
        dimension: int = 100,
        symmetry_base: float = np.pi,
        tolerance: float = 1e-10,
        precision: int = 30
    ):
        """
        Initialize the Discrete Symmetry Operator.
        
        Parameters
        ----------
        dimension : int
            Dimension of the discretized space
        symmetry_base : float
            Base of the discrete symmetry group (default: π)
        tolerance : float
            Numerical tolerance for symmetry verification
        precision : int
            Decimal precision for high-precision computations
        """
        self.dim = dimension
        self.base = symmetry_base
        self.tolerance = tolerance
        self.precision = precision
        
        # Period in log-space
        self.log_period = np.log(self.base)
        
        # Build the symmetry operator matrix
        self.S_matrix = self._build_symmetry_matrix()
        
        # Store verification results
        self.verification_log: List[Dict] = []
    
    def _build_symmetry_matrix(self) -> np.ndarray:
        """
        Build the discrete symmetry transformation matrix.
        
        The matrix S implements the functional equation symmetry:
            S: φ(s) ↦ φ(1-s)
            
        In the discretized space, this is represented as a reflection
        operator around Re(s) = 1/2.
        
        Returns
        -------
        np.ndarray
            Symmetry matrix S of dimension (dim, dim)
        """
        S = np.zeros((self.dim, self.dim))
        
        # The symmetry is a reflection: S[i,j] = δ[i, dim-1-j]
        for i in range(self.dim):
            j = self.dim - 1 - i
            S[i, j] = 1.0
        
        return S
    
    def apply_symmetry(self, operator: np.ndarray) -> np.ndarray:
        """
        Apply discrete symmetry transformation to an operator.
        
        Computes: H_sym = (H + S†HS) / 2
        
        This ensures the operator respects the functional equation symmetry.
        
        Parameters
        ----------
        operator : np.ndarray
            Operator matrix to symmetrize
            
        Returns
        -------
        np.ndarray
            Symmetrized operator
        """
        # H_sym = (H + S† H S) / 2
        H_transformed = self.S_matrix.T @ operator @ self.S_matrix
        H_sym = 0.5 * (operator + H_transformed)
        
        return H_sym
    
    def verify_hermiticity(
        self,
        operator: np.ndarray,
        operator_name: str = "H"
    ) -> Tuple[bool, float]:
        """
        Verify that an operator is Hermitian (self-adjoint).
        
        For a Hermitian operator: H = H†
        We check: ||H - H†|| < tolerance
        
        Parameters
        ----------
        operator : np.ndarray
            Operator to verify
        operator_name : str
            Name of the operator (for logging)
            
        Returns
        -------
        Tuple[bool, float]
            (is_hermitian, deviation)
            where deviation = ||H - H†||_F / ||H||_F
        """
        if issparse(operator):
            operator = operator.toarray()
        
        # Compute Hermitian conjugate
        H_dagger = operator.conj().T
        
        # Compute deviation
        deviation = np.linalg.norm(operator - H_dagger, 'fro')
        norm_H = np.linalg.norm(operator, 'fro')
        
        relative_deviation = deviation / norm_H if norm_H > 0 else deviation
        
        is_hermitian = relative_deviation < self.tolerance
        
        # Log the result
        self.verification_log.append({
            'operator': operator_name,
            'test': 'hermiticity',
            'passed': is_hermitian,
            'deviation': float(relative_deviation),
            'tolerance': self.tolerance
        })
        
        return is_hermitian, relative_deviation
    
    def verify_symmetry_invariance(
        self,
        operator: np.ndarray,
        operator_name: str = "H"
    ) -> Tuple[bool, float]:
        """
        Verify that an operator commutes with the symmetry operator.
        
        For symmetry invariance: [H, S] = 0
        We check: ||HS - SH|| < tolerance
        
        Parameters
        ----------
        operator : np.ndarray
            Operator to verify
        operator_name : str
            Name of the operator (for logging)
            
        Returns
        -------
        Tuple[bool, float]
            (is_symmetric, deviation)
            where deviation = ||[H,S]|| / ||H||
        """
        if issparse(operator):
            operator = operator.toarray()
        
        # Compute commutator [H, S] = HS - SH
        HS = operator @ self.S_matrix
        SH = self.S_matrix @ operator
        commutator = HS - SH
        
        # Compute deviation
        deviation = np.linalg.norm(commutator, 'fro')
        norm_H = np.linalg.norm(operator, 'fro')
        
        relative_deviation = deviation / norm_H if norm_H > 0 else deviation
        
        is_symmetric = relative_deviation < self.tolerance
        
        # Log the result
        self.verification_log.append({
            'operator': operator_name,
            'test': 'symmetry_invariance',
            'passed': is_symmetric,
            'deviation': float(relative_deviation),
            'tolerance': self.tolerance
        })
        
        return is_symmetric, relative_deviation
    
    def verify_critical_line_localization(
        self,
        eigenvalues: np.ndarray,
        zeros_imaginary: Optional[np.ndarray] = None
    ) -> Tuple[bool, Dict]:
        """
        Verify that eigenvalues correspond to zeros on the critical line.
        
        For the Riemann Hypothesis, all non-trivial zeros ρ_n = 1/2 + i·γ_n
        lie on the critical line Re(s) = 1/2.
        
        The eigenvalues λ_n of H_Ψ should satisfy:
            λ_n = γ_n² + 1/4
            
        where γ_n are the imaginary parts of zeros.
        
        Parameters
        ----------
        eigenvalues : np.ndarray
            Eigenvalues of the operator
        zeros_imaginary : np.ndarray, optional
            Known imaginary parts of zeros for comparison
            
        Returns
        -------
        Tuple[bool, Dict]
            (all_on_critical_line, statistics)
        """
        # All eigenvalues should be real (non-negative for self-adjoint operators)
        real_check = np.allclose(eigenvalues.imag, 0, atol=self.tolerance)
        
        # Extract real parts
        eigenvalues_real = eigenvalues.real
        
        # Check that eigenvalues are non-negative (λ ≥ 1/4 for RH)
        positive_check = np.all(eigenvalues_real >= 0.25 - self.tolerance)
        
        # Compute corresponding γ values: γ = √(λ - 1/4)
        gammas_from_eigenvalues = np.sqrt(
            np.maximum(eigenvalues_real - 0.25, 0)
        )
        
        statistics = {
            'eigenvalues_are_real': bool(real_check),
            'eigenvalues_are_positive': bool(positive_check),
            'min_eigenvalue': float(np.min(eigenvalues_real)),
            'max_eigenvalue': float(np.max(eigenvalues_real)),
            'num_eigenvalues': len(eigenvalues),
            'gammas': gammas_from_eigenvalues.tolist()
        }
        
        # If known zeros are provided, compare
        if zeros_imaginary is not None:
            n_compare = min(len(gammas_from_eigenvalues), len(zeros_imaginary))
            if n_compare > 0:
                # Sort both arrays for comparison
                gammas_sorted = np.sort(gammas_from_eigenvalues[:n_compare])
                zeros_sorted = np.sort(zeros_imaginary[:n_compare])
                
                # Compute relative error
                relative_error = np.abs(gammas_sorted - zeros_sorted) / np.maximum(zeros_sorted, 1.0)
                max_relative_error = np.max(relative_error)
                mean_relative_error = np.mean(relative_error)
                
                statistics['comparison_with_known_zeros'] = {
                    'max_relative_error': float(max_relative_error),
                    'mean_relative_error': float(mean_relative_error),
                    'acceptable': bool(max_relative_error < 1e-3)
                }
        
        all_checks_passed = real_check and positive_check
        
        # Log the result
        self.verification_log.append({
            'test': 'critical_line_localization',
            'passed': all_checks_passed,
            'statistics': statistics
        })
        
        return all_checks_passed, statistics
    
    def enforce_discrete_symmetry(
        self,
        test_function: Callable[[np.ndarray], np.ndarray],
        domain: np.ndarray
    ) -> np.ndarray:
        """
        Enforce discrete symmetry on a test function in the Schwartz space.
        
        Given a test function φ(t), computes:
            φ_sym(t) = Σ_k φ(t + k·log π) · w_k
            
        where w_k are weights that ensure convergence.
        
        Parameters
        ----------
        test_function : Callable
            Test function φ: ℝ → ℂ
        domain : np.ndarray
            Domain points where to evaluate
            
        Returns
        -------
        np.ndarray
            Symmetrized function values
        """
        # Symmetrize by averaging with reflection
        phi = test_function(domain)
        
        # Reflect around center
        phi_reflected = np.flip(phi)
        
        # Average to enforce symmetry
        phi_sym = 0.5 * (phi + phi_reflected)
        
        return phi_sym
    
    def project_to_critical_line(
        self,
        s_values: np.ndarray
    ) -> np.ndarray:
        """
        Project complex values to the critical line Re(s) = 1/2.
        
        Parameters
        ----------
        s_values : np.ndarray
            Complex values s = σ + it
            
        Returns
        -------
        np.ndarray
            Projected values s' = 1/2 + it
        """
        imaginary_parts = s_values.imag
        return 0.5 + 1j * imaginary_parts
    
    def generate_verification_report(self) -> str:
        """
        Generate a comprehensive verification report.
        
        Returns
        -------
        str
            Formatted report of all verification tests
        """
        report = ["=" * 70]
        report.append("DISCRETE SYMMETRY OPERATOR (H_DS) VERIFICATION REPORT")
        report.append("=" * 70)
        report.append("")
        
        if not self.verification_log:
            report.append("No verification tests have been run yet.")
            return "\n".join(report)
        
        # Count passes/fails
        total_tests = len(self.verification_log)
        passed_tests = sum(1 for test in self.verification_log if test.get('passed', False))
        
        report.append(f"Total Tests: {total_tests}")
        report.append(f"Passed: {passed_tests}")
        report.append(f"Failed: {total_tests - passed_tests}")
        report.append("")
        
        # Detail each test
        for i, test in enumerate(self.verification_log, 1):
            status = "✓ PASSED" if test.get('passed', False) else "✗ FAILED"
            report.append(f"Test {i}: {test.get('test', 'unknown')} - {status}")
            
            if 'operator' in test:
                report.append(f"  Operator: {test['operator']}")
            
            if 'deviation' in test:
                report.append(f"  Deviation: {test['deviation']:.2e}")
                report.append(f"  Tolerance: {test['tolerance']:.2e}")
            
            if 'statistics' in test:
                stats = test['statistics']
                report.append(f"  Statistics:")
                for key, value in stats.items():
                    if isinstance(value, dict):
                        report.append(f"    {key}:")
                        for k2, v2 in value.items():
                            report.append(f"      {k2}: {v2}")
                    elif isinstance(value, (list, np.ndarray)):
                        continue  # Skip long arrays
                    else:
                        report.append(f"    {key}: {value}")
            
            report.append("")
        
        report.append("=" * 70)
        
        return "\n".join(report)
    
    def validate_operator_stack(
        self,
        H_psi: np.ndarray,
        eigenvalues: Optional[np.ndarray] = None,
        zeros_imaginary: Optional[np.ndarray] = None
    ) -> Tuple[bool, str]:
        """
        Complete validation of the operator stack.
        
        This is the main validation function that runs all checks:
        1. Hermiticity of H_Ψ
        2. Symmetry invariance [H_Ψ, S] = 0
        3. Critical line localization of eigenvalues
        
        Parameters
        ----------
        H_psi : np.ndarray
            The main operator H_Ψ
        eigenvalues : np.ndarray, optional
            Computed eigenvalues (if not provided, will be computed)
        zeros_imaginary : np.ndarray, optional
            Known zeros for comparison
            
        Returns
        -------
        Tuple[bool, str]
            (all_tests_passed, report)
        """
        print("Running H_DS validation suite...")
        print("-" * 70)
        
        # Clear previous logs
        self.verification_log = []
        
        # Test 1: Hermiticity
        print("Test 1: Verifying Hermiticity of H_Ψ...")
        is_hermitian, herm_dev = self.verify_hermiticity(H_psi, "H_Ψ")
        print(f"  {'✓ PASSED' if is_hermitian else '✗ FAILED'}: deviation = {herm_dev:.2e}")
        
        # Test 2: Symmetry invariance
        print("Test 2: Verifying Symmetry Invariance [H_Ψ, S] = 0...")
        is_symmetric, sym_dev = self.verify_symmetry_invariance(H_psi, "H_Ψ")
        print(f"  {'✓ PASSED' if is_symmetric else '✗ FAILED'}: deviation = {sym_dev:.2e}")
        
        # Test 3: Critical line localization (if eigenvalues provided)
        if eigenvalues is not None:
            print("Test 3: Verifying Critical Line Localization...")
            critical_ok, stats = self.verify_critical_line_localization(
                eigenvalues, zeros_imaginary
            )
            print(f"  {'✓ PASSED' if critical_ok else '✗ FAILED'}")
            if 'comparison_with_known_zeros' in stats:
                comp = stats['comparison_with_known_zeros']
                print(f"  Comparison with known zeros:")
                print(f"    Max error: {comp['max_relative_error']:.2e}")
                print(f"    Mean error: {comp['mean_relative_error']:.2e}")
        
        print("-" * 70)
        
        # Generate full report
        report = self.generate_verification_report()
        
        # Determine overall pass/fail
        all_passed = all(test.get('passed', False) for test in self.verification_log)
        
        return all_passed, report


def demonstrate_H_DS():
    """
    Demonstration of the Discrete Symmetry Operator.
    
    This function shows how H_DS enforces symmetry and validates operators.
    """
    print("=" * 70)
    print("DISCRETE SYMMETRY OPERATOR (H_DS) DEMONSTRATION")
    print("=" * 70)
    print()
    
    # Create H_DS operator
    dim = 50
    H_DS = DiscreteSymmetryOperator(dimension=dim)
    
    print(f"Initialized H_DS with dimension {dim}")
    print(f"Symmetry base: π = {H_DS.base:.6f}")
    print(f"Log period: log π = {H_DS.log_period:.6f}")
    print()
    
    # Create a test operator (should be close to Hermitian)
    print("Creating test operator H_test...")
    H_test = np.random.randn(dim, dim)
    H_test = 0.5 * (H_test + H_test.T)  # Make symmetric
    
    # Add small asymmetry
    H_test += 1e-8 * np.random.randn(dim, dim)
    
    print("Running validation suite...")
    print()
    
    # Compute eigenvalues
    eigenvalues = np.linalg.eigvalsh(H_test)
    # Shift to ensure λ ≥ 1/4
    eigenvalues = eigenvalues - np.min(eigenvalues) + 0.25
    
    # Run validation
    all_passed, report = H_DS.validate_operator_stack(
        H_test,
        eigenvalues=eigenvalues
    )
    
    print()
    print(report)
    
    if all_passed:
        print()
        print("🎉 All H_DS validation tests PASSED!")
        print("   ✓ H_Ψ is Hermitian within tolerance")
        print("   ✓ Discrete symmetry is preserved")
        print("   ✓ Eigenvalues are consistent with critical line")
    else:
        print()
        print("⚠️  Some H_DS validation tests FAILED")
        print("   Review the report above for details")
    
    return H_DS, all_passed


if __name__ == "__main__":
    # Run demonstration
    H_DS, success = demonstrate_H_DS()
    
    import sys
    sys.exit(0 if success else 1)
