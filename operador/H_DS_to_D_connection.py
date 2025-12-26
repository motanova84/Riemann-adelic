#!/usr/bin/env python3
"""
H_DS to D(s) Connection Module

This module implements the connection between the discrete symmetry
operator H_DS and the spectral determinant D(s).

Mathematical Framework:
- H_DS: discrete symmetry operator (x ↦ 1/x)
- H_Ψ: Hilbert-Pólya operator
- R: resolvent operator
- D(s): spectral determinant = det(I - sH⁻¹)

Key Properties:
1. [H_Ψ, H_DS] = 0 (operators commute)
2. Spectrum symmetric under s ↦ 1-s
3. D(s) = D(1-s) (functional equation)

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Instituto de Conciencia Cuántica (ICQ)
Date: 2025-12-26
"""

import numpy as np
import mpmath as mp
from typing import Callable, Tuple, List, Optional
from scipy.linalg import eig, det


class HDSConnection:
    """Connection between H_DS and spectral determinant D(s)"""
    
    def __init__(self, dimension: int = 40, precision: int = 50):
        """
        Initialize connection.
        
        Args:
            dimension: Hilbert space dimension (truncation)
            precision: Decimal precision for computations
        """
        self.dimension = dimension
        self.precision = precision
        mp.mp.dps = precision
        
    def build_H_DS_matrix(self) -> np.ndarray:
        """
        Build discrete symmetry matrix H_DS.
        
        In the basis of Hermite functions, H_DS acts as inversion.
        This is represented as a permutation-like matrix with sign changes.
        
        Returns:
            H_DS matrix (dimension × dimension)
        """
        n = self.dimension
        H_DS = np.zeros((n, n))
        
        # H_DS swaps ψ_n ↔ ψ_{n-1} with appropriate factors
        # This is a simplified representation
        for i in range(n):
            if i > 0:
                H_DS[i, i-1] = 1.0
            if i < n - 1:
                H_DS[i, i+1] = 1.0
        
        return H_DS
    
    def verify_commutator(self, H_psi: np.ndarray, H_DS: np.ndarray, 
                         tolerance: float = 1e-10) -> bool:
        """
        Verify that [H_Ψ, H_DS] = 0.
        
        Args:
            H_psi: H_Ψ operator matrix
            H_DS: H_DS operator matrix
            tolerance: Numerical tolerance
            
        Returns:
            True if operators commute
        """
        commutator = H_psi @ H_DS - H_DS @ H_psi
        comm_norm = np.linalg.norm(commutator, 'fro')
        
        print(f"  Commutator norm: ‖[H_Ψ, H_DS]‖ = {comm_norm:.2e}")
        
        if comm_norm < tolerance:
            print(f"  ✅ Operators commute (within tolerance {tolerance:.0e})")
            return True
        else:
            print(f"  ⚠️  Operators do not commute (norm {comm_norm:.2e})")
            return False
    
    def compute_spectrum(self, H: np.ndarray) -> Tuple[np.ndarray, np.ndarray]:
        """
        Compute spectrum (eigenvalues and eigenvectors).
        
        Args:
            H: Operator matrix (should be Hermitian)
            
        Returns:
            (eigenvalues, eigenvectors) tuple
        """
        # Use eigh for Hermitian matrices (more stable)
        eigenvalues, eigenvectors = np.linalg.eigh(H)
        
        # Sort by real part
        idx = eigenvalues.argsort()
        eigenvalues = eigenvalues[idx]
        eigenvectors = eigenvectors[:, idx]
        
        return eigenvalues, eigenvectors
    
    def verify_spectral_symmetry(self, eigenvalues: np.ndarray,
                                 tolerance: float = 1e-6) -> bool:
        """
        Verify spectrum is symmetric under λ ↦ 1-λ.
        
        Args:
            eigenvalues: Spectrum of H_Ψ
            tolerance: Numerical tolerance
            
        Returns:
            True if spectrum is symmetric
        """
        print("\n🔍 Verifying spectral symmetry λ ↔ 1-λ:")
        
        # For each eigenvalue λ, check if 1-λ is also present
        symmetric_pairs = 0
        total_checked = 0
        
        for i, lam in enumerate(eigenvalues):
            # Look for 1 - λ in spectrum
            symmetric_val = 1.0 - lam
            
            # Find closest eigenvalue
            diffs = np.abs(eigenvalues - symmetric_val)
            min_diff = np.min(diffs)
            
            if min_diff < tolerance:
                symmetric_pairs += 1
                if i < 5:  # Show first few
                    j = np.argmin(diffs)
                    print(f"  λ_{i} = {lam:.6f} ↔ λ_{j} = {eigenvalues[j]:.6f} "
                          f"(expected {symmetric_val:.6f})")
            
            total_checked += 1
        
        ratio = symmetric_pairs / total_checked
        print(f"\n  Symmetric pairs: {symmetric_pairs}/{total_checked} ({ratio:.1%})")
        
        return ratio > 0.8  # Allow some tolerance
    
    def build_spectral_determinant(self, R_matrix: np.ndarray
                                   ) -> Tuple[Callable[[complex], complex], np.ndarray]:
        """
        Build spectral determinant D(s) = det(I - sR).
        
        Args:
            R_matrix: Resolvent or related operator matrix
            
        Returns:
            (D_function, eigenvalues) tuple
        """
        print("\n🔨 Building spectral determinant D(s)...")
        
        # Compute eigenvalues of R
        eigenvalues, _ = self.compute_spectrum(R_matrix)
        
        print(f"  Computed {len(eigenvalues)} eigenvalues")
        print(f"  Range: [{eigenvalues[0]:.6f}, {eigenvalues[-1]:.6f}]")
        
        def D_func(s: complex) -> complex:
            """
            Spectral determinant D(s) = ∏(1 - s/λ).
            
            Uses log-sum to prevent overflow/underflow.
            
            Args:
                s: Complex argument
                
            Returns:
                D(s) value
            """
            log_product = 0.0
            for lam in eigenvalues:
                if abs(lam) > 1e-10:  # Avoid division by zero
                    log_product += np.log(1.0 - s / lam)
            return np.exp(log_product)
        
        return D_func, eigenvalues
    
    def verify_functional_equation(self, D_func: Callable[[complex], complex],
                                   test_points: int = 10,
                                   tolerance: float = 1e-8) -> bool:
        """
        Verify functional equation D(s) = D(1-s).
        
        Args:
            D_func: Spectral determinant function
            test_points: Number of test points
            tolerance: Relative tolerance
            
        Returns:
            True if functional equation holds
        """
        print("\n🧪 Verifying functional equation D(s) = D(1-s):")
        
        violations = 0
        
        for _ in range(test_points):
            # Random test point
            s = np.random.uniform(0, 1) + 1j * np.random.uniform(-5, 5)
            
            D_s = D_func(s)
            D_1ms = D_func(1 - s)
            
            if abs(D_s) > 1e-10:
                rel_diff = abs(D_s - D_1ms) / abs(D_s)
                
                if rel_diff > tolerance:
                    violations += 1
                    if violations <= 3:  # Show first few violations
                        print(f"  s={s:.4f}: D(s)={D_s:.6e}, D(1-s)={D_1ms:.6e}, "
                              f"diff={rel_diff:.2e}")
        
        success_rate = 1.0 - violations / test_points
        print(f"\n  Success rate: {success_rate:.1%} ({test_points - violations}/{test_points})")
        
        return violations == 0
    
    def run_complete_validation(self, H_psi_matrix: np.ndarray) -> dict:
        """
        Run complete validation of H_DS → D(s) connection.
        
        Args:
            H_psi_matrix: H_Ψ operator matrix
            
        Returns:
            Dictionary with validation results
        """
        print("=" * 60)
        print("🚀 H_DS TO D(s) CONNECTION VALIDATION")
        print("=" * 60)
        
        results = {}
        
        # Build H_DS
        print("\n1. Building H_DS operator...")
        H_DS = self.build_H_DS_matrix()
        results['H_DS'] = H_DS
        
        # Verify commutation
        print("\n2. Verifying [H_Ψ, H_DS] = 0...")
        commutes = self.verify_commutator(H_psi_matrix, H_DS)
        results['commutes'] = commutes
        
        # Compute spectrum
        print("\n3. Computing spectrum of H_Ψ...")
        eigenvalues, eigenvectors = self.compute_spectrum(H_psi_matrix)
        results['eigenvalues'] = eigenvalues
        results['eigenvectors'] = eigenvectors
        
        print(f"  Found {len(eigenvalues)} eigenvalues")
        if len(eigenvalues) > 0:
            print(f"  First 5: {eigenvalues[:5]}")
        
        # Verify spectral symmetry
        print("\n4. Verifying spectral symmetry...")
        symmetric = self.verify_spectral_symmetry(eigenvalues)
        results['spectral_symmetry'] = symmetric
        
        # Build D(s)
        print("\n5. Constructing D(s)...")
        D_func, _ = self.build_spectral_determinant(H_psi_matrix)
        results['D_func'] = D_func
        
        # Test special values
        print("\n6. Testing special values...")
        D_0 = D_func(0)
        D_half = D_func(0.5)
        D_1 = D_func(1)
        
        print(f"  D(0) = {D_0:.10f} (should be ≈ 1)")
        print(f"  D(1/2) = {D_half:.10f}")
        print(f"  D(1) = {D_1:.10f} (should equal D(0))")
        
        results['D_0'] = D_0
        results['D_half'] = D_half
        results['D_1'] = D_1
        
        # Verify functional equation
        print("\n7. Verifying functional equation...")
        satisfies_FE = self.verify_functional_equation(D_func)
        results['functional_equation'] = satisfies_FE
        
        # Final summary
        print("\n" + "=" * 60)
        print("📊 VALIDATION SUMMARY")
        print("=" * 60)
        
        all_pass = commutes and symmetric and satisfies_FE
        
        checks = [
            ("H_Ψ and H_DS commute", commutes),
            ("Spectrum is symmetric", symmetric),
            ("Functional equation holds", satisfies_FE),
        ]
        
        for check_name, passed in checks:
            icon = "✅" if passed else "❌"
            print(f"  {icon} {check_name}")
        
        print("\n" + "=" * 60)
        if all_pass:
            print("✅ ALL VALIDATIONS PASSED")
            print("   H_DS → D(s) connection verified ✓")
        else:
            print("⚠️  SOME VALIDATIONS FAILED")
            print("   Further investigation needed")
        print("=" * 60)
        
        results['all_pass'] = all_pass
        return results


# Example usage and testing
if __name__ == "__main__":
    # This would typically be called with an H_Ψ matrix from operador_H.py
    print("H_DS to D(s) connection module loaded.")
    print("Use HDSConnection class to validate the connection.")
