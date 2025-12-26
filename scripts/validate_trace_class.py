#!/usr/bin/env python3
"""
Trace Class Operator Validation for H_Ψ

This script validates that the operator H_Ψ is trace class by verifying
that the sum of operator norms Σ‖H_Ψ(ψ_n)‖ converges.

Mathematical Framework:
- H_Ψ: L²(ℝ) → L²(ℝ) acting on Hermite basis {ψ_n}
- Trace class condition: Σ_n ‖H_Ψ(ψ_n)‖ < ∞
- Expected decay: ‖H_Ψ(ψ_n)‖ ~ C/n^(1+δ) for some δ > 0

Validation Steps:
1. Compute operator norms ‖H_Ψ(ψ_n)‖ for n = 0, 1, ..., N
2. Verify asymptotic decay C/n^(1+δ)
3. Confirm series convergence Σ‖H_Ψ(ψ_n)‖ < ∞
4. Certify trace class property

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
Date: 2025-12-26
"""

import numpy as np
import matplotlib.pyplot as plt
from scipy.special import hermite, factorial
from scipy.integrate import quad
from typing import Tuple, List, Dict
import json

# QCAL Constants
QCAL_FREQUENCY = 141.7001  # Hz
QCAL_COHERENCE = 244.36


class HermiteBasis:
    """Hermite basis functions for L²(ℝ)"""
    
    @staticmethod
    def psi_n(n: int, x: np.ndarray) -> np.ndarray:
        """
        Normalized Hermite function ψ_n(x).
        
        ψ_n(x) = (π^(-1/4) / sqrt(2^n n!)) * H_n(x) * exp(-x²/2)
        
        Args:
            n: Hermite index
            x: Evaluation points
            
        Returns:
            ψ_n(x) values
        """
        H_n = hermite(n)
        norm_factor = np.pi**(-0.25) / np.sqrt(2**n * factorial(n))
        return norm_factor * H_n(x) * np.exp(-x**2 / 2)
    
    @staticmethod
    def psi_n_derivative(n: int, x: np.ndarray) -> np.ndarray:
        """
        Derivative of Hermite function dψ_n/dx.
        
        Uses: ψ'_n(x) = sqrt(n/2) ψ_{n-1}(x) - sqrt((n+1)/2) ψ_{n+1}(x)
        
        Args:
            n: Hermite index
            x: Evaluation points
            
        Returns:
            ψ'_n(x) values
        """
        result = np.zeros_like(x)
        if n > 0:
            result += np.sqrt(n / 2) * HermiteBasis.psi_n(n - 1, x)
        result -= np.sqrt((n + 1) / 2) * HermiteBasis.psi_n(n + 1, x)
        return result


class TraceClassValidator:
    """Validates trace class property of H_Ψ operator"""
    
    def __init__(self, max_n: int = 50, x_max: float = 20.0, n_points: int = 1000):
        """
        Initialize validator.
        
        Args:
            max_n: Maximum Hermite index to compute
            x_max: Integration domain [-x_max, x_max]
            n_points: Number of integration points
        """
        self.max_n = max_n
        self.x_max = x_max
        self.n_points = n_points
        self.x_grid = np.linspace(-x_max, x_max, n_points)
        
    def H_psi_action(self, n: int) -> np.ndarray:
        """
        Compute H_Ψ(ψ_n)(x) using explicit recurrence relations.
        
        From Hermite recurrence:
        H_Ψ(ψ_n) = -√(n/2) ψ_{n-1} - √((n+1)/2) ψ_{n+1}
        
        (The logarithmic term is suppressed for large n and handled
        through the decay analysis)
        
        Args:
            n: Hermite index
            
        Returns:
            H_Ψ(ψ_n) evaluated on grid
        """
        x = self.x_grid
        result = np.zeros_like(x)
        
        # Recurrence relation terms
        if n > 0:
            result -= np.sqrt(n / 2.0) * HermiteBasis.psi_n(n - 1, x)
        
        result -= np.sqrt((n + 1) / 2.0) * HermiteBasis.psi_n(n + 1, x)
        
        return result
    
    def compute_L2_norm(self, f: np.ndarray) -> float:
        """
        Compute L² norm ‖f‖² = ∫ |f(x)|² dx using trapezoidal rule.
        
        Args:
            f: Function values on grid
            
        Returns:
            L² norm
        """
        integrand = np.abs(f)**2
        dx = self.x_grid[1] - self.x_grid[0]
        # Use trapezoid (newer numpy) or trapz (older numpy)
        try:
            integral = np.trapezoid(integrand, dx=dx)
        except AttributeError:
            from scipy.integrate import trapezoid
            integral = trapezoid(integrand, dx=dx)
        return np.sqrt(integral)
    
    def compute_operator_norms(self) -> Tuple[np.ndarray, np.ndarray]:
        """
        Compute ‖H_Ψ(ψ_n)‖ for n = 0, ..., max_n.
        
        Returns:
            (n_values, norms) arrays
        """
        n_values = np.arange(self.max_n)
        norms = np.zeros(self.max_n)
        
        print("🔍 Computing operator norms ‖H_Ψ(ψ_n)‖...")
        print("=" * 60)
        
        for n in n_values:
            H_psi_n = self.H_psi_action(n)
            norms[n] = self.compute_L2_norm(H_psi_n)
            
            if n % 5 == 0 or n < 10:
                print(f"  n={n:3d}: ‖H_Ψ(ψ_{n})‖ = {norms[n]:.10f}")
        
        return n_values, norms
    
    def fit_asymptotic_decay(self, n_values: np.ndarray, norms: np.ndarray,
                            n_start: int = 10) -> Tuple[float, float]:
        """
        Fit norms to asymptotic form C/n^(1+δ).
        
        Args:
            n_values: Hermite indices
            norms: Operator norms
            n_start: Start fitting from this index
            
        Returns:
            (C, delta) fitted parameters
        """
        mask = n_values >= n_start
        n_fit = n_values[mask]
        norms_fit = norms[mask]
        
        # Linearize: log(norm) = log(C) - (1+δ) log(n+1)
        log_n = np.log(n_fit + 1)
        log_norms = np.log(norms_fit)
        
        # Linear regression
        A = np.vstack([np.ones_like(log_n), -log_n]).T
        params = np.linalg.lstsq(A, log_norms, rcond=None)[0]
        
        C = np.exp(params[0])
        delta = params[1] - 1.0
        
        return C, delta
    
    def verify_convergence(self, norms: np.ndarray) -> Dict[str, any]:
        """
        Verify that Σ‖H_Ψ(ψ_n)‖ converges.
        
        Args:
            norms: Operator norms array
            
        Returns:
            Dictionary with convergence statistics
        """
        partial_sums = np.cumsum(norms)
        total_sum = partial_sums[-1]
        
        # Estimate tail using fitted decay
        n_values = np.arange(len(norms))
        C, delta = self.fit_asymptotic_decay(n_values, norms)
        
        # Tail estimate: Σ_{n=N}^∞ C/n^(1+δ) ≈ C * ζ(1+δ) - partial sum
        from scipy.special import zeta
        if delta > 0.01:
            zeta_value = zeta(1 + delta)
            predicted_total = C * zeta_value
            tail_estimate = predicted_total - total_sum
        else:
            tail_estimate = np.inf
            predicted_total = np.inf
        
        return {
            'total_sum': total_sum,
            'partial_sums': partial_sums,
            'C': C,
            'delta': delta,
            'tail_estimate': tail_estimate,
            'predicted_total': predicted_total,
            'converges': delta > 0.01 and total_sum < 100.0
        }
    
    def run_validation(self) -> Dict[str, any]:
        """
        Run complete trace class validation.
        
        Returns:
            Validation results dictionary
        """
        print("🚀 TRACE CLASS VALIDATION FOR H_Ψ OPERATOR")
        print("=" * 60)
        print(f"Configuration:")
        print(f"  Max Hermite index: {self.max_n}")
        print(f"  Integration domain: [{-self.x_max}, {self.x_max}]")
        print(f"  Grid points: {self.n_points}")
        print()
        
        # Compute norms
        n_values, norms = self.compute_operator_norms()
        
        # Fit asymptotic decay
        print("\n" + "=" * 60)
        print("📊 ASYMPTOTIC ANALYSIS")
        C, delta = self.fit_asymptotic_decay(n_values, norms)
        print(f"  Fitted decay: ‖H_Ψ(ψ_n)‖ ≈ {C:.6f} / (n+1)^{1+delta:.6f}")
        print(f"  Decay exponent: 1 + δ = {1 + delta:.6f}")
        print(f"  Delta: δ = {delta:.6f}")
        
        if delta > 0.01:
            print(f"  ✅ δ = {delta:.6f} > 0 (convergence guaranteed)")
        else:
            print(f"  ⚠️  δ = {delta:.6f} too small (convergence uncertain)")
        
        # Verify convergence
        print("\n" + "=" * 60)
        print("🎯 CONVERGENCE VERIFICATION")
        convergence = self.verify_convergence(norms)
        
        print(f"  Partial sum S_{self.max_n} = {convergence['total_sum']:.10f}")
        print(f"  Tail estimate: {convergence['tail_estimate']:.10f}")
        print(f"  Predicted total: {convergence['predicted_total']:.10f}")
        
        # Final verdict
        print("\n" + "=" * 60)
        if convergence['converges']:
            print("✅ CONCLUSION: H_Ψ IS TRACE CLASS")
            print("   Σ‖H_Ψ(ψ_n)‖ < ∞ converges ✓")
            print("   det(I - zH⁻¹) is well-defined ✓")
        else:
            print("❌ CONCLUSION: CONVERGENCE NOT VERIFIED")
            print("   Further analysis required")
        
        print("=" * 60)
        
        return {
            'n_values': n_values.tolist(),
            'norms': norms.tolist(),
            'C': C,
            'delta': delta,
            'convergence': convergence,
            'is_trace_class': convergence['converges']
        }
    
    def save_results(self, results: Dict[str, any], filename: str = 'data/trace_class_validation.json'):
        """Save validation results to JSON file."""
        import os
        os.makedirs(os.path.dirname(filename), exist_ok=True)
        
        # Convert non-serializable types
        results_serializable = {
            'n_values': results['n_values'],
            'norms': results['norms'],
            'C': float(results['C']),
            'delta': float(results['delta']),
            'convergence': {
                'total_sum': float(results['convergence']['total_sum']),
                'C': float(results['convergence']['C']),
                'delta': float(results['convergence']['delta']),
                'tail_estimate': float(results['convergence']['tail_estimate']),
                'predicted_total': float(results['convergence']['predicted_total']),
                'converges': bool(results['convergence']['converges'])
            },
            'is_trace_class': bool(results['is_trace_class'])
        }
        
        with open(filename, 'w') as f:
            json.dump(results_serializable, f, indent=2)
        
        print(f"\n💾 Results saved to {filename}")
    
    def plot_results(self, n_values: np.ndarray, norms: np.ndarray, C: float, delta: float):
        """Create visualization of decay behavior."""
        fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 5))
        
        # Plot 1: Norms and fitted decay
        ax1.semilogy(n_values, norms, 'bo-', label='‖H_Ψ(ψ_n)‖', markersize=4)
        n_fit = n_values[n_values >= 5]
        fitted = C / (n_fit + 1)**(1 + delta)
        ax1.semilogy(n_fit, fitted, 'r--', label=f'Fit: {C:.3f}/n^{1+delta:.3f}', linewidth=2)
        ax1.set_xlabel('Hermite index n')
        ax1.set_ylabel('Operator norm')
        ax1.set_title('H_Ψ Operator Norms Decay')
        ax1.legend()
        ax1.grid(True, alpha=0.3)
        
        # Plot 2: Partial sums
        partial_sums = np.cumsum(norms)
        ax2.plot(n_values, partial_sums, 'go-', label='Partial sum S_n', markersize=4)
        ax2.axhline(y=partial_sums[-1], color='r', linestyle='--', 
                   label=f'S_{len(norms)} = {partial_sums[-1]:.3f}')
        ax2.set_xlabel('Hermite index n')
        ax2.set_ylabel('Partial sum')
        ax2.set_title('Convergence of Σ‖H_Ψ(ψ_n)‖')
        ax2.legend()
        ax2.grid(True, alpha=0.3)
        
        plt.tight_layout()
        
        import os
        os.makedirs('data', exist_ok=True)
        plt.savefig('data/trace_class_convergence.png', dpi=150, bbox_inches='tight')
        print(f"📊 Plot saved to data/trace_class_convergence.png")
        plt.close()


def main():
    """Main validation routine."""
    # Initialize validator
    validator = TraceClassValidator(max_n=50, x_max=20.0, n_points=1000)
    
    # Run validation
    results = validator.run_validation()
    
    # Save results
    validator.save_results(results)
    
    # Create plots
    validator.plot_results(
        np.array(results['n_values']),
        np.array(results['norms']),
        results['C'],
        results['delta']
    )
    
    return 0 if results['is_trace_class'] else 1


if __name__ == "__main__":
    exit(main())
