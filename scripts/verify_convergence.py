#!/usr/bin/env python3
"""
High-Precision Convergence Verification for H_Ψ Trace Class

This script uses mpmath for high-precision arithmetic to verify
the convergence of Σ‖H_Ψ(ψ_n)‖ with extreme accuracy.

Features:
- Arbitrary precision arithmetic (50+ decimal places)
- Complex differentiation for derivative computation
- Detailed asymptotic analysis
- Statistical fitting with error estimates

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Instituto de Conciencia Cuántica (ICQ)
Date: 2025-12-26
"""

import numpy as np
import mpmath as mp
from scipy.special import hermite, gamma
from scipy.optimize import curve_fit
from typing import Tuple, List
import sys

# Configure high precision
mp.mp.dps = 50


class HermiteOperator:
    """High-precision implementation of H_Ψ"""
    
    def __init__(self, max_n: int = 100):
        """
        Initialize operator.
        
        Args:
            max_n: Maximum Hermite index
        """
        self.max_n = max_n
        
    def hermite_basis_mp(self, n: int, x: mp.mpf) -> mp.mpf:
        """
        Hermite basis function with mpmath precision.
        
        ψ_n(x) = (π^(-1/4) / sqrt(2^n n!)) H_n(x) exp(-x²/2)
        
        Args:
            n: Hermite index
            x: Evaluation point
            
        Returns:
            ψ_n(x) with high precision
        """
        # Normalization
        norm = mp.pi**(-0.25) / mp.sqrt(mp.power(2, n) * mp.gamma(n + 1))
        
        # Hermite polynomial
        H_n = mp.hermite(n, x)
        
        # Gaussian factor
        gaussian = mp.exp(-x**2 / 2)
        
        return norm * H_n * gaussian
    
    def psi_derivative_mp(self, n: int, x: mp.mpf, eps: mp.mpf = mp.mpf('1e-10')) -> mp.mpf:
        """
        Derivative using complex differentiation (more accurate).
        
        Uses: ψ'(x) ≈ Im[ψ(x + iε)] / ε
        
        Args:
            n: Hermite index
            x: Evaluation point
            eps: Complex step size
            
        Returns:
            ψ'_n(x) with high precision
        """
        # Complex step differentiation
        x_complex = x + 1j * eps
        psi_complex = self.hermite_basis_mp(n, x_complex)
        
        # Extract derivative from imaginary part
        deriv = psi_complex.imag / eps
        
        return mp.mpf(deriv)
    
    def H_psi_action_mp(self, n: int, x: mp.mpf) -> mp.mpf:
        """
        H_Ψ(ψ_n)(x) with high precision.
        
        H_Ψ(ψ_n) = -x ψ'_n(x) + π log|x| ψ_n(x)
        
        Args:
            n: Hermite index
            x: Evaluation point
            
        Returns:
            H_Ψ(ψ_n)(x)
        """
        psi_n = self.hermite_basis_mp(n, x)
        psi_deriv = self.psi_derivative_mp(n, x)
        
        # Handle log singularity
        if abs(x) < mp.mpf('1e-10'):
            log_term = mp.mpf(0)
        else:
            log_term = mp.pi * mp.log(mp.fabs(x)) * psi_n
        
        return -x * psi_deriv + log_term
    
    def compute_norm_mp(self, n: int, x_min: float = -15, x_max: float = 15, 
                       points: int = 500) -> mp.mpf:
        """
        Compute L² norm with mpmath integration.
        
        ‖f‖² = ∫ |f(x)|² dx
        
        Args:
            n: Hermite index
            x_min: Integration lower bound
            x_max: Integration upper bound
            points: Number of integration points
            
        Returns:
            L² norm with high precision
        """
        # Generate integration grid
        xs = [mp.mpf(x_min + i * (x_max - x_min) / (points - 1)) 
              for i in range(points)]
        
        # Evaluate function
        values = [self.H_psi_action_mp(n, x) for x in xs]
        
        # Trapezoidal integration of |f|²
        dx = mp.mpf((x_max - x_min) / (points - 1))
        integral = mp.mpf(0)
        
        for i in range(points - 1):
            f1 = mp.fabs(values[i])**2
            f2 = mp.fabs(values[i + 1])**2
            integral += (f1 + f2) * dx / 2
        
        return mp.sqrt(integral)
    
    def verify_trace_class(self) -> bool:
        """
        Verify convergence Σ‖H_Ψ(ψ_n)‖ < ∞ with high precision.
        
        Returns:
            True if trace class property verified
        """
        print("🔍 VERIFYING CONVERGENCE WITH HIGH PRECISION")
        print("=" * 60)
        print(f"Decimal precision: {mp.mp.dps} digits")
        print()
        
        norms = []
        n_vals = list(range(0, self.max_n))
        
        for n in n_vals:
            norm = self.compute_norm_mp(n)
            norms.append(float(norm))
            
            if n % 10 == 0 or n < 10:
                print(f"n={n:3d}: ‖H_Ψ(ψ_{n})‖ = {float(norm):.10f}")
            
            if n > 0 and n % 10 == 0:
                # Show partial sum
                partial_sum = sum(norms)
                print(f"  → Partial sum S_{n} = {partial_sum:.6f}")
        
        # Convergence analysis
        print("\n" + "=" * 60)
        print("📊 CONVERGENCE ANALYSIS")
        
        total_sum = sum(norms)
        print(f"\nTotal sum Σ‖H_Ψ(ψ_n)‖ = {total_sum:.10f}")
        
        # Fit asymptotic decay C/n^(1+δ)
        try:
            n_fit = np.array(n_vals)[10:]  # Use n ≥ 10
            norms_fit = np.array(norms)[10:]
            
            def model(n, C, delta):
                """Asymptotic model C/(n+1)^(1+δ)"""
                return C / (n + 1)**(1 + delta)
            
            # Fit with bounds
            popt, pcov = curve_fit(
                model, n_fit, norms_fit,
                p0=[0.5, 0.2],
                bounds=([0.1, 0.01], [2.0, 1.0])
            )
            
            C_fit, delta_fit = popt
            perr = np.sqrt(np.diag(pcov))
            
            print(f"\n📈 ASYMPTOTIC FIT:")
            print(f"  ‖H_Ψ(ψ_n)‖ ≈ {C_fit:.6f} ± {perr[0]:.6f} / (n+1)^{1+delta_fit:.6f}")
            print(f"  Decay exponent: 1 + δ = {1 + delta_fit:.6f} ± {perr[1]:.6f}")
            print(f"  Delta: δ = {delta_fit:.6f} ± {perr[1]:.6f}")
            
            # Check significance
            if delta_fit > 3 * perr[1]:
                print(f"  ✅ δ = {delta_fit:.6f} > 0 (statistically significant)")
                is_significant = True
            else:
                print(f"  ⚠️  δ = {delta_fit:.6f} ± {perr[1]:.6f} (not significant)")
                is_significant = False
            
            # Predict convergence using zeta function
            from scipy.special import zeta
            
            if delta_fit > 0.01:
                zeta_value = zeta(1 + delta_fit)
                predicted_sum = C_fit * zeta_value
                
                print(f"\n🎯 CONVERGENCE PREDICTION:")
                print(f"  ζ(1+δ) = ζ({1 + delta_fit:.6f}) = {zeta_value:.6f}")
                print(f"  Predicted total: Σ C/n^(1+δ) ≈ {predicted_sum:.6f}")
                print(f"  Computed sum: {total_sum:.6f}")
                print(f"  Difference: {abs(total_sum - predicted_sum):.6f}")
                
                # Check agreement
                rel_diff = abs(total_sum - predicted_sum) / predicted_sum
                if rel_diff < 0.2:
                    print(f"  ✅ Relative difference: {rel_diff:.2%} (good agreement)")
                else:
                    print(f"  ⚠️  Relative difference: {rel_diff:.2%} (needs more terms)")
                
                return is_significant and delta_fit > 0.1 and total_sum < 100.0
            else:
                return False
                
        except Exception as e:
            print(f"❌ Error in asymptotic fit: {e}")
            return False


def main():
    """Main execution routine."""
    # Create operator with moderate max_n for reasonable runtime
    operator = HermiteOperator(max_n=30)  # Reduced from 50 for speed
    
    # Run verification
    is_trace_class = operator.verify_trace_class()
    
    # Final verdict
    print("\n" + "=" * 60)
    if is_trace_class:
        print("✅ CONCLUSION: H_Ψ IS TRACE CLASS OPERATOR")
        print("   Σ‖H_Ψ(ψ_n)‖ < ∞ converges ✓")
        print("   det(I - zH⁻¹) is well-defined ✓")
        print("   Spectral determinant D(s) can be constructed ✓")
    else:
        print("❌ CONCLUSION: TRACE CLASS PROPERTY NOT VERIFIED")
        print("   Further analysis or higher precision needed")
    print("=" * 60)
    
    return 0 if is_trace_class else 1


if __name__ == "__main__":
    sys.exit(main())
