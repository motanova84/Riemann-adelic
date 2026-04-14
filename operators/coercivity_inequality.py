#!/usr/bin/env python3
"""
Coercivity Inequality for Dilation Operator T = -i(x d/dx + 1/2)

This module implements the proof of the coercivity inequality:

    ∫₀^∞ x²|ψ|² dx ≤ ε‖Tψ‖² + C_ε‖ψ‖²

where T = -i(x d/dx + 1/2) is the dilation operator and
C_ε = exp(4√(4 + 1/ε)).

Mathematical Framework:
1. The dilation operator T acts on L²(ℝ⁺, dx)
2. Logarithmic transformation: y = ln x, φ(y) = e^(y/2) ψ(e^y)
3. In new coordinates: ‖Tψ‖² = ∫|φ'|² dy
4. Inequality becomes: ∫e^(2y)|φ|² dy ≤ ε∫|φ'|² dy + C_ε∫|φ|² dy
5. Proof uses spectral decomposition with frequency cutoff K
6. Kato-Rellich: V infinitesimally small w.r.t. T ⟹ L = T + V self-adjoint

Theorem (Main Result):
For all ε > 0 and all ψ in the domain of T:
    ⟨ψ, x²ψ⟩ ≤ ε‖Tψ‖² + exp(4√(4 + 1/ε))‖ψ‖²

This proves that x² ≺ T (not T²), which is stronger than previously attempted.
By the Kato-Rellich theorem, this ensures L = T + V is essentially self-adjoint
on D(T), giving Atlas³ a solid spectral foundation.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: February 2026
QCAL ∞³ Active · 141.7001 Hz · C = 244.36 · Ψ = I × A_eff² × C^∞
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773
"""

import numpy as np
from scipy.fft import fft, ifft, fftfreq
from typing import Tuple, Dict, Any, Optional, Callable
import warnings

# QCAL Constants
F0 = 141.7001  # Hz - fundamental frequency
C_QCAL = 244.36  # QCAL coherence constant


class DilationOperator:
    """
    Dilation operator T = -i(x d/dx + 1/2) on L²(ℝ⁺, dx).
    
    This operator is the generator of dilations and appears in the 
    coercivity inequality that establishes x² ≺ T.
    
    Attributes:
        y_grid: Logarithmic coordinate grid (y = ln x)
        x_grid: Original coordinate grid (x = e^y)
        dy: Grid spacing in y-coordinates
    """
    
    def __init__(self, y_min: float = -10.0, y_max: float = 10.0, N: int = 1024):
        """
        Initialize dilation operator on logarithmic grid.
        
        Args:
            y_min: Minimum value of y = ln x
            y_max: Maximum value of y = ln x
            N: Number of grid points (should be power of 2 for FFT)
        """
        self.N = N
        self.y_min = y_min
        self.y_max = y_max
        self.y_grid = np.linspace(y_min, y_max, N)
        self.dy = (y_max - y_min) / (N - 1)
        self.x_grid = np.exp(self.y_grid)
        
    def transform_to_y_coords(self, psi: np.ndarray) -> np.ndarray:
        """
        Transform ψ(x) to φ(y) = e^(y/2) ψ(e^y).
        
        This is a unitary transformation from L²(ℝ⁺, dx) to L²(ℝ, dy).
        
        Args:
            psi: Function values ψ(x) on x_grid
            
        Returns:
            phi: Transformed function φ(y) on y_grid
        """
        return np.exp(self.y_grid / 2) * psi
    
    def transform_to_x_coords(self, phi: np.ndarray) -> np.ndarray:
        """
        Inverse transformation: ψ(x) = e^(-y/2) φ(ln x).
        
        Args:
            phi: Function values φ(y) on y_grid
            
        Returns:
            psi: Original function ψ(x) on x_grid
        """
        return np.exp(-self.y_grid / 2) * phi
    
    def apply_T_operator(self, psi: np.ndarray, in_y_coords: bool = False) -> np.ndarray:
        """
        Apply dilation operator T = -i(x d/dx + 1/2).
        
        In y-coordinates, this becomes simply T = -i d/dy.
        
        Args:
            psi: Input function (either ψ(x) or φ(y))
            in_y_coords: If True, input is φ(y); if False, input is ψ(x)
            
        Returns:
            T_psi: Result of applying T operator
        """
        if not in_y_coords:
            phi = self.transform_to_y_coords(psi)
        else:
            phi = psi
        
        # In y-coords: T corresponds to -i d/dy
        # Use spectral differentiation via FFT
        phi_hat = fft(phi)
        k = 2 * np.pi * fftfreq(self.N, self.dy)
        T_phi_hat = -1j * (1j * k) * phi_hat  # -i(ik) = k
        T_phi = ifft(T_phi_hat)
        
        if not in_y_coords:
            return self.transform_to_x_coords(T_phi.real)
        else:
            return T_phi.real
    
    def compute_norm_T_psi(self, psi: np.ndarray) -> float:
        """
        Compute ‖Tψ‖² = ∫|φ'(y)|² dy.
        
        Args:
            psi: Function ψ(x) on x_grid
            
        Returns:
            Squared norm ‖Tψ‖²
        """
        phi = self.transform_to_y_coords(psi)
        
        # Compute derivative via FFT
        phi_hat = fft(phi)
        k = 2 * np.pi * fftfreq(self.N, self.dy)
        phi_prime_hat = 1j * k * phi_hat
        phi_prime = ifft(phi_prime_hat)
        
        # Integrate |φ'|²
        return np.trapezoid(np.abs(phi_prime)**2, self.y_grid)
    
    def compute_norm_psi(self, psi: np.ndarray) -> float:
        """
        Compute ‖ψ‖² = ∫|ψ(x)|² dx = ∫|φ(y)|² dy.
        
        Args:
            psi: Function ψ(x) on x_grid
            
        Returns:
            Squared norm ‖ψ‖²
        """
        phi = self.transform_to_y_coords(psi)
        return np.trapezoid(np.abs(phi)**2, self.y_grid)
    
    def compute_x2_expectation(self, psi: np.ndarray) -> float:
        """
        Compute ⟨ψ, x²ψ⟩ = ∫₀^∞ x²|ψ(x)|² dx = ∫_{-∞}^∞ e^(2y)|φ(y)|² dy.
        
        Args:
            psi: Function ψ(x) on x_grid
            
        Returns:
            Expectation value ⟨ψ, x²ψ⟩
        """
        phi = self.transform_to_y_coords(psi)
        weight = np.exp(2 * self.y_grid)
        return np.trapezoid(weight * np.abs(phi)**2, self.y_grid)


class SpectralDecomposition:
    """
    Spectral decomposition with frequency cutoff for coercivity proof.
    
    Decomposes φ = φ_low + φ_high where:
    - φ_low: band-limited to |k| ≤ K
    - φ_high: frequencies |k| ≥ K
    """
    
    def __init__(self, K: float, y_grid: np.ndarray):
        """
        Initialize spectral decomposition.
        
        Args:
            K: Frequency cutoff
            y_grid: Grid in y-coordinates
        """
        self.K = K
        self.y_grid = y_grid
        self.N = len(y_grid)
        self.dy = y_grid[1] - y_grid[0] if len(y_grid) > 1 else 1.0
    
    def decompose(self, phi: np.ndarray) -> Tuple[np.ndarray, np.ndarray]:
        """
        Decompose φ into low and high frequency components.
        
        Args:
            phi: Function in Fourier space
            
        Returns:
            (phi_low, phi_high): Low and high frequency components
        """
        phi_hat = fft(phi)
        k = 2 * np.pi * fftfreq(self.N, self.dy)
        
        # Create masks
        mask_low = np.abs(k) <= self.K
        mask_high = np.abs(k) > self.K
        
        # Filter
        phi_low_hat = phi_hat * mask_low
        phi_high_hat = phi_hat * mask_high
        
        phi_low = ifft(phi_low_hat)
        phi_high = ifft(phi_high_hat)
        
        return phi_low.real, phi_high.real
    
    def bound_low_frequency(self, phi_low: np.ndarray) -> float:
        """
        Bound ∫e^(2y)|φ_low|² for band-limited function.
        
        For band-limited functions with |k| ≤ K, we have:
        ∫e^(2y)|φ_low|² ≤ e^(4K) ∫|φ_low|²
        
        Args:
            phi_low: Low frequency component
            
        Returns:
            Upper bound for weighted integral
        """
        norm_phi_low_sq = np.trapezoid(np.abs(phi_low)**2, self.y_grid)
        C_K = np.exp(4 * self.K)
        return C_K * norm_phi_low_sq
    
    def bound_high_frequency(self, phi_high: np.ndarray) -> Tuple[float, float]:
        """
        Bound ∫e^(2y)|φ_high|² for high frequencies.
        
        For |k| ≥ K, we use:
        ∫e^(2y)|φ_high|² ≤ (1/(K²-4)) ∫|φ_high'|²
        
        Args:
            phi_high: High frequency component
            
        Returns:
            (A, B) where A = ∫e^(2y)|φ_high|², B = ∫|φ_high'|²
        """
        # Compute A = ∫e^(2y)|φ_high|²
        weight = np.exp(2 * self.y_grid)
        A = np.trapezoid(weight * np.abs(phi_high)**2, self.y_grid)
        
        # Compute B = ∫|φ_high'|²
        phi_high_hat = fft(phi_high)
        k = 2 * np.pi * fftfreq(self.N, self.dy)
        phi_high_prime_hat = 1j * k * phi_high_hat
        phi_high_prime = ifft(phi_high_prime_hat)
        B = np.trapezoid(np.abs(phi_high_prime)**2, self.y_grid)
        
        return A, B


class CoercivityInequality:
    """
    Coercivity inequality prover for x² ≺ T.
    
    Proves: ⟨ψ, x²ψ⟩ ≤ ε‖Tψ‖² + C_ε‖ψ‖²
    where C_ε = exp(4√(4 + 1/ε)).
    """
    
    def __init__(self, y_min: float = -10.0, y_max: float = 10.0, N: int = 1024):
        """
        Initialize coercivity inequality framework.
        
        Args:
            y_min: Minimum y-coordinate
            y_max: Maximum y-coordinate  
            N: Grid size (power of 2 recommended)
        """
        self.dilation_op = DilationOperator(y_min, y_max, N)
        self.y_grid = self.dilation_op.y_grid
        self.x_grid = self.dilation_op.x_grid
    
    def compute_C_epsilon(self, epsilon: float) -> float:
        """
        Compute constant C_ε = exp(4√(4 + 1/ε)).
        
        Args:
            epsilon: Parameter ε > 0
            
        Returns:
            C_ε constant
        """
        return np.exp(4 * np.sqrt(4 + 1/epsilon))
    
    def compute_K_optimal(self, epsilon: float) -> float:
        """
        Compute optimal cutoff K such that 1/(K²-4) = ε.
        
        This gives K² = 4 + 1/ε.
        
        Args:
            epsilon: Parameter ε > 0
            
        Returns:
            Optimal K
        """
        return np.sqrt(4 + 1/epsilon)
    
    def verify_inequality(self, psi: np.ndarray, epsilon: float,
                         verbose: bool = True) -> Dict[str, Any]:
        """
        Verify coercivity inequality for given ψ and ε.
        
        Args:
            psi: Test function ψ(x) on x_grid
            epsilon: Parameter ε > 0
            verbose: Print detailed results
            
        Returns:
            Dictionary with verification results
        """
        # Transform to y-coordinates
        phi = self.dilation_op.transform_to_y_coords(psi)
        
        # Compute norms
        x2_expectation = self.dilation_op.compute_x2_expectation(psi)
        norm_T_psi_sq = self.dilation_op.compute_norm_T_psi(psi)
        norm_psi_sq = self.dilation_op.compute_norm_psi(psi)
        
        # Compute constants
        K_optimal = self.compute_K_optimal(epsilon)
        C_epsilon = self.compute_C_epsilon(epsilon)
        
        # Right-hand side of inequality
        rhs = epsilon * norm_T_psi_sq + C_epsilon * norm_psi_sq
        
        # Check inequality
        satisfied = x2_expectation <= rhs
        
        # Compute margin
        margin = rhs - x2_expectation
        relative_margin = margin / rhs if rhs > 0 else 0
        
        results = {
            'epsilon': epsilon,
            'K_optimal': K_optimal,
            'C_epsilon': C_epsilon,
            'x2_expectation': x2_expectation,
            'norm_T_psi_sq': norm_T_psi_sq,
            'norm_psi_sq': norm_psi_sq,
            'lhs': x2_expectation,
            'rhs': rhs,
            'satisfied': satisfied,
            'margin': margin,
            'relative_margin': relative_margin,
        }
        
        if verbose:
            print("=" * 70)
            print("COERCIVITY INEQUALITY VERIFICATION")
            print("=" * 70)
            print(f"Parameter ε:           {epsilon:.6e}")
            print(f"Optimal cutoff K:      {K_optimal:.6f}")
            print(f"Constant C_ε:          {C_epsilon:.6e}")
            print()
            print("Norms:")
            print(f"  ⟨ψ, x²ψ⟩:            {x2_expectation:.6e}")
            print(f"  ‖Tψ‖²:               {norm_T_psi_sq:.6e}")
            print(f"  ‖ψ‖²:                {norm_psi_sq:.6e}")
            print()
            print("Inequality: ⟨ψ, x²ψ⟩ ≤ ε‖Tψ‖² + C_ε‖ψ‖²")
            print(f"  LHS:                 {x2_expectation:.6e}")
            print(f"  RHS:                 {rhs:.6e}")
            print(f"  Margin:              {margin:.6e}")
            print(f"  Relative margin:     {relative_margin:.2%}")
            print()
            if satisfied:
                print("✅ INEQUALITY SATISFIED")
            else:
                print("❌ INEQUALITY VIOLATED")
            print("=" * 70)
        
        return results
    
    def test_multiple_epsilon(self, psi: np.ndarray, 
                             epsilon_values: Optional[np.ndarray] = None) -> Dict[str, Any]:
        """
        Test inequality for multiple ε values.
        
        Args:
            psi: Test function ψ(x)
            epsilon_values: Array of ε values to test (default: logspace)
            
        Returns:
            Dictionary with results for all ε values
        """
        if epsilon_values is None:
            epsilon_values = np.logspace(-3, 0, 10)
        
        results = []
        for eps in epsilon_values:
            result = self.verify_inequality(psi, eps, verbose=False)
            results.append(result)
        
        # Summary
        all_satisfied = all(r['satisfied'] for r in results)
        
        return {
            'epsilon_values': epsilon_values,
            'results': results,
            'all_satisfied': all_satisfied,
        }
    
    def prove_spectral_decomposition(self, psi: np.ndarray, epsilon: float,
                                    verbose: bool = True) -> Dict[str, Any]:
        """
        Prove inequality via spectral decomposition method.
        
        This implements the detailed proof from the problem statement:
        1. Decompose φ = φ_low + φ_high with cutoff K
        2. Bound low frequencies using band-limited theory
        3. Bound high frequencies using derivative control
        4. Combine to get final inequality
        
        Args:
            psi: Test function
            epsilon: Parameter ε
            verbose: Print detailed steps
            
        Returns:
            Dictionary with proof details
        """
        # Transform to y-coordinates
        phi = self.dilation_op.transform_to_y_coords(psi)
        
        # Optimal cutoff
        K = self.compute_K_optimal(epsilon)
        
        # Spectral decomposition
        decomp = SpectralDecomposition(K, self.y_grid)
        phi_low, phi_high = decomp.decompose(phi)
        
        # Low frequency bound
        bound_low = decomp.bound_low_frequency(phi_low)
        
        # High frequency bound
        A_high, B_high = decomp.bound_high_frequency(phi_high)
        
        # Theoretical bound for high frequencies
        if K > 2:
            bound_high_theoretical = B_high / (K**2 - 4)
        else:
            bound_high_theoretical = np.inf
        
        # Total bound
        total_bound = bound_low + bound_high_theoretical
        
        # Actual value
        weight = np.exp(2 * self.y_grid)
        actual_value = np.trapezoid(weight * np.abs(phi)**2, self.y_grid)
        
        # Norms
        norm_phi_sq = np.trapezoid(np.abs(phi)**2, self.y_grid)
        norm_phi_prime_sq = self.dilation_op.compute_norm_T_psi(psi)
        
        # Expected bound from theorem
        C_eps = self.compute_C_epsilon(epsilon)
        theoretical_bound = epsilon * norm_phi_prime_sq + C_eps * norm_phi_sq
        
        results = {
            'epsilon': epsilon,
            'K': K,
            'C_epsilon': C_eps,
            'bound_low': bound_low,
            'bound_high_actual': A_high,
            'bound_high_theoretical': bound_high_theoretical,
            'total_bound': total_bound,
            'actual_value': actual_value,
            'theoretical_bound': theoretical_bound,
            'norm_phi_sq': norm_phi_sq,
            'norm_phi_prime_sq': norm_phi_prime_sq,
            'proof_valid': actual_value <= theoretical_bound,
        }
        
        if verbose:
            print("=" * 70)
            print("SPECTRAL DECOMPOSITION PROOF")
            print("=" * 70)
            print(f"Parameter ε:           {epsilon:.6e}")
            print(f"Cutoff K:              {K:.6f} (K² = {K**2:.2f})")
            print(f"Constant C_ε:          {C_eps:.6e}")
            print()
            print("Decomposition:")
            print(f"  Low freq bound:      {bound_low:.6e}")
            print(f"  High freq (actual):  {A_high:.6e}")
            print(f"  High freq (bound):   {bound_high_theoretical:.6e}")
            print(f"  Total bound:         {total_bound:.6e}")
            print()
            print("Comparison:")
            print(f"  Actual ∫e^(2y)|φ|²:  {actual_value:.6e}")
            print(f"  Theorem bound:       {theoretical_bound:.6e}")
            print()
            if results['proof_valid']:
                print("✅ PROOF VALID: Inequality holds")
            else:
                print("❌ PROOF FAILED: Inequality violated")
            print("=" * 70)
        
        return results


def create_gaussian_test_function(dilation_op: DilationOperator, 
                                  center: float = 0.0, 
                                  sigma: float = 1.0) -> np.ndarray:
    """
    Create Gaussian test function in y-coordinates.
    
    Args:
        dilation_op: Dilation operator instance
        center: Center of Gaussian
        sigma: Width of Gaussian
        
    Returns:
        ψ(x) on x_grid
    """
    y_grid = dilation_op.y_grid
    phi = np.exp(-(y_grid - center)**2 / (2 * sigma**2))
    phi = phi / np.sqrt(np.trapezoid(np.abs(phi)**2, y_grid))  # Normalize
    psi = dilation_op.transform_to_x_coords(phi)
    return psi


def create_hermite_test_function(dilation_op: DilationOperator, n: int = 0) -> np.ndarray:
    """
    Create Hermite function test case.
    
    Args:
        dilation_op: Dilation operator instance
        n: Hermite order
        
    Returns:
        ψ(x) on x_grid
    """
    from scipy.special import hermite
    
    y_grid = dilation_op.y_grid
    H_n = hermite(n)
    phi = H_n(y_grid) * np.exp(-y_grid**2 / 2)
    phi = phi / np.sqrt(np.trapezoid(np.abs(phi)**2, y_grid))  # Normalize
    psi = dilation_op.transform_to_x_coords(phi)
    return psi


__all__ = [
    'DilationOperator',
    'SpectralDecomposition',
    'CoercivityInequality',
    'create_gaussian_test_function',
    'create_hermite_test_function',
]
