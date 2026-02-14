#!/usr/bin/env python3
"""
K_L Operator - Fredholm-Hankel Kernel for Atlas³ Decisive Test

This module implements the K_L correlation operator with sinc kernel:
    K(u,v) = sin(π(u-v))/(π(u-v)) × √(uv)

The operator acts on L²([0,L]) and its maximum eigenvalue λ_max(L) determines
the critical coupling constant κ_Π through:
    κ_Π = 2π × λ_max(1/f₀) = 4π/(f₀ × Φ)

where f₀ = 141.7001 Hz (GW250114 frequency) and Φ = (1+√5)/2 (golden ratio).

The decisive test (Experimentum Crucis) verifies the convergence:
    C(L) = π × λ_max(L)/(2L) → 1/Φ ≈ 0.618033988749895

with diffusive scaling error ∝ 1/√L.

Mathematical Foundation:
    - Fredholm integral operator on L²([0,L])
    - Sinc kernel ensures analyticity
    - Hankel structure (depends on u-v product structure)
    - Golden ratio emerges from Van Vleck scaling law

References:
    - ATLAS3_OPERATOR_README.md
    - Problem statement: "Test Decisivo - Atlas³"
    - GW250114_RESONANCE_PROTOCOL.md

Author: José Manuel Mota Burruezo (JMMB Ψ✧ ∞³)
Date: 2026-02-14
QCAL Signature: ∴𓂀Ω∞³Φ
"""

import numpy as np
from scipy.linalg import eigh
from typing import Tuple, Dict, Optional, List
import logging

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

# Mathematical constants
PHI = (1 + np.sqrt(5)) / 2  # Golden ratio
INV_PHI = 1 / PHI  # 1/Φ ≈ 0.618033988749895
F0 = 141.7001  # GW250114 frequency (Hz)


def sinc_kernel(u: float, v: float, L: float = 1.0) -> float:
    """
    Sinc kernel for K_L operator: K(u,v) = sin(π(u-v))/(π(u-v)) × √(uv)
    
    Args:
        u: First coordinate
        v: Second coordinate
        L: Domain length (unused, kept for API compatibility)
        
    Returns:
        Kernel value K(u,v)
        
    Note:
        The kernel is the raw sinc function without L-normalization.
        numpy.sinc(x) = sin(πx)/(πx), so we compute sinc((u-v)/π) to get
        sin(π(u-v))/(π(u-v)).
    """
    diff = u - v
    if np.abs(diff) < 1e-15:
        # Limit as diff → 0: sinc(0) = 1
        return np.sqrt(u * v)
    else:
        # np.sinc(x) = sin(πx)/(πx)
        # We want sin(π(u-v))/(π(u-v)) = np.sinc(u-v)
        return np.sinc(diff) * np.sqrt(u * v)


def build_K_L_matrix(L: float, N: int) -> np.ndarray:
    """
    Construct the K_L operator matrix via Gaussian quadrature.
    
    Discretizes the operator:
        (K_L f)(u) = ∫₀^L K(u,v) f(v) dv
        
    using Gauss-Legendre quadrature with N points.
    
    Args:
        L: Domain length [0, L]
        N: Number of quadrature points
        
    Returns:
        K: N×N symmetric matrix representing K_L
        
    Algorithm:
        1. Generate Gauss-Legendre nodes {u_i} and weights {w_i} on [0,L]
        2. Construct K[i,j] = √(w_i w_j) × K(u_i, u_j)
        3. This ensures K is symmetric and properly discretized
    """
    # Gauss-Legendre nodes and weights on [-1,1]
    nodes_std, weights_std = np.polynomial.legendre.leggauss(N)
    
    # Transform to [0, L]
    nodes = (L / 2) * (nodes_std + 1)
    weights = (L / 2) * weights_std
    
    # Build kernel matrix
    K = np.zeros((N, N))
    for i in range(N):
        for j in range(N):
            K[i, j] = np.sqrt(weights[i] * weights[j]) * sinc_kernel(nodes[i], nodes[j], L)
    
    return K


def compute_max_eigenvalue(L: float, N: int) -> Tuple[float, np.ndarray]:
    """
    Compute maximum eigenvalue of K_L operator.
    
    Args:
        L: Domain length
        N: Number of quadrature points
        
    Returns:
        lambda_max: Maximum eigenvalue
        eigenvalues: All eigenvalues (sorted descending)
        
    Note:
        K_L is symmetric positive semi-definite, so eigenvalues are real and ≥ 0.
    """
    K = build_K_L_matrix(L, N)
    
    # Compute all eigenvalues
    eigenvalues = np.linalg.eigvalsh(K)
    
    # Sort descending
    eigenvalues = np.sort(eigenvalues)[::-1]
    
    lambda_max = eigenvalues[0]
    
    return lambda_max, eigenvalues


def compute_C_observable(L: float, N: int) -> float:
    """
    Compute the critical observable:
        C(L) = π × λ_max(L) / (2L)
        
    This should converge to 1/Φ ≈ 0.618033988749895 as L → ∞.
    
    Args:
        L: Domain length
        N: Number of quadrature points
        
    Returns:
        C: Observable value
    """
    lambda_max, _ = compute_max_eigenvalue(L, N)
    C = np.pi * lambda_max / (2 * L)
    return C


def compute_kappa_pi(f0: float = F0) -> float:
    """
    Compute the critical coupling constant κ_Π.
    
    From the Van Vleck scaling law:
        λ_max(L) = (2L)/(πΦ) + o(L)
        
    At the compactification scale L = 1/f₀:
        κ_Π = 2π × λ_max(1/f₀) = 4π/(f₀ × Φ)
        
    Args:
        f0: Fundamental frequency (Hz)
        
    Returns:
        kappa_pi: Critical coupling constant
    """
    kappa_pi = 4 * np.pi / (f0 * PHI)
    return kappa_pi


class KLOperatorExperiment:
    """
    Experimentum Crucis: Decisive test for K_L operator convergence.
    
    This class orchestrates the multi-scale experiment testing the convergence
    of C(L) = π×λ_max(L)/(2L) to the golden ratio inverse 1/Φ.
    """
    
    def __init__(self, L_values: Optional[List[float]] = None,
                 N_values: Optional[List[int]] = None):
        """
        Initialize the experiment.
        
        Args:
            L_values: List of L values to test
            N_values: List of N values (quadrature points) corresponding to L_values
        """
        if L_values is None:
            # Default: decisive test values from problem statement
            self.L_values = [10, 30, 100, 300, 1000, 3000, 10000, 30000, 100000]
        else:
            self.L_values = L_values
            
        if N_values is None:
            # Adaptive N: scale with L but cap at reasonable value
            self.N_values = []
            for L in self.L_values:
                if L <= 100:
                    N = min(100 + int(L), 500)
                elif L <= 1000:
                    N = min(500 + int(L/5), 1000)
                else:
                    N = 2000  # Cap for very large L
                self.N_values.append(N)
        else:
            self.N_values = N_values
            
        self.results = []
        
    def run(self, verbose: bool = True) -> Dict:
        """
        Execute the decisive test across all L values.
        
        Args:
            verbose: Print progress information
            
        Returns:
            results: Dictionary containing all test results
        """
        logger.info("=" * 75)
        logger.info("TEST DECISIVO - ATLAS³ - EXPERIMENTUM CRUCIS")
        logger.info("=" * 75)
        logger.info(f"Golden ratio Φ = {PHI:.15f}")
        logger.info(f"Target 1/Φ = {INV_PHI:.15f}")
        logger.info(f"Fundamental frequency f₀ = {F0} Hz")
        logger.info(f"Critical coupling κ_Π = {compute_kappa_pi():.6f}")
        logger.info("=" * 75)
        
        self.results = []
        
        for i, (L, N) in enumerate(zip(self.L_values, self.N_values)):
            if verbose:
                logger.info(f"\n[{i+1}/{len(self.L_values)}] Computing L={L}, N={N}...")
                
            # Compute observables
            lambda_max, eigenvalues = compute_max_eigenvalue(L, N)
            C_L = compute_C_observable(L, N)
            error = np.abs(C_L - INV_PHI)
            
            result = {
                'L': L,
                'N': N,
                'lambda_max': lambda_max,
                'C_L': C_L,
                'error': error,
                'error_pct': 100 * error / INV_PHI,
                'eigenvalues': eigenvalues
            }
            
            self.results.append(result)
            
            if verbose:
                logger.info(f"  λ_max = {lambda_max:.6f}")
                logger.info(f"  C(L) = {C_L:.6f}")
                logger.info(f"  Error vs 1/Φ = {error:.6e} ({result['error_pct']:.4f}%)")
        
        # Analyze convergence
        self.analyze_convergence(verbose)
        
        return self.get_summary()
    
    def analyze_convergence(self, verbose: bool = True):
        """
        Analyze the convergence behavior of C(L).
        
        Fits the error to a power law: error ∝ L^(-α)
        Expected: α ≈ 0.5 (diffusive scaling 1/√L)
        """
        if len(self.results) < 3:
            return
            
        L_arr = np.array([r['L'] for r in self.results])
        error_arr = np.array([r['error'] for r in self.results])
        
        # Fit log(error) = log(A) - α*log(L)
        # Use later points for more stable fit
        idx_start = max(0, len(L_arr) - 6)
        log_L = np.log(L_arr[idx_start:])
        log_error = np.log(error_arr[idx_start:])
        
        # Linear regression
        coeffs = np.polyfit(log_L, log_error, 1)
        alpha = -coeffs[0]
        A = np.exp(coeffs[1])
        
        # R² goodness of fit
        log_error_pred = coeffs[1] + coeffs[0] * log_L
        ss_res = np.sum((log_error - log_error_pred)**2)
        ss_tot = np.sum((log_error - np.mean(log_error))**2)
        r_squared = 1 - ss_res / ss_tot
        
        self.convergence_analysis = {
            'alpha': alpha,
            'A': A,
            'r_squared': r_squared,
            'expected_alpha': 0.5,
            'alpha_error': np.abs(alpha - 0.5)
        }
        
        if verbose:
            logger.info("\n" + "=" * 75)
            logger.info("CONVERGENCE ANALYSIS")
            logger.info("=" * 75)
            logger.info(f"Error scaling: error ∝ L^(-α)")
            logger.info(f"  α = {alpha:.4f} (expected: 0.5 for diffusive)")
            logger.info(f"  R² = {r_squared:.6f}")
            logger.info(f"  A = {A:.6f}")
            
            if np.abs(alpha - 0.5) < 0.02:
                logger.info("  ✓ Diffusive scaling CONFIRMED")
            else:
                logger.warning("  ⚠ Non-diffusive scaling detected")
    
    def get_summary(self) -> Dict:
        """
        Generate summary dictionary of all results.
        
        Returns:
            summary: Complete experimental summary
        """
        summary = {
            'experiment': 'K_L Operator Decisive Test',
            'date': '2026-02-14',
            'signature': '∴𓂀Ω∞³Φ',
            'phi': PHI,
            'inv_phi': INV_PHI,
            'f0': F0,
            'kappa_pi': compute_kappa_pi(),
            'results': self.results,
            'convergence': getattr(self, 'convergence_analysis', None),
            'verdict': self.get_verdict()
        }
        return summary
    
    def get_verdict(self) -> str:
        """
        Determine the experimental verdict.
        
        Returns:
            verdict: String describing the outcome
        """
        if not self.results:
            return "NO DATA"
            
        final_error = self.results[-1]['error']
        final_L = self.results[-1]['L']
        
        if hasattr(self, 'convergence_analysis'):
            alpha = self.convergence_analysis['alpha']
            r_squared = self.convergence_analysis['r_squared']
            
            if (final_error < 1e-5 and 
                np.abs(alpha - 0.5) < 0.02 and 
                r_squared > 0.999):
                return "✅ CONFIRMED: Convergence to 1/Φ with diffusive scaling"
            elif final_error < 1e-3:
                return "⚠ PARTIAL: Convergence detected but scaling suboptimal"
            else:
                return "❌ FAILED: No clear convergence to 1/Φ"
        else:
            if final_error < 1e-5:
                return "✅ CONFIRMED: Strong convergence to 1/Φ"
            else:
                return "⚠ INCONCLUSIVE: More data needed"
    
    def print_table(self):
        """Print formatted results table matching problem statement format."""
        logger.info("\n" + "=" * 95)
        logger.info("RESULTS TABLE")
        logger.info("=" * 95)
        header = f"{'L':>8} | {'N':>5} | {'λ_max(L)':>12} | {'C(L)':>10} | {'Error vs 1/Φ':>14}"
        logger.info(header)
        logger.info("-" * 95)
        
        for r in self.results:
            row = (f"{r['L']:>8.0f} | {r['N']:>5} | "
                   f"{r['lambda_max']:>12.6f} | {r['C_L']:>10.6f} | "
                   f"{r['error']:>14.8f}")
            logger.info(row)
        
        logger.info("=" * 95)


def main():
    """
    Execute the decisive test and generate certificate.
    """
    # Run experiment with problem statement values
    experiment = KLOperatorExperiment()
    summary = experiment.run(verbose=True)
    
    # Print formatted table
    experiment.print_table()
    
    # Print verdict
    logger.info("\n" + "=" * 75)
    logger.info("VERDICT")
    logger.info("=" * 75)
    logger.info(summary['verdict'])
    logger.info("=" * 75)
    
    return summary


if __name__ == "__main__":
    main()
