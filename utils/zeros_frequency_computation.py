#!/usr/bin/env python3
"""
Riemann Zeros Frequency Computation Module

This module implements the computation of a specific frequency based on
Riemann zeros with exponential decay weighting and golden ratio scaling.

The computation involves:
1. Loading Riemann zeros from data files
2. Computing weighted sum with exponential decay: Σ exp(-α·γ_n)
3. Validating against φ·400/exp(γ·π) target value
4. Computing final frequency with multiple scaling factors

Mathematical Background:
-----------------------
Constants:
- φ (phi): Golden ratio ≈ 1.618033988749894848...
- γ (Euler-Mascheroni constant): ≈ 0.577215664901532860...
- π (pi): ≈ 3.141592653589793238...

Target relationship:
S = Σ exp(-α·γ_n) where γ_n are Riemann zero imaginary parts
Validation: S·exp(γ·π) ≈ φ·400

Frequency formula:
f = (1/(2π)) × exp(γ)×√(2πγ) × (φ²/(2π)) × ψ_eff × δ

where:
- ψ_eff = ψ'/(2π·log²(ψ'/(2π)))
- ψ' = φ·400·exp(γ·π)
- δ = 1 + (1/φ)·log(γ·π)

Author: José Manuel Mota Burruezo
Date: October 2025
"""

import os
from pathlib import Path
from typing import List, Optional, Tuple
import warnings

from mpmath import mp


class ZerosFrequencyComputation:
    """
    Class for computing frequency from Riemann zeros with golden ratio scaling.
    
    This class implements the complete computation chain from loading zeros
    to calculating the final frequency with multiple scaling factors.
    
    Attributes:
        dps: Decimal precision for mpmath computations
        phi: Golden ratio constant
        gamma: Euler-Mascheroni constant
        pi: Pi constant
        e_gamma_pi: exp(γ·π)
        phi_400: φ × 400
        target: φ·400/exp(γ·π)
    """
    
    def __init__(self, dps: int = 100):
        """
        Initialize the computation with specified precision.
        
        Args:
            dps: Decimal precision for mpmath (default: 100)
        """
        # Set precision
        mp.dps = dps
        self.dps = dps
        
        # Initialize constants with high precision
        self.phi = mp.mpf('1.618033988749894848204586834365638117720309179805762862135448622705260')
        self.gamma = mp.mpf('0.577215664901532860606512090082402431042159335939923598805767234648689')
        self.pi = mp.mpf('3.141592653589793238462643383279502884197169399375105820974944592307816')
        
        # Derived constants
        self.e_gamma_pi = mp.exp(self.gamma * self.pi)
        self.phi_400 = self.phi * 400
        self.target = self.phi_400 / self.e_gamma_pi  # ~105.561830058
        
    def get_riemann_zeros(
        self, 
        T: Optional[float] = None, 
        limit: int = 3438,
        zeros_file: Optional[str] = None
    ) -> List[mp.mpf]:
        """
        Load Riemann zeros from file up to height T.
        
        This function loads Riemann zero imaginary parts from the data files
        in the zeros/ directory. If no file is specified, it attempts to load
        from the standard locations.
        
        Args:
            T: Maximum height to load zeros (if None, loads up to limit)
            limit: Maximum number of zeros to load
            zeros_file: Path to zeros file (if None, uses default)
            
        Returns:
            List of Riemann zero imaginary parts as mpmath mpf objects
            
        Raises:
            FileNotFoundError: If zeros file cannot be found
        """
        # Determine zeros file path
        if zeros_file is None:
            # Try standard locations
            repo_root = Path(__file__).parent.parent
            possible_paths = [
                repo_root / 'zeros' / 'zeros_t1e8.txt',
                repo_root / 'zeros' / 'zeros_t1e3.txt',
                Path('zeros') / 'zeros_t1e8.txt',
                Path('zeros') / 'zeros_t1e3.txt',
            ]
            
            zeros_file_path = None
            for path in possible_paths:
                if path.exists():
                    zeros_file_path = path
                    break
                    
            if zeros_file_path is None:
                raise FileNotFoundError(
                    "Could not find zeros file in standard locations. "
                    "Please specify zeros_file parameter."
                )
        else:
            zeros_file_path = Path(zeros_file)
            if not zeros_file_path.exists():
                raise FileNotFoundError(f"Zeros file not found: {zeros_file}")
        
        # Load zeros from file
        zeros = []
        try:
            with open(zeros_file_path, 'r') as f:
                for line in f:
                    line = line.strip()
                    if line and not line.startswith('#'):
                        try:
                            zero = mp.mpf(line)
                            if T is None or zero < T:
                                zeros.append(zero)
                                if len(zeros) >= limit:
                                    break
                        except (ValueError, TypeError):
                            # Skip invalid lines
                            continue
        except Exception as e:
            warnings.warn(f"Error reading zeros file: {e}")
            # Return hardcoded first few zeros as fallback
            zeros = [
                mp.mpf('14.134725141735'),
                mp.mpf('21.022039638772'),
                mp.mpf('25.010857580146'),
                mp.mpf('30.424876125860'),
                mp.mpf('32.935061587739'),
            ]
            warnings.warn(f"Using hardcoded first 5 zeros as fallback")
        
        # Sort zeros to ensure they are in ascending order
        zeros.sort(key=float)
        
        return zeros
    
    def compute_zeros_sum(
        self, 
        T: float = 3967.986, 
        alpha: float = 0.551020,
        zeros_file: Optional[str] = None,
        limit: int = 3438
    ) -> mp.mpf:
        """
        Calculate sum of exp(-α·γ_n) over Riemann zeros.
        
        This function computes:
        S = Σ exp(-α·γ_n)
        
        where γ_n are the imaginary parts of Riemann zeros up to height T.
        
        Args:
            T: Maximum height for zeros (default: 3967.986)
            alpha: Decay parameter (default: 0.551020)
            zeros_file: Path to zeros file (optional)
            limit: Maximum number of zeros (default: 3438)
            
        Returns:
            The computed sum S as mpmath mpf object
        """
        # Load zeros
        zeros = self.get_riemann_zeros(T=T, limit=limit, zeros_file=zeros_file)
        
        # Compute sum
        sum_exp = mp.mpf(0)
        for gamma_n in zeros:
            sum_exp += mp.exp(-alpha * gamma_n)
        
        return sum_exp
    
    def validate_sum(
        self,
        T: float = 3967.986,
        alpha: float = 0.551020,
        zeros_file: Optional[str] = None,
        limit: int = 3438,
        tolerance: float = 1e-6
    ) -> Tuple[mp.mpf, mp.mpf, bool]:
        """
        Validate that the zeros sum satisfies the target relationship.
        
        Computes S = Σ exp(-α·γ_n) and checks if:
        S·exp(γ·π) ≈ φ·400
        
        Args:
            T: Maximum height for zeros
            alpha: Decay parameter
            zeros_file: Path to zeros file (optional)
            limit: Maximum number of zeros
            tolerance: Relative tolerance for validation
            
        Returns:
            Tuple of (computed_sum, result, passed) where:
            - computed_sum: The sum S
            - result: S·exp(γ·π)
            - passed: Whether validation passed within tolerance
        """
        # Compute sum
        S = self.compute_zeros_sum(T=T, alpha=alpha, zeros_file=zeros_file, limit=limit)
        
        # Validate against target
        result = S * self.e_gamma_pi
        
        # Check if close to target φ·400
        relative_error = abs(result - self.phi_400) / self.phi_400
        passed = relative_error < tolerance
        
        return S, result, passed
    
    def compute_frequency(self) -> mp.mpf:
        """
        Compute the final frequency using multiple scaling factors.
        
        This implements the complete frequency formula:
        f = f_base × scaling × ψ_eff × δ
        
        where:
        - f_base = 1/(2π)
        - scaling = exp(γ) × √(2πγ) × (φ²/(2π))
        - psi_prime = φ·400·exp(γ·π)
        - log_term = log(ψ'/(2π))
        - ψ_eff = ψ'/(2π·log²(ψ'/(2π)))
        - δ = 1 + (1/φ)·log(γ·π)
        
        Returns:
            Computed frequency in Hz as mpmath mpf object
        """
        # Base frequency
        f_base = 1 / (2 * self.pi)
        
        # Scaling factor
        scaling = (
            mp.exp(self.gamma) * 
            mp.sqrt(2 * self.pi * self.gamma) * 
            (self.phi**2 / (2 * self.pi))
        )
        
        # Psi prime
        psi_prime = self.phi_400 * self.e_gamma_pi
        
        # Log term
        log_term = mp.log(psi_prime / (2 * self.pi))
        
        # Effective psi
        psi_eff = psi_prime / (2 * self.pi * log_term**2)
        
        # Delta correction
        delta = 1 + (1 / self.phi) * mp.log(self.gamma * self.pi)
        
        # Final frequency
        f = f_base * scaling * psi_eff * delta
        
        return f
    
    def run_complete_computation(
        self,
        T: float = 3967.986,
        alpha: float = 0.551020,
        zeros_file: Optional[str] = None,
        limit: int = 3438,
        verbose: bool = True
    ) -> dict:
        """
        Run the complete computation chain and return all results.
        
        This function performs:
        1. Load Riemann zeros
        2. Compute weighted sum
        3. Validate against target
        4. Compute frequency
        
        Args:
            T: Maximum height for zeros
            alpha: Decay parameter
            zeros_file: Path to zeros file (optional)
            limit: Maximum number of zeros
            verbose: Print results if True
            
        Returns:
            Dictionary containing all computed values and validation results
        """
        # Compute sum and validate
        S, result, passed = self.validate_sum(
            T=T, alpha=alpha, zeros_file=zeros_file, limit=limit
        )
        
        # Compute frequency
        f = self.compute_frequency()
        
        # Prepare results
        results = {
            'sum': float(S),
            'sum_str': str(S),
            'validation_result': float(result),
            'target': float(self.phi_400),
            'target_ratio': float(self.target),
            'validation_passed': passed,
            'frequency_hz': float(f),
            'frequency_str': str(f),
            'parameters': {
                'T': T,
                'alpha': alpha,
                'limit': limit,
                'precision': self.dps
            }
        }
        
        # Print if verbose
        if verbose:
            print("=" * 80)
            print("RIEMANN ZEROS FREQUENCY COMPUTATION")
            print("=" * 80)
            print(f"Precision: {self.dps} decimal places")
            print(f"Parameters: T={T}, α={alpha}, limit={limit}")
            print()
            print(f"Suma calculada: S = {S}")
            print(f"Validación: S·exp(γ·π) = {result}")
            print(f"Target: φ·400 = {self.phi_400}")
            print(f"Target ratio: φ·400/exp(γ·π) = {self.target}")
            print(f"Validation: {'✅ PASSED' if passed else '❌ FAILED'}")
            print()
            print(f"Frecuencia: f = {f} Hz")
            print("=" * 80)
        
        return results


def main():
    """
    Main function for standalone execution.
    
    Demonstrates usage of the ZerosFrequencyComputation class.
    """
    import argparse
    
    parser = argparse.ArgumentParser(
        description='Compute frequency from Riemann zeros with golden ratio scaling'
    )
    parser.add_argument('--precision', type=int, default=100,
                        help='Decimal precision (default: 100)')
    parser.add_argument('--T', type=float, default=3967.986,
                        help='Maximum height for zeros (default: 3967.986)')
    parser.add_argument('--alpha', type=float, default=0.551020,
                        help='Decay parameter (default: 0.551020)')
    parser.add_argument('--limit', type=int, default=3438,
                        help='Maximum number of zeros (default: 3438)')
    parser.add_argument('--zeros-file', type=str, default=None,
                        help='Path to zeros file (optional)')
    parser.add_argument('--quiet', action='store_true',
                        help='Suppress verbose output')
    
    args = parser.parse_args()
    
    # Create computation instance
    computation = ZerosFrequencyComputation(dps=args.precision)
    
    # Run complete computation
    results = computation.run_complete_computation(
        T=args.T,
        alpha=args.alpha,
        zeros_file=args.zeros_file,
        limit=args.limit,
        verbose=not args.quiet
    )
    
    return results


if __name__ == '__main__':
    main()
