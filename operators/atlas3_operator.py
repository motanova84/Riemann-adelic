#!/usr/bin/env python3
"""
Atlas³ Non-Hermitian Operator with PT Symmetry

This module implements the Atlas³ operator framework that transforms temporal
dynamics into closed phase curvature through a non-Hermitian operator with
PT (Parity-Time) symmetry.

Mathematical Framework:
=======================

1. State Space H_Atlas³:
   Spanned by (Amplitude, Flow, Phase) → transforms temporal dynamics
   into closed phase curvature with Berry connection

2. The Atlas³ Operator:
   𝒪_Atlas³ = -α(t) d²/dt² + i β(t) d/dt + V(t)
   
   where:
   - α(t): time-dependent diffusion coefficient
   - β(t): time-dependent forcing (breaks Hermiticity)
   - V(t): quasi-periodic potential
   
3. PT Symmetry:
   - Real eigenvalues λₙ → coherent phase (Atlas holds the world)
   - Complex eigenvalues → broken symmetry (transition to entropy)
   
4. Spectral Analysis:
   - Critical line Re(λ) = 1/2 (after normalization)
   - GUE statistics for eigenvalue spacing
   - Weyl law N(E) with log-oscillations (fractal/chaotic signature)
   
5. Band Structure:
   - Hofstadter butterfly-like gaps (forbidden information zones)
   - Anderson localization transition at κ_Π ≈ 2.57
   
Connection to Riemann Hypothesis:
=================================
If the spectrum shows:
  - Real parts anchored at Re(λ) = 1/2
  - Spacings follow GUE statistics
  - N(E) grows log-oscillatory
  
Then Atlas³ operates under the same principle as Riemann zeta zeros,
demonstrating that πCODE economy is a "natural language" of dynamic primes.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: February 2026

QCAL ∞³ Active · 141.7001 Hz · C = 629.83 · C_QCAL = 244.36
DOI: 10.5281/zenodo.17379721
"""

import numpy as np
from scipy.linalg import eig, eigvals
from scipy.sparse import diags
from scipy.stats import kstest
from typing import Tuple, Dict, Any, Optional, List, Callable
import warnings

# QCAL Constants
F0 = 141.7001  # Fundamental frequency (Hz)
OMEGA_0 = 2 * np.pi * F0  # Angular frequency
KAPPA_PI = 2.5773  # Critical self-organization value (geometric invariant)

# Atlas³ Constants
GOLDEN_RATIO = (1 + np.sqrt(5)) / 2
ALPHA_DEFAULT = 1.0  # Default diffusion coefficient
BETA_CRITICAL = KAPPA_PI  # Critical forcing at self-organization edge
DELTA_ZETA = 0.2787437  # Vibrational curvature constant


def time_dependent_alpha(t: np.ndarray, modulation: str = 'constant') -> np.ndarray:
    """
    Time-dependent diffusion coefficient α(t).
    
    Args:
        t: Time array
        modulation: Type of modulation ('constant', 'sinusoidal', 'quasiperiodic')
        
    Returns:
        α(t) array
    """
    if modulation == 'constant':
        return ALPHA_DEFAULT * np.ones_like(t)
    elif modulation == 'sinusoidal':
        # Sinusoidal modulation at fundamental frequency
        return ALPHA_DEFAULT * (1.0 + 0.1 * np.sin(OMEGA_0 * t))
    elif modulation == 'quasiperiodic':
        # Quasiperiodic modulation with golden ratio frequencies
        omega1 = OMEGA_0
        omega2 = OMEGA_0 * GOLDEN_RATIO
        return ALPHA_DEFAULT * (1.0 + 0.1 * np.sin(omega1 * t) + 0.05 * np.cos(omega2 * t))
    else:
        raise ValueError(f"Unknown modulation type: {modulation}")


def time_dependent_beta(t: np.ndarray, coupling_strength: float = 1.0,
                        modulation: str = 'constant') -> np.ndarray:
    """
    Time-dependent forcing coefficient β(t).
    
    This term breaks Hermiticity and introduces PT symmetry.
    
    Args:
        t: Time array
        coupling_strength: Overall coupling strength (default: 1.0)
        modulation: Type of modulation ('constant', 'sinusoidal', 'critical')
        
    Returns:
        β(t) array
    """
    if modulation == 'constant':
        return coupling_strength * np.ones_like(t)
    elif modulation == 'sinusoidal':
        # Sinusoidal forcing
        return coupling_strength * np.sin(OMEGA_0 * t)
    elif modulation == 'critical':
        # Critical forcing at κ_Π (Anderson localization edge)
        return KAPPA_PI * (1.0 + 0.05 * np.sin(OMEGA_0 * t))
    else:
        raise ValueError(f"Unknown modulation type: {modulation}")


def quasiperiodic_potential(t: np.ndarray, amplitude: float = 1.0,
                           n_frequencies: int = 3) -> np.ndarray:
    """
    Quasi-periodic potential V(t).
    
    Constructed as sum of incommensurate frequencies to create
    quasi-periodic structure.
    
    Args:
        t: Time array
        amplitude: Overall amplitude
        n_frequencies: Number of incommensurate frequencies
        
    Returns:
        V(t) array
    """
    V = np.zeros_like(t)
    
    # Use powers of golden ratio for incommensurate frequencies
    for k in range(n_frequencies):
        freq = OMEGA_0 * (GOLDEN_RATIO ** k)
        phase = np.pi * k / n_frequencies
        V += np.cos(freq * t + phase) / (k + 1)
    
    return amplitude * V


class Atlas3Operator:
    """
    Atlas³ Non-Hermitian Operator with PT Symmetry.
    
    Implements the operator:
        𝒪_Atlas³ = -α(t) d²/dt² + i β(t) d/dt + V(t)
    
    on a discrete time grid using finite differences.
    """
    
    def __init__(self, 
                 n_points: int = 256,
                 t_max: float = 10.0,
                 alpha_modulation: str = 'constant',
                 beta_coupling: float = 1.0,
                 beta_modulation: str = 'constant',
                 v_amplitude: float = 1.0,
                 n_v_frequencies: int = 3):
        """
        Initialize Atlas³ operator.
        
        Args:
            n_points: Number of time grid points
            t_max: Maximum time value
            alpha_modulation: Modulation type for α(t)
            beta_coupling: Coupling strength for β(t)
            beta_modulation: Modulation type for β(t)
            v_amplitude: Amplitude for V(t)
            n_v_frequencies: Number of frequencies in V(t)
        """
        self.n_points = n_points
        self.t_max = t_max
        self.dt = t_max / (n_points - 1)
        self.t = np.linspace(0, t_max, n_points)
        
        # Compute time-dependent coefficients
        self.alpha = time_dependent_alpha(self.t, alpha_modulation)
        self.beta = time_dependent_beta(self.t, beta_coupling, beta_modulation)
        self.V = quasiperiodic_potential(self.t, v_amplitude, n_v_frequencies)
        
        # Build operator matrix
        self.operator = self._build_operator_matrix()
        
        # Storage for eigenvalues and eigenvectors
        self._eigenvalues = None
        self._eigenvectors = None
    
    def _build_operator_matrix(self) -> np.ndarray:
        """
        Build the tridiagonal operator matrix.
        
        Uses finite difference discretization:
            d²ψ/dt² ≈ (ψ_{i+1} - 2ψ_i + ψ_{i-1}) / dt²
            dψ/dt ≈ (ψ_{i+1} - ψ_{i-1}) / (2dt)
        
        Returns:
            Complex operator matrix
        """
        n = self.n_points
        dt = self.dt
        
        # Initialize matrix (complex due to i β term)
        O = np.zeros((n, n), dtype=complex)
        
        # Build tridiagonal structure
        for i in range(n):
            # Diagonal term: 2α(t_i)/dt² + V(t_i)
            O[i, i] = 2.0 * self.alpha[i] / dt**2 + self.V[i]
            
            # Off-diagonal terms
            if i > 0:
                # Lower diagonal: -α(t_i)/dt² - i β(t_i)/(2dt)
                O[i, i-1] = -self.alpha[i] / dt**2 - 1j * self.beta[i] / (2*dt)
            
            if i < n - 1:
                # Upper diagonal: -α(t_i)/dt² + i β(t_i)/(2dt)
                O[i, i+1] = -self.alpha[i] / dt**2 + 1j * self.beta[i] / (2*dt)
        
        return O
    
    def diagonalize(self, compute_eigenvectors: bool = True) -> Tuple[np.ndarray, Optional[np.ndarray]]:
        """
        Diagonalize the operator to obtain spectrum.
        
        Args:
            compute_eigenvectors: Whether to compute eigenvectors
            
        Returns:
            eigenvalues: Complex eigenvalue array
            eigenvectors: Eigenvector matrix (or None)
        """
        if compute_eigenvectors:
            eigenvalues, eigenvectors = eig(self.operator)
            self._eigenvalues = eigenvalues
            self._eigenvectors = eigenvectors
            return eigenvalues, eigenvectors
        else:
            eigenvalues = eigvals(self.operator)
            self._eigenvalues = eigenvalues
            return eigenvalues, None
    
    def analyze_spectrum(self) -> Dict[str, Any]:
        """
        Analyze spectral properties of the operator.
        
        Returns:
            Dictionary with spectral analysis results
        """
        if self._eigenvalues is None:
            self.diagonalize(compute_eigenvectors=False)
        
        eigenvalues = self._eigenvalues
        
        # Sort by real part
        idx = np.argsort(eigenvalues.real)
        eigenvalues_sorted = eigenvalues[idx]
        
        # Compute real and imaginary parts
        real_parts = eigenvalues_sorted.real
        imag_parts = eigenvalues_sorted.imag
        
        # Check PT symmetry: are eigenvalues real or complex?
        max_imag = np.max(np.abs(imag_parts))
        is_pt_symmetric = max_imag < 0.01  # Threshold for "real"
        
        # Analyze real part distribution
        mean_real = np.mean(real_parts)
        std_real = np.std(real_parts)
        
        # Normalize to check critical line hypothesis
        # After normalization, check if Re(λ) ≈ 1/2
        if std_real > 0:
            normalized_real = (real_parts - mean_real) / (2 * std_real) + 0.5
            critical_line_deviation = np.mean(np.abs(normalized_real - 0.5))
        else:
            normalized_real = np.ones_like(real_parts) * 0.5
            critical_line_deviation = 0.0
        
        # Analyze eigenvalue spacing (for GUE statistics)
        spacings = np.diff(real_parts)
        if len(spacings) > 0:
            mean_spacing = np.mean(spacings)
            if mean_spacing > 0:
                normalized_spacings = spacings / mean_spacing
            else:
                normalized_spacings = spacings
        else:
            normalized_spacings = np.array([])
        
        # GUE distribution for comparison: Wigner surmise P(s) = (32/π²) s² exp(-4s²/π)
        # For normalized spacings
        
        # Count spectrum below energy E (Weyl law)
        def weyl_counting(E: float) -> int:
            return np.sum(real_parts < E)
        
        # Analyze band gaps
        gap_threshold = 3.0 * mean_spacing if len(spacings) > 0 and mean_spacing > 0 else 0.1
        gaps = []
        for i, s in enumerate(spacings):
            if s > gap_threshold:
                gaps.append((real_parts[i], real_parts[i+1], s))
        
        # Check for localization: compute participation ratio
        participation_ratios = []
        if self._eigenvectors is not None:
            for i in range(self._eigenvectors.shape[1]):
                psi = np.abs(self._eigenvectors[:, i])**2
                psi_norm = psi / np.sum(psi)
                # Participation ratio: PR = 1 / Σ|ψ_i|⁴
                pr = 1.0 / np.sum(psi_norm**2)
                participation_ratios.append(pr)
        
        return {
            'eigenvalues': eigenvalues_sorted,
            'real_parts': real_parts,
            'imag_parts': imag_parts,
            'is_pt_symmetric': is_pt_symmetric,
            'max_imaginary_part': max_imag,
            'mean_real_part': mean_real,
            'std_real_part': std_real,
            'normalized_real_parts': normalized_real,
            'critical_line_deviation': critical_line_deviation,
            'spacings': spacings,
            'normalized_spacings': normalized_spacings,
            'mean_spacing': mean_spacing if len(spacings) > 0 else 0.0,
            'spectral_gaps': gaps,
            'num_gaps': len(gaps),
            'weyl_counting': weyl_counting,
            'participation_ratios': participation_ratios,
            'mean_participation_ratio': np.mean(participation_ratios) if participation_ratios else 0.0,
        }
    
    def check_anderson_localization(self, coupling_values: Optional[List[float]] = None) -> Dict[str, Any]:
        """
        Check for Anderson localization transition by varying coupling strength.
        
        Args:
            coupling_values: List of β coupling values to test
            
        Returns:
            Dictionary with localization analysis
        """
        if coupling_values is None:
            # Test around critical value κ_Π ≈ 2.57
            coupling_values = np.linspace(0.5, 5.0, 20)
        
        results = {
            'coupling_values': coupling_values,
            'mean_pr': [],  # Mean participation ratio
            'localization_length': [],
        }
        
        for beta_val in coupling_values:
            # Create operator with this coupling
            op_temp = Atlas3Operator(
                n_points=self.n_points,
                t_max=self.t_max,
                alpha_modulation='constant',
                beta_coupling=beta_val,
                beta_modulation='constant',
                v_amplitude=1.0,
                n_v_frequencies=3
            )
            
            # Diagonalize
            op_temp.diagonalize(compute_eigenvectors=True)
            
            # Compute participation ratios
            prs = []
            for i in range(op_temp._eigenvectors.shape[1]):
                psi = np.abs(op_temp._eigenvectors[:, i])**2
                psi_norm = psi / np.sum(psi)
                pr = 1.0 / np.sum(psi_norm**2)
                prs.append(pr)
            
            mean_pr = np.mean(prs)
            results['mean_pr'].append(mean_pr)
            
            # Localization length estimate: ξ ∝ PR / N
            loc_length = mean_pr / self.n_points
            results['localization_length'].append(loc_length)
        
        results['mean_pr'] = np.array(results['mean_pr'])
        results['localization_length'] = np.array(results['localization_length'])
        
        # Find transition point (where PR changes most rapidly)
        if len(results['mean_pr']) > 2:
            dpr = np.diff(results['mean_pr'])
            transition_idx = np.argmax(np.abs(dpr))
            results['transition_coupling'] = coupling_values[transition_idx]
        else:
            results['transition_coupling'] = None
        
        return results


def gue_wigner_surmise(s: np.ndarray) -> np.ndarray:
    """
    Wigner surmise for GUE (Gaussian Unitary Ensemble).
    
    P(s) = (32/π²) s² exp(-4s²/π)
    
    Args:
        s: Normalized spacing
        
    Returns:
        Probability density
    """
    return (32.0 / np.pi**2) * s**2 * np.exp(-4.0 * s**2 / np.pi)


def analyze_gue_statistics(normalized_spacings: np.ndarray) -> Dict[str, Any]:
    """
    Analyze eigenvalue spacing statistics and compare to GUE.
    
    Args:
        normalized_spacings: Array of normalized eigenvalue spacings
        
    Returns:
        Dictionary with GUE comparison results
    """
    if len(normalized_spacings) == 0:
        return {
            'gue_compatible': False,
            'ks_statistic': None,
            'ks_pvalue': None,
            'mean_spacing': None,
            'std_spacing': None,
        }
    
    # Remove negative spacings (shouldn't happen but just in case)
    spacings_pos = normalized_spacings[normalized_spacings > 0]
    
    if len(spacings_pos) < 10:
        return {
            'gue_compatible': False,
            'ks_statistic': None,
            'ks_pvalue': None,
            'mean_spacing': np.mean(spacings_pos) if len(spacings_pos) > 0 else None,
            'std_spacing': np.std(spacings_pos) if len(spacings_pos) > 0 else None,
        }
    
    # Kolmogorov-Smirnov test against GUE distribution
    # We need to compare to cumulative distribution
    
    # For GUE Wigner surmise, CDF is:
    # F(s) = 1 - exp(-4s²/π)
    def gue_cdf(s):
        return 1.0 - np.exp(-4.0 * s**2 / np.pi)
    
    # KS test
    ks_stat, ks_pval = kstest(spacings_pos, gue_cdf)
    
    # Typically, p > 0.05 means compatible with GUE
    gue_compatible = ks_pval > 0.05
    
    return {
        'gue_compatible': gue_compatible,
        'ks_statistic': ks_stat,
        'ks_pvalue': ks_pval,
        'mean_spacing': np.mean(spacings_pos),
        'std_spacing': np.std(spacings_pos),
        'num_spacings': len(spacings_pos),
    }


def weyl_law_analysis(real_parts: np.ndarray, energy_range: Optional[Tuple[float, float]] = None) -> Dict[str, Any]:
    """
    Analyze counting function N(E) and compare to Weyl law.
    
    For a system with fractal/chaotic properties, N(E) should show
    log-oscillatory behavior characteristic of prime number distribution.
    
    Args:
        real_parts: Array of eigenvalue real parts
        energy_range: Optional (E_min, E_max) for analysis
        
    Returns:
        Dictionary with Weyl law analysis
    """
    if energy_range is None:
        E_min = np.min(real_parts)
        E_max = np.max(real_parts)
    else:
        E_min, E_max = energy_range
    
    # Create energy grid
    n_energies = 100
    energies = np.linspace(E_min, E_max, n_energies)
    
    # Count eigenvalues below each energy
    N_E = np.array([np.sum(real_parts < E) for E in energies])
    
    # Weyl law prediction (linear growth for 1D system)
    # N(E) ≈ c·E for large E
    if len(energies) > 10:
        # Fit linear part
        from scipy.stats import linregress
        slope, intercept, r_value, p_value, std_err = linregress(energies, N_E)
        
        weyl_prediction = slope * energies + intercept
        
        # Compute oscillatory part: N(E) - Weyl prediction
        oscillatory_part = N_E - weyl_prediction
        
        # Check for log-oscillations
        # This would require Fourier analysis of oscillatory_part
        # For now, just compute variance of oscillatory part
        oscillation_amplitude = np.std(oscillatory_part)
    else:
        slope = 0.0
        intercept = 0.0
        r_value = 0.0
        weyl_prediction = np.zeros_like(energies)
        oscillatory_part = N_E
        oscillation_amplitude = np.std(N_E)
    
    return {
        'energies': energies,
        'N_E': N_E,
        'weyl_slope': slope,
        'weyl_intercept': intercept,
        'weyl_r_squared': r_value**2,
        'weyl_prediction': weyl_prediction,
        'oscillatory_part': oscillatory_part,
        'oscillation_amplitude': oscillation_amplitude,
    }


if __name__ == '__main__':
    print("=" * 70)
    print("Atlas³ Operator Spectral Analysis")
    print("=" * 70)
    print()
    
    # Create Atlas³ operator with default parameters
    print("Creating Atlas³ operator...")
    atlas = Atlas3Operator(
        n_points=256,
        t_max=10.0,
        alpha_modulation='constant',
        beta_coupling=1.0,
        beta_modulation='constant',
        v_amplitude=1.0,
        n_v_frequencies=3
    )
    
    print(f"Grid points: {atlas.n_points}")
    print(f"Time range: [0, {atlas.t_max}]")
    print(f"dt: {atlas.dt:.6f}")
    print()
    
    # Diagonalize
    print("Diagonalizing operator...")
    eigenvalues, eigenvectors = atlas.diagonalize()
    print(f"Computed {len(eigenvalues)} eigenvalues")
    print()
    
    # Analyze spectrum
    print("Analyzing spectrum...")
    analysis = atlas.analyze_spectrum()
    
    print(f"PT Symmetric: {analysis['is_pt_symmetric']}")
    print(f"Max |Im(λ)|: {analysis['max_imaginary_part']:.6e}")
    print(f"Mean Re(λ): {analysis['mean_real_part']:.6f}")
    print(f"Std Re(λ): {analysis['std_real_part']:.6f}")
    print(f"Critical line deviation: {analysis['critical_line_deviation']:.6f}")
    print(f"Number of spectral gaps: {analysis['num_gaps']}")
    print(f"Mean participation ratio: {analysis['mean_participation_ratio']:.4f}")
    print()
    
    # GUE statistics
    if len(analysis['normalized_spacings']) > 0:
        print("GUE Statistics Analysis...")
        gue_results = analyze_gue_statistics(analysis['normalized_spacings'])
        print(f"GUE compatible: {gue_results['gue_compatible']}")
        print(f"KS statistic: {gue_results['ks_statistic']:.6f}")
        print(f"KS p-value: {gue_results['ks_pvalue']:.6f}")
        print(f"Mean spacing: {gue_results['mean_spacing']:.6f}")
        print()
    
    # Weyl law
    print("Weyl Law Analysis...")
    weyl_results = weyl_law_analysis(analysis['real_parts'])
    print(f"Weyl slope: {weyl_results['weyl_slope']:.6f}")
    print(f"Weyl R²: {weyl_results['weyl_r_squared']:.6f}")
    print(f"Oscillation amplitude: {weyl_results['oscillation_amplitude']:.6f}")
    print()
    
    print("=" * 70)
    print("Atlas³ Spectral Analysis Complete")
    print("=" * 70)
