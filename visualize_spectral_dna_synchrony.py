#!/usr/bin/env python3
"""
Visualize Spectral DNA Synchrony: Fredholm Determinant vs. Riemann Xi Function
==============================================================================

This module creates the synchrony visualization showing the alignment between:
- log|det(t-H)| (Fredholm determinant of operator H, magenta)
- Re log ξ(1/2+it) (Real part of log Riemann xi function, cyan)
- Critical zeros (vertical gray lines)

The visualization demonstrates the "Brutal Evidence" that the operator H
successfully captures the Riemann zeta zeros.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID: 0009-0002-1923-0773
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: March 2026
DOI: 10.5281/zenodo.17379721
QCAL ∞³ Framework
"""

import numpy as np
import matplotlib
matplotlib.use('Agg')  # Headless backend
import matplotlib.pyplot as plt
from pathlib import Path
import json
from typing import Tuple, List, Optional
import mpmath as mp

# High precision
mp.mp.dps = 50

# QCAL Constants
F0_QCAL = 141.7001  # Hz


def get_riemann_zeros_in_range(t_min: float, t_max: float, max_zeros: int = 50) -> List[float]:
    """
    Get Riemann zeta zeros in the specified range using mpmath.
    
    Args:
        t_min: Minimum t value
        t_max: Maximum t value
        max_zeros: Maximum number of zeros to return
        
    Returns:
        List of imaginary parts of zeros
    """
    zeros = []
    
    # Start from the first zero above t_min
    n = 1
    
    while len(zeros) < max_zeros:
        try:
            # Get the n-th zero
            zero = float(mp.zetazero(n).imag)
            
            if zero > t_max:
                break
            
            if zero >= t_min:
                zeros.append(zero)
            
            n += 1
            
            if n > 10000:  # Safety limit
                break
        except:
            break
    
    return zeros


def load_spectral_dna_result(filename: str = "spectral_dna_omega_v3_result.json") -> dict:
    """
    Load spectral DNA result from JSON file.
    
    Args:
        filename: Input filename
        
    Returns:
        Result dictionary
    """
    with open(filename, 'r') as f:
        return json.load(f)


def create_synchrony_plot(t_values: np.ndarray,
                          fredholm_log_det: np.ndarray,
                          xi_log_values: np.ndarray,
                          riemann_zeros: List[float],
                          output_filename: str = "spectral_dna_omega_v3_synchrony.png",
                          title: str = "Espejo de Fredholm: Sincronía con ξ(s)",
                          dpi: int = 300) -> None:
    """
    Create the synchrony visualization plot.
    
    Args:
        t_values: Array of t values
        fredholm_log_det: log|det(t-H)| values
        xi_log_values: Re log ξ(1/2+it) values
        riemann_zeros: List of critical zeros
        output_filename: Output file path
        title: Plot title
        dpi: Resolution
    """
    fig, ax = plt.subplots(figsize=(16, 6))
    
    # Plot vertical lines for critical zeros (gray dashed)
    for zero in riemann_zeros:
        ax.axvline(x=zero, color='gray', linestyle='--', linewidth=0.5, alpha=0.6, zorder=1)
    
    # Plot Re log ξ(1/2+it) (cyan, "Verdad")
    ax.plot(t_values, np.real(xi_log_values), 
            color='cyan', linewidth=2, label='Oscilaciones Re log ξ(s) (Verdad)', zorder=3)
    
    # Plot log|det(t-H)| (magenta dashed, "Espejo")
    ax.plot(t_values, np.real(fredholm_log_det), 
            color='magenta', linestyle='--', linewidth=2, 
            label='log |det(t - H)| (Espejo)', zorder=2)
    
    # Styling
    ax.set_xlabel('t', fontsize=14)
    ax.set_ylabel('Amplitud', fontsize=14)
    ax.set_title(title, fontsize=16, fontweight='bold')
    ax.legend(loc='upper right', fontsize=12, framealpha=0.9)
    ax.grid(True, alpha=0.3, linestyle=':', linewidth=0.5)
    
    # Set background
    ax.set_facecolor('#f8f8f8')
    fig.patch.set_facecolor('white')
    
    # Tight layout
    plt.tight_layout()
    
    # Save
    output_path = Path(output_filename)
    plt.savefig(output_path, dpi=dpi, bbox_inches='tight', facecolor='white')
    plt.close()
    
    print(f"📊 Synchrony plot saved to: {output_path}")


def create_eigenvalue_distribution_plot(eigenvalues: np.ndarray,
                                         output_filename: str = "spectral_dna_omega_v3_eigenvalues.png",
                                         dpi: int = 300) -> None:
    """
    Create eigenvalue distribution plot showing the first 50 eigenvalues.
    
    Args:
        eigenvalues: Array of eigenvalues
        output_filename: Output file path
        dpi: Resolution
    """
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 5))
    
    # Plot 1: First 50 eigenvalues
    n_plot = min(50, len(eigenvalues))
    indices = np.arange(1, n_plot + 1)
    
    ax1.scatter(indices, eigenvalues[:n_plot], color='darkblue', s=50, alpha=0.7, edgecolors='black')
    ax1.plot(indices, eigenvalues[:n_plot], color='blue', linewidth=1, alpha=0.5)
    ax1.set_xlabel('Index n', fontsize=12)
    ax1.set_ylabel('Eigenvalue λₙ', fontsize=12)
    ax1.set_title('I. Los Autovalores de la Verdad (λᵢ)', fontsize=14, fontweight='bold')
    ax1.grid(True, alpha=0.3)
    ax1.set_facecolor('#f8f8f8')
    
    # Plot 2: Spacing distribution (GUE validation)
    if len(eigenvalues) > 1:
        spacings = np.diff(eigenvalues)
        mean_spacing = np.mean(spacings)
        normalized_spacings = spacings / mean_spacing
        
        ax2.hist(normalized_spacings, bins=30, color='darkgreen', alpha=0.7, edgecolor='black', density=True)
        
        # Overlay Wigner surmise (GUE)
        s = np.linspace(0, np.max(normalized_spacings), 200)
        wigner = (np.pi / 2) * s * np.exp(-np.pi * s**2 / 4)
        ax2.plot(s, wigner, 'r-', linewidth=2, label='Wigner Surmise (GUE)')
        
        ax2.set_xlabel('Normalized Spacing s/⟨s⟩', fontsize=12)
        ax2.set_ylabel('Probability Density P(s)', fontsize=12)
        ax2.set_title('Repulsión de Niveles (GUE)', fontsize=14, fontweight='bold')
        ax2.legend(fontsize=10)
        ax2.grid(True, alpha=0.3)
        ax2.set_facecolor('#f8f8f8')
    
    plt.tight_layout()
    
    output_path = Path(output_filename)
    plt.savefig(output_path, dpi=dpi, bbox_inches='tight', facecolor='white')
    plt.close()
    
    print(f"📊 Eigenvalue distribution plot saved to: {output_path}")


def visualize_spectral_dna(fredholm_log_det: Optional[np.ndarray] = None,
                            xi_log_values: Optional[np.ndarray] = None,
                            t_values: Optional[np.ndarray] = None,
                            eigenvalues: Optional[np.ndarray] = None,
                            result_file: str = "spectral_dna_omega_v3_result.json",
                            t_range: Tuple[float, float] = (10.0, 100.0)) -> None:
    """
    Create all visualizations for spectral DNA analysis.
    
    Args:
        fredholm_log_det: Fredholm determinant values (if None, load from file)
        xi_log_values: Xi function values (if None, load from file)
        t_values: t parameter values (if None, load from file)
        eigenvalues: Eigenvalue array (if None, load from file)
        result_file: JSON result file to load if arrays not provided
        t_range: Range for t values
    """
    print("=" * 70)
    print(" VISUALIZING SPECTRAL DNA SYNCHRONY")
    print(" QCAL ∞³ · Riemann Hypothesis Validation")
    print("=" * 70)
    print()
    
    # Load data if not provided
    if any(x is None for x in [fredholm_log_det, xi_log_values, t_values, eigenvalues]):
        print("📂 Loading spectral DNA result...")
        
        try:
            result = load_spectral_dna_result(result_file)
            
            # Reload eigenvalues from CSV
            import pandas as pd
            eigenvalues_df = pd.read_csv("eigenvalues_omega_v3.csv")
            eigenvalues = eigenvalues_df['eigenvalue'].values
            
            # Recompute Fredholm and Xi if needed
            if fredholm_log_det is None or xi_log_values is None or t_values is None:
                print("⚙️  Recomputing Fredholm determinant and Xi function...")
                
                n_t_points = result['parameters'].get('n_t_points', 500)
                t_values = np.linspace(t_range[0], t_range[1], n_t_points)
                
                # Import from spectral DNA extractor
                from operators.spectral_dna_omega_extractor import (
                    compute_fredholm_log_determinant,
                    compute_riemann_xi_log
                )
                
                fredholm_log_det = np.zeros(n_t_points, dtype=complex)
                xi_log_values = np.zeros(n_t_points, dtype=complex)
                
                for i, t in enumerate(t_values):
                    if i % 100 == 0:
                        print(f"   Progress: {i}/{n_t_points}")
                    fredholm_log_det[i] = compute_fredholm_log_determinant(eigenvalues, t)
                    xi_log_values[i] = compute_riemann_xi_log(t)
                
                print("   Computation complete.")
        
        except FileNotFoundError:
            print(f"❌ Error: Result file '{result_file}' not found.")
            print("   Please run spectral_dna_omega_extractor.py first.")
            return
    
    print()
    
    # Get Riemann zeros in range
    print(f"🔍 Finding Riemann zeros in range t ∈ [{t_range[0]}, {t_range[1]}]...")
    riemann_zeros = get_riemann_zeros_in_range(t_range[0], t_range[1], max_zeros=50)
    print(f"   Found {len(riemann_zeros)} zeros")
    print()
    
    # Create synchrony plot
    print("📊 Creating synchrony visualization...")
    create_synchrony_plot(
        t_values=t_values,
        fredholm_log_det=fredholm_log_det,
        xi_log_values=xi_log_values,
        riemann_zeros=riemann_zeros,
        output_filename="spectral_dna_omega_v3_synchrony.png"
    )
    print()
    
    # Create eigenvalue distribution plot
    print("📊 Creating eigenvalue distribution plot...")
    create_eigenvalue_distribution_plot(
        eigenvalues=eigenvalues,
        output_filename="spectral_dna_omega_v3_eigenvalues.png"
    )
    print()
    
    print("=" * 70)
    print(" VISUALIZATION COMPLETE")
    print("=" * 70)
    print()
    print("✓ Synchrony plot: spectral_dna_omega_v3_synchrony.png")
    print("✓ Eigenvalue plot: spectral_dna_omega_v3_eigenvalues.png")
    print()


if __name__ == "__main__":
    visualize_spectral_dna()
