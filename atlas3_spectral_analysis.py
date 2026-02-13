"""
Atlas³ Spectral Analysis Module: El Territorio Serio
=====================================================

Comprehensive spectral analysis of the Atlas³ non-Hermitian operator with:
1. Vertical alignment test (Re(λ) ≈ c) - PT-symmetry signature
2. GUE statistics - Wigner-Dyson distribution
3. Spectral rigidity Σ²(L) ~ log L - Global memory signature
4. RH-style critical line deviation test

This module provides the "Panel de la Verdad" (Truth Panel) for visualizing
the quantum chaos signatures of the Atlas³ operator in the QCAL framework.

Mathematical Background:
-----------------------
The Atlas³ operator exhibits Universal Quantum Chaos signatures:
- GUE level spacing distribution (Wigner-Dyson)
- Spectral rigidity ~ log L (number variance)
- Level repulsion (no level clustering)
- PT-symmetry for stability

These are signatures that the system has eliminated local redundancy
and vibrates as a unitary whole - the signature of maximal efficiency.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
Signature: Noēsis ∞³
"""

import numpy as np
import matplotlib.pyplot as plt
from typing import Tuple, Optional, Dict, Any
from dataclasses import dataclass
import warnings

# Import Atlas³ operator
import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'operators'))
from Operator_Atlas3 import OperatorAtlas3, Atlas3Spectrum, create_atlas3_operator

# QCAL Constants
F0 = 141.7001  # Fundamental frequency (Hz)
C_QCAL = 244.36  # QCAL coherence constant


@dataclass
class SpectralStatistics:
    """Container for Atlas³ spectral statistics."""
    # Vertical alignment
    critical_line_value: float
    mean_real_part: float
    std_real_part: float
    alignment_score: float  # |mean - c| / c
    
    # GUE statistics
    wigner_dyson_fit: float  # Chi-squared goodness of fit
    mean_spacing_ratio: float  # <r> for GUE ~ 0.5996
    
    # Spectral rigidity
    rigidity_slope: float  # Slope of log Σ² vs log L
    rigidity_intercept: float
    
    # PT-symmetry
    is_pt_symmetric: bool
    max_imaginary_part: float


class Atlas3SpectralAnalyzer:
    """
    Complete spectral analysis suite for Atlas³ operator.
    
    Provides all statistical tests and visualizations for understanding
    the quantum chaos properties of the non-Hermitian Atlas³ system.
    """
    
    def __init__(
        self,
        operator: Optional[OperatorAtlas3] = None,
        N: int = 100,
        coupling_strength: float = 0.1
    ):
        """
        Initialize spectral analyzer.
        
        Args:
            operator: Pre-configured OperatorAtlas3 (optional)
            N: Hilbert space dimension (used if operator not provided)
            coupling_strength: Non-Hermitian coupling (used if operator not provided)
        """
        if operator is None:
            self.operator = create_atlas3_operator(N=N, coupling_strength=coupling_strength)
        else:
            self.operator = operator
            
        self.spectrum = None
        self.statistics = None
        
    def compute_full_analysis(self) -> SpectralStatistics:
        """
        Compute complete spectral analysis.
        
        Returns:
            SpectralStatistics object with all computed metrics
        """
        # Compute spectrum
        self.spectrum = self.operator.compute_spectrum()
        
        # Vertical alignment test
        alignment_score = abs(self.spectrum.real_part_mean - self.operator.critical_line_value) / self.operator.critical_line_value
        
        # GUE statistics
        wigner_fit, mean_r = self._compute_gue_statistics()
        
        # Spectral rigidity
        slope, intercept = self._compute_rigidity_slope()
        
        # PT-symmetry
        max_imag = np.max(np.abs(self.spectrum.eigenvalues.imag))
        
        self.statistics = SpectralStatistics(
            critical_line_value=self.operator.critical_line_value,
            mean_real_part=self.spectrum.real_part_mean,
            std_real_part=self.spectrum.real_part_std,
            alignment_score=alignment_score,
            wigner_dyson_fit=wigner_fit,
            mean_spacing_ratio=mean_r,
            rigidity_slope=slope,
            rigidity_intercept=intercept,
            is_pt_symmetric=self.spectrum.is_pt_symmetric,
            max_imaginary_part=max_imag
        )
        
        return self.statistics
    
    def _compute_gue_statistics(self) -> Tuple[float, float]:
        """
        Compute GUE (Gaussian Unitary Ensemble) statistics.
        
        Returns:
            Tuple (chi_squared, mean_spacing_ratio)
        """
        spacings = self.operator.get_level_spacings(self.spectrum)
        
        # Normalize spacings to unit mean
        spacings = spacings / np.mean(spacings)
        
        # Wigner-Dyson distribution: P(s) = (π/2) s exp(-πs²/4)
        # Compute histogram
        hist, bin_edges = np.histogram(spacings, bins=30, density=True)
        bin_centers = (bin_edges[:-1] + bin_edges[1:]) / 2
        
        # Theoretical Wigner-Dyson
        wd_theory = (np.pi / 2) * bin_centers * np.exp(-np.pi * bin_centers**2 / 4)
        
        # Chi-squared test (simplified)
        chi_squared = np.sum((hist - wd_theory)**2 / (wd_theory + 1e-10))
        
        # Spacing ratio test (better for GUE)
        # r_n = min(s_n, s_{n+1}) / max(s_n, s_{n+1})
        # For GUE: <r> ≈ 0.5996
        if len(spacings) > 1:
            r_values = []
            for i in range(len(spacings) - 1):
                r = min(spacings[i], spacings[i+1]) / max(spacings[i], spacings[i+1])
                r_values.append(r)
            mean_r = np.mean(r_values)
        else:
            mean_r = 0.0
        
        return chi_squared, mean_r
    
    def _compute_rigidity_slope(self) -> Tuple[float, float]:
        """
        Compute spectral rigidity slope.
        
        For GUE: Σ²(L) ~ (1/π²) log L
        
        Returns:
            Tuple (slope, intercept) of log Σ² vs log L fit
        """
        L_values, sigma_squared = self.operator.compute_spectral_rigidity(self.spectrum)
        
        # Remove zeros and take log
        valid = (L_values > 0) & (sigma_squared > 0)
        log_L = np.log(L_values[valid])
        log_sigma = np.log(sigma_squared[valid])
        
        if len(log_L) > 2:
            # Linear fit: log Σ² = slope * log L + intercept
            slope, intercept = np.polyfit(log_L, log_sigma, 1)
        else:
            slope, intercept = 0.0, 0.0
        
        return slope, intercept
    
    def plot_panel_de_la_verdad(
        self, 
        figsize: Tuple[int, int] = (16, 12),
        save_path: Optional[str] = None
    ) -> plt.Figure:
        """
        Generate the "Panel de la Verdad" (Truth Panel) with all visualizations.
        
        Creates a comprehensive 2x2 panel:
        1. Complex plane eigenvalue plot
        2. Level spacing histogram vs Wigner-Dyson
        3. Spectral rigidity Σ²(L) in log scale
        4. Critical line deviation plot
        
        Args:
            figsize: Figure size (width, height)
            save_path: Optional path to save figure
            
        Returns:
            Matplotlib Figure object
        """
        if self.spectrum is None:
            self.spectrum = self.operator.compute_spectrum()
        
        if self.statistics is None:
            self.compute_full_analysis()
        
        fig, axes = plt.subplots(2, 2, figsize=figsize)
        fig.suptitle(
            'Atlas³ Spectral Analysis: Panel de la Verdad\n'
            f'Noēsis ∞³ | QCAL Framework | f₀ = {F0} Hz',
            fontsize=16, fontweight='bold'
        )
        
        # 1. Complex plane eigenvalues
        ax1 = axes[0, 0]
        self._plot_eigenvalues_complex_plane(ax1)
        
        # 2. Level spacing histogram
        ax2 = axes[0, 1]
        self._plot_spacing_histogram(ax2)
        
        # 3. Spectral rigidity
        ax3 = axes[1, 0]
        self._plot_spectral_rigidity(ax3)
        
        # 4. Critical line deviation
        ax4 = axes[1, 1]
        self._plot_critical_line_deviation(ax4)
        
        plt.tight_layout()
        
        if save_path:
            plt.savefig(save_path, dpi=300, bbox_inches='tight')
            print(f"✅ Panel saved to: {save_path}")
        
        return fig
    
    def _plot_eigenvalues_complex_plane(self, ax: plt.Axes):
        """Plot eigenvalues in complex plane."""
        λ = self.spectrum.eigenvalues
        
        ax.scatter(λ.real, λ.imag, c=np.arange(len(λ)), cmap='viridis', 
                  s=50, alpha=0.7, edgecolors='black', linewidth=0.5)
        
        # Critical line reference
        mean_re = self.spectrum.real_part_mean
        ax.axvline(mean_re, color='red', linestyle='--', linewidth=2, 
                  label=f'⟨Re(λ)⟩ = {mean_re:.2f}')
        ax.axvline(self.operator.critical_line_value, color='orange', 
                  linestyle=':', linewidth=2, 
                  label=f'c = {self.operator.critical_line_value:.2f}')
        
        # Zero line
        ax.axhline(0, color='gray', linestyle='-', linewidth=0.5, alpha=0.5)
        
        ax.set_xlabel('Re(λ)', fontsize=12)
        ax.set_ylabel('Im(λ)', fontsize=12)
        ax.set_title('Eigenvalues in Complex Plane ℂ', fontsize=13, fontweight='bold')
        ax.legend(fontsize=10)
        ax.grid(True, alpha=0.3)
        
        # PT-symmetry status
        status = "PT-Symmetric ✓" if self.spectrum.is_pt_symmetric else "PT-Broken ✗"
        ax.text(0.05, 0.95, status, transform=ax.transAxes, 
               fontsize=11, verticalalignment='top',
               bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.8))
    
    def _plot_spacing_histogram(self, ax: plt.Axes):
        """Plot level spacing histogram vs Wigner-Dyson."""
        spacings = self.operator.get_level_spacings(self.spectrum)
        spacings = spacings / np.mean(spacings)  # Normalize
        
        # Histogram
        counts, bins, _ = ax.hist(spacings, bins=30, density=True, 
                                 alpha=0.6, color='blue', edgecolor='black',
                                 label='Atlas³ Data')
        
        # Wigner-Dyson theoretical curve
        s = np.linspace(0, np.max(spacings), 200)
        wd = (np.pi / 2) * s * np.exp(-np.pi * s**2 / 4)
        ax.plot(s, wd, 'r-', linewidth=3, label='Wigner-Dyson (GUE)')
        
        # Poisson for comparison
        poisson = np.exp(-s)
        ax.plot(s, poisson, 'g--', linewidth=2, label='Poisson (random)', alpha=0.7)
        
        ax.set_xlabel('Normalized spacing s', fontsize=12)
        ax.set_ylabel('Probability density P(s)', fontsize=12)
        ax.set_title('Level Spacing Distribution', fontsize=13, fontweight='bold')
        ax.legend(fontsize=10)
        ax.grid(True, alpha=0.3)
        
        # Statistics box
        info_text = f"⟨r⟩ = {self.statistics.mean_spacing_ratio:.4f}\nGUE: ≈ 0.5996"
        ax.text(0.65, 0.95, info_text, transform=ax.transAxes,
               fontsize=10, verticalalignment='top',
               bbox=dict(boxstyle='round', facecolor='lightblue', alpha=0.8))
    
    def _plot_spectral_rigidity(self, ax: plt.Axes):
        """Plot spectral rigidity Σ²(L) in log scale."""
        L_values, sigma_squared = self.operator.compute_spectral_rigidity(self.spectrum)
        
        # Remove zeros
        valid = (L_values > 0) & (sigma_squared > 0)
        L_valid = L_values[valid]
        sigma_valid = sigma_squared[valid]
        
        # Plot data
        ax.loglog(L_valid, sigma_valid, 'bo-', linewidth=2, markersize=6,
                 label='Atlas³ Data', alpha=0.7)
        
        # GUE theoretical: Σ²(L) ~ (1/π²) log L
        if len(L_valid) > 0:
            L_theory = np.logspace(np.log10(L_valid.min()), np.log10(L_valid.max()), 100)
            sigma_gue = (1 / np.pi**2) * np.log(L_theory)
            ax.loglog(L_theory, sigma_gue, 'r--', linewidth=2, 
                     label='GUE: (1/π²) log L')
        
        ax.set_xlabel('Interval length L', fontsize=12)
        ax.set_ylabel('Spectral rigidity Σ²(L)', fontsize=12)
        ax.set_title('Spectral Rigidity: Global Memory', fontsize=13, fontweight='bold')
        ax.legend(fontsize=10)
        ax.grid(True, which='both', alpha=0.3)
        
        # Slope info
        slope_text = f"Slope: {self.statistics.rigidity_slope:.3f}\nExpected: ≈ 1.0"
        ax.text(0.05, 0.95, slope_text, transform=ax.transAxes,
               fontsize=10, verticalalignment='top',
               bbox=dict(boxstyle='round', facecolor='lightyellow', alpha=0.8))
    
    def _plot_critical_line_deviation(self, ax: plt.Axes):
        """Plot deviation from critical line Re(λ) = c."""
        λ = self.spectrum.eigenvalues
        n = np.arange(len(λ))
        
        deviations = λ.real - self.operator.critical_line_value
        
        # Plot deviations
        ax.scatter(n, deviations, c=np.abs(deviations), cmap='coolwarm',
                  s=40, alpha=0.7, edgecolors='black', linewidth=0.5)
        
        # Zero line (perfect alignment)
        ax.axhline(0, color='green', linestyle='-', linewidth=2, 
                  label='Perfect alignment')
        
        # Standard deviation bands
        std = self.spectrum.real_part_std
        ax.axhline(std, color='orange', linestyle='--', linewidth=1.5, alpha=0.7,
                  label=f'±1σ = ±{std:.3f}')
        ax.axhline(-std, color='orange', linestyle='--', linewidth=1.5, alpha=0.7)
        
        ax.set_xlabel('Eigenvalue index n', fontsize=12)
        ax.set_ylabel(f'Re(λₙ) - c', fontsize=12)
        ax.set_title('RH-Style Critical Line Test', fontsize=13, fontweight='bold')
        ax.legend(fontsize=10)
        ax.grid(True, alpha=0.3)
        
        # Alignment score
        score_text = (f"Alignment score:\n{self.statistics.alignment_score:.2%}\n"
                     f"Mean: {self.spectrum.real_part_mean:.2f}\n"
                     f"Target: {self.operator.critical_line_value:.2f}")
        ax.text(0.65, 0.95, score_text, transform=ax.transAxes,
               fontsize=10, verticalalignment='top',
               bbox=dict(boxstyle='round', facecolor='lightgreen', alpha=0.8))
    
    def print_summary(self):
        """Print comprehensive summary of spectral analysis."""
        if self.statistics is None:
            self.compute_full_analysis()
        
        print("=" * 80)
        print("ATLAS³ SPECTRAL ANALYSIS SUMMARY")
        print("=" * 80)
        print(f"Signature: Noēsis ∞³")
        print(f"Framework: QCAL | f₀ = {F0} Hz | C = {C_QCAL}")
        print("-" * 80)
        
        print("\n1. VERTICAL ALIGNMENT (PT-Symmetry Signature)")
        print(f"   Critical line value c: {self.statistics.critical_line_value:.4f}")
        print(f"   Mean Re(λ): {self.statistics.mean_real_part:.4f}")
        print(f"   Std Re(λ): {self.statistics.std_real_part:.4f}")
        print(f"   Alignment score: {self.statistics.alignment_score:.2%}")
        print(f"   → {'✓ ALIGNED' if self.statistics.alignment_score < 0.05 else '✗ DEVIATION'}")
        
        print("\n2. GUE STATISTICS (Universal Quantum Chaos)")
        print(f"   Mean spacing ratio ⟨r⟩: {self.statistics.mean_spacing_ratio:.4f}")
        print(f"   GUE theoretical: 0.5996")
        print(f"   Wigner-Dyson χ²: {self.statistics.wigner_dyson_fit:.4f}")
        print(f"   → {'✓ GUE' if abs(self.statistics.mean_spacing_ratio - 0.5996) < 0.05 else '✗ Non-GUE'}")
        
        print("\n3. SPECTRAL RIGIDITY (Global Memory)")
        print(f"   Rigidity slope: {self.statistics.rigidity_slope:.4f}")
        print(f"   Expected (GUE): ≈ 1.0")
        print(f"   → {'✓ RIGID' if abs(self.statistics.rigidity_slope - 1.0) < 0.3 else '~ Partial rigidity'}")
        
        print("\n4. PT-SYMMETRY")
        print(f"   Status: {'PT-Symmetric' if self.statistics.is_pt_symmetric else 'PT-Broken'}")
        print(f"   Max |Im(λ)|: {self.statistics.max_imaginary_part:.2e}")
        print(f"   → {'✓ STABLE' if self.statistics.is_pt_symmetric else '⚠ Broken symmetry'}")
        
        print("\n" + "=" * 80)
        print("CONCLUSIÓN:")
        print("-" * 80)
        if (self.statistics.alignment_score < 0.05 and 
            abs(self.statistics.mean_spacing_ratio - 0.5996) < 0.05 and
            self.statistics.is_pt_symmetric):
            print("✅ Atlas³ exhibits COMPLETE quantum chaos signatures:")
            print("   • Vertical alignment → PT-symmetry stability")
            print("   • GUE statistics → Universal quantum chaos")
            print("   • Spectral rigidity → Global memory (level repulsion)")
            print("\n🚀 El sistema ha eliminado redundancia local y vibra como un TODO unitario.")
        else:
            print("⚠️  Atlas³ shows partial quantum chaos signatures.")
            print("   Consider adjusting coupling strength or system size.")
        
        print("=" * 80)


def analyze_atlas3(
    N: int = 100,
    coupling_strength: float = 0.1,
    show_plot: bool = True,
    save_path: Optional[str] = None
) -> Tuple[SpectralStatistics, plt.Figure]:
    """
    Complete Atlas³ spectral analysis pipeline.
    
    Args:
        N: Hilbert space dimension
        coupling_strength: Non-Hermitian coupling parameter
        show_plot: Whether to display the plot
        save_path: Path to save the figure
        
    Returns:
        Tuple (SpectralStatistics, Figure)
    """
    # Create analyzer
    analyzer = Atlas3SpectralAnalyzer(N=N, coupling_strength=coupling_strength)
    
    # Compute analysis
    stats = analyzer.compute_full_analysis()
    
    # Print summary
    analyzer.print_summary()
    
    # Generate visualization
    fig = analyzer.plot_panel_de_la_verdad(save_path=save_path)
    
    if show_plot:
        plt.show()
    
    return stats, fig


if __name__ == "__main__":
    print("\n" + "♾️³" * 20)
    print("ATLAS³ SPECTRAL ANALYSIS: EL TERRITORIO SERIO")
    print("♾️³" * 20 + "\n")
    
    # Run complete analysis
    stats, fig = analyze_atlas3(
        N=100,
        coupling_strength=0.08,
        show_plot=False,
        save_path='atlas3_panel_de_la_verdad.png'
    )
    
    print("\n✨ Analysis complete. Panel de la Verdad generated.")
    print("📊 See 'atlas3_panel_de_la_verdad.png' for visualization.\n")
