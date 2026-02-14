"""
GUE Statistics Validation for Perturbed Systems
================================================

Validates preservation of Gaussian Unitary Ensemble (GUE) statistics
after biological perturbation injection.

Implements statistical tests for Random Matrix Theory properties.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID: 0009-0002-1923-0773
Date: 2026-02-14
Institution: Instituto de Conciencia Cuántica (ICQ)
DOI: 10.5281/zenodo.17379721
"""

import numpy as np
from typing import Dict, Tuple, Optional
from scipy import stats
from dataclasses import dataclass


@dataclass
class GUEStatistics:
    """Container for GUE statistical measures."""
    rigidity: float  # Spectral rigidity Δ₃
    level_spacing_ratio: float  # Mean spacing ratio
    wigner_surmise_fit: float  # Fit to Wigner surmise
    nearest_neighbor_variance: float  # NN spacing variance
    is_gue_compatible: bool  # Overall GUE compatibility
    metadata: Dict


class GUEValidator:
    """
    Validates GUE statistics for eigenvalue spectra.
    
    Tests for Random Matrix Theory signatures:
    - Level repulsion (Wigner surmise)
    - Spectral rigidity (Δ₃ statistic)
    - Nearest-neighbor spacing distribution
    
    Attributes:
        tolerance (float): Tolerance for GUE compatibility tests
    """
    
    def __init__(self, tolerance: float = 0.2):
        """
        Initialize GUE validator.
        
        Args:
            tolerance: Relative tolerance for GUE tests (default: 20%)
        """
        self.tolerance = tolerance
    
    def unfold_spectrum(self, eigenvalues: np.ndarray) -> np.ndarray:
        """
        Unfold spectrum to have unit mean spacing.
        
        This removes the density of states ρ(E) to focus on
        fluctuations in level spacings.
        
        Args:
            eigenvalues: Raw eigenvalue spectrum
            
        Returns:
            Unfolded eigenvalues with mean spacing = 1
        """
        # Sort eigenvalues
        eigs_sorted = np.sort(eigenvalues)
        
        # Smooth integrated density of states
        n_eigs = len(eigs_sorted)
        cumulative = np.arange(n_eigs) / n_eigs
        
        # Fit polynomial to get smooth N(E)
        poly_degree = min(5, n_eigs // 10)
        poly_coeffs = np.polyfit(eigs_sorted, cumulative, poly_degree)
        smooth_cumulative = np.polyval(poly_coeffs, eigs_sorted)
        
        # Unfolded spectrum: ξ_n = N(E_n)
        unfolded = smooth_cumulative * n_eigs
        
        return unfolded
    
    def compute_nearest_neighbor_spacings(
        self,
        eigenvalues: np.ndarray,
        unfold: bool = True
    ) -> np.ndarray:
        """
        Compute nearest-neighbor level spacings.
        
        Args:
            eigenvalues: Eigenvalue spectrum
            unfold: Whether to unfold spectrum first
            
        Returns:
            Array of normalized spacings s_i
        """
        if unfold:
            eigs = self.unfold_spectrum(eigenvalues)
        else:
            eigs = np.sort(eigenvalues)
        
        # Compute spacings
        spacings = np.diff(eigs)
        
        # Normalize to unit mean spacing
        mean_spacing = np.mean(spacings)
        if mean_spacing > 0:
            normalized_spacings = spacings / mean_spacing
        else:
            normalized_spacings = spacings
        
        return normalized_spacings
    
    def wigner_surmise_pdf(self, s: np.ndarray) -> np.ndarray:
        """
        Wigner surmise for GUE level spacing distribution.
        
        P_GUE(s) = (32/π²)·s²·exp(-4s²/π)
        
        Args:
            s: Spacing values
            
        Returns:
            PDF values
        """
        return (32.0 / np.pi**2) * s**2 * np.exp(-4.0 * s**2 / np.pi)
    
    def compute_spacing_ratio(self, eigenvalues: np.ndarray) -> float:
        """
        Compute mean level spacing ratio.
        
        For GUE, <r> ≈ 0.5996
        
        Args:
            eigenvalues: Eigenvalue spectrum
            
        Returns:
            Mean spacing ratio
        """
        spacings = self.compute_nearest_neighbor_spacings(eigenvalues, unfold=True)
        
        if len(spacings) < 2:
            return 0.0
        
        # Compute ratios r_n = min(s_n, s_{n+1}) / max(s_n, s_{n+1})
        ratios = []
        for i in range(len(spacings) - 1):
            s_min = min(spacings[i], spacings[i+1])
            s_max = max(spacings[i], spacings[i+1])
            if s_max > 0:
                ratios.append(s_min / s_max)
        
        return float(np.mean(ratios)) if ratios else 0.0
    
    def compute_spectral_rigidity(
        self,
        eigenvalues: np.ndarray,
        L: Optional[float] = None
    ) -> float:
        """
        Compute Dyson-Mehta Δ₃ spectral rigidity statistic.
        
        For GUE: Δ₃(L) ≈ (1/π²)[ln(2πL) - 0.007] for large L
        
        Args:
            eigenvalues: Eigenvalue spectrum
            L: Window length (default: ~15% of spectrum)
            
        Returns:
            Δ₃ statistic
        """
        # Unfold spectrum
        unfolded = self.unfold_spectrum(eigenvalues)
        n = len(unfolded)
        
        if L is None:
            L = max(10, int(0.15 * n))
        
        # Compute spectral staircase deviations
        delta3_values = []
        
        for i in range(n - int(L)):
            window = unfolded[i:i+int(L)]
            
            # Best-fit linear function in window
            x = np.arange(len(window))
            A = np.vstack([x, np.ones(len(x))]).T
            m, c = np.linalg.lstsq(A, window, rcond=None)[0]
            
            # Deviation from best fit
            fit = m * x + c
            deviation = window - fit
            
            # Δ₃ = (1/L)·∫|N(E) - fit|² dE
            delta3 = np.mean(deviation**2)
            delta3_values.append(delta3)
        
        return float(np.mean(delta3_values)) if delta3_values else 0.0
    
    def test_wigner_surmise_fit(
        self,
        eigenvalues: np.ndarray,
        n_bins: int = 30
    ) -> float:
        """
        Test fit to Wigner surmise distribution.
        
        Uses Kolmogorov-Smirnov test to compare spacing distribution
        with theoretical GUE prediction.
        
        Args:
            eigenvalues: Eigenvalue spectrum
            n_bins: Number of bins for histogram
            
        Returns:
            KS test p-value (higher = better fit)
        """
        spacings = self.compute_nearest_neighbor_spacings(eigenvalues)
        
        # Theoretical CDF for Wigner surmise (GUE)
        def wigner_cdf(s):
            return 1 - np.exp(-4.0 * s**2 / np.pi)
        
        # KS test
        try:
            ks_stat, p_value = stats.kstest(
                spacings,
                lambda s: wigner_cdf(s)
            )
            return float(p_value)
        except:
            return 0.0
    
    def validate_gue_statistics(
        self,
        eigenvalues: np.ndarray
    ) -> GUEStatistics:
        """
        Complete GUE statistics validation.
        
        Args:
            eigenvalues: Eigenvalue spectrum
            
        Returns:
            GUEStatistics object with all measures
        """
        # Compute statistics
        rigidity = self.compute_spectral_rigidity(eigenvalues)
        spacing_ratio = self.compute_spacing_ratio(eigenvalues)
        wigner_fit = self.test_wigner_surmise_fit(eigenvalues)
        
        spacings = self.compute_nearest_neighbor_spacings(eigenvalues)
        nn_variance = float(np.var(spacings))
        
        # GUE compatibility checks
        # Expected values for GUE:
        # - Spacing ratio: ~0.60
        # - Rigidity: proportional to ln(L)
        # - NN variance: ~0.286 (for normalized spacings)
        
        ratio_ok = abs(spacing_ratio - 0.60) < self.tolerance
        variance_ok = abs(nn_variance - 0.286) < self.tolerance
        
        is_compatible = ratio_ok and variance_ok
        
        metadata = {
            'n_eigenvalues': len(eigenvalues),
            'spacing_ratio_expected': 0.60,
            'nn_variance_expected': 0.286,
            'tolerance': self.tolerance
        }
        
        return GUEStatistics(
            rigidity=rigidity,
            level_spacing_ratio=spacing_ratio,
            wigner_surmise_fit=wigner_fit,
            nearest_neighbor_variance=nn_variance,
            is_gue_compatible=is_compatible,
            metadata=metadata
        )
    
    def compare_gue_statistics(
        self,
        baseline_eigenvalues: np.ndarray,
        perturbed_eigenvalues: np.ndarray
    ) -> Dict:
        """
        Compare GUE statistics before and after perturbation.
        
        Args:
            baseline_eigenvalues: Unperturbed spectrum
            perturbed_eigenvalues: Perturbed spectrum
            
        Returns:
            Comparison dictionary with preservation metrics
        """
        baseline_stats = self.validate_gue_statistics(baseline_eigenvalues)
        perturbed_stats = self.validate_gue_statistics(perturbed_eigenvalues)
        
        # Compute relative changes
        rigidity_change = abs(
            (perturbed_stats.rigidity - baseline_stats.rigidity) /
            (baseline_stats.rigidity + 1e-10)
        )
        
        ratio_change = abs(
            (perturbed_stats.level_spacing_ratio - baseline_stats.level_spacing_ratio) /
            (baseline_stats.level_spacing_ratio + 1e-10)
        )
        
        variance_change = abs(
            (perturbed_stats.nearest_neighbor_variance - baseline_stats.nearest_neighbor_variance) /
            (baseline_stats.nearest_neighbor_variance + 1e-10)
        )
        
        # Check if GUE is preserved (relative changes < tolerance)
        gue_preserved = (
            rigidity_change < self.tolerance and
            ratio_change < self.tolerance and
            variance_change < self.tolerance
        )
        
        return {
            'baseline': baseline_stats,
            'perturbed': perturbed_stats,
            'rigidity_change_percent': rigidity_change * 100,
            'spacing_ratio_change_percent': ratio_change * 100,
            'variance_change_percent': variance_change * 100,
            'gue_preserved': gue_preserved,
            'tolerance_percent': self.tolerance * 100
        }


if __name__ == "__main__":
    # Demo usage
    print("=" * 70)
    print("GUE Statistics Validation Demo")
    print("=" * 70)
    
    # Generate GUE-like spectrum (Gaussian random matrix)
    n = 500
    H = np.random.randn(n, n) + 1j * np.random.randn(n, n)
    H = (H + H.conj().T) / (2 * np.sqrt(n))  # Hermitian, normalized
    
    eigenvalues = np.linalg.eigvalsh(H)
    
    # Validate GUE statistics
    validator = GUEValidator()
    stats = validator.validate_gue_statistics(eigenvalues)
    
    print(f"\n✓ GUE Statistics:")
    print(f"  Spectral rigidity Δ₃: {stats.rigidity:.6f}")
    print(f"  Level spacing ratio: {stats.level_spacing_ratio:.4f} (expected: 0.60)")
    print(f"  NN variance: {stats.nearest_neighbor_variance:.4f} (expected: 0.286)")
    print(f"  Wigner fit p-value: {stats.wigner_surmise_fit:.4f}")
    print(f"  GUE compatible: {stats.is_gue_compatible}")
    
    print("\n∴ 𓂀 Ω ∞³")
