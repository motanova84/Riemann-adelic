"""
Biological Perturbation Injection for QCAL Riemann Filter
==========================================================

Injects biological signals (HRV, microtubule oscillations) as perturbations
into the Xi operator Hamiltonian to test GUE statistics preservation.

Implements perturbation theory for biological-mathematical coupling.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID: 0009-0002-1923-0773
Date: 2026-02-14
Institution: Instituto de Conciencia Cuántica (ICQ)
DOI: 10.5281/zenodo.17379721
"""

import numpy as np
from typing import Dict, Optional, Union, Tuple
from scipy.interpolate import interp1d
import warnings


class BiologicalPerturbation:
    """
    Biological signal perturbation for spectral operators.
    
    Converts biological time-series data into operator perturbations
    that can be injected into the Riemann spectral filter.
    
    Attributes:
        signal_time (ndarray): Time points of biological signal
        signal_values (ndarray): Amplitude values of biological signal
        perturbation_strength (float): Overall coupling strength
        interpolator: Interpolation function for signal
    """
    
    def __init__(
        self,
        signal_time: np.ndarray,
        signal_values: np.ndarray,
        perturbation_strength: float = 0.01,
        signal_type: str = "hrv"
    ):
        """
        Initialize biological perturbation.
        
        Args:
            signal_time: Time points of signal (seconds)
            signal_values: Signal amplitude values (normalized)
            perturbation_strength: Coupling strength (default: 0.01 = 1%)
            signal_type: Type of biological signal ("hrv", "microtubule", "generic")
        """
        self.signal_time = signal_time
        self.signal_values = signal_values
        self.perturbation_strength = perturbation_strength
        self.signal_type = signal_type
        
        # Normalize signal to [-1, 1] range
        self.signal_normalized = self._normalize_signal(signal_values)
        
        # Create interpolator for signal
        self.interpolator = interp1d(
            signal_time,
            self.signal_normalized,
            kind='cubic',
            bounds_error=False,
            fill_value=0.0
        )
    
    def _normalize_signal(self, signal: np.ndarray) -> np.ndarray:
        """
        Normalize signal to [-1, 1] range.
        
        Args:
            signal: Input signal
            
        Returns:
            Normalized signal
        """
        # Remove mean
        signal_centered = signal - np.mean(signal)
        
        # Normalize to [-1, 1]
        max_abs = np.max(np.abs(signal_centered))
        if max_abs > 0:
            return signal_centered / max_abs
        else:
            return signal_centered
    
    def evaluate_at_points(self, t_points: np.ndarray) -> np.ndarray:
        """
        Evaluate biological signal at given time points.
        
        Args:
            t_points: Time points to evaluate at
            
        Returns:
            Signal values at specified points
        """
        # Map operator grid points to signal time domain
        # Use modulo to handle periodic extension if needed
        t_signal_domain = np.mod(t_points, self.signal_time[-1])
        
        return self.interpolator(t_signal_domain)
    
    def to_diagonal_perturbation(self, operator_grid: np.ndarray) -> np.ndarray:
        """
        Convert biological signal to diagonal perturbation matrix.
        
        Creates a diagonal perturbation:
        V_bio(x,x') = ε·f(x)·δ(x-x')
        
        where f(x) is the biological signal mapped to operator domain.
        
        Args:
            operator_grid: Grid points of operator (e.g., time or position)
            
        Returns:
            Diagonal perturbation values
        """
        signal_at_grid = self.evaluate_at_points(operator_grid)
        return self.perturbation_strength * signal_at_grid
    
    def to_rank1_perturbation(
        self,
        operator_grid: np.ndarray,
        spatial_width: Optional[float] = None
    ) -> np.ndarray:
        """
        Convert biological signal to rank-1 perturbation matrix.
        
        Creates perturbation of form:
        V_bio(x,x') = ε·f(x)·g(x')
        
        where f is biological signal and g is spatial profile.
        
        Args:
            operator_grid: Grid points of operator
            spatial_width: Width parameter for spatial profile (optional)
            
        Returns:
            Full perturbation matrix (N x N)
        """
        n = len(operator_grid)
        signal_at_grid = self.evaluate_at_points(operator_grid)
        
        # Spatial profile (Gaussian or constant)
        if spatial_width is not None:
            x_center = np.mean(operator_grid)
            spatial_profile = np.exp(-((operator_grid - x_center) / spatial_width)**2)
        else:
            spatial_profile = np.ones_like(operator_grid)
        
        # Outer product for rank-1 perturbation
        perturbation_matrix = (
            self.perturbation_strength *
            np.outer(signal_at_grid, spatial_profile)
        )
        
        return perturbation_matrix
    
    def to_local_potential_perturbation(
        self,
        operator_grid: np.ndarray,
        locality_scale: float = 1.0
    ) -> np.ndarray:
        """
        Convert to local potential perturbation.
        
        Creates smooth potential:
        V_bio(x,x') = ε·f(x)·K(|x-x'|/λ)·δ(x-x')
        
        where K is a smoothing kernel.
        
        Args:
            operator_grid: Grid points
            locality_scale: Spatial scale of locality
            
        Returns:
            Diagonal perturbation with smoothing
        """
        signal_at_grid = self.evaluate_at_points(operator_grid)
        
        # Apply Gaussian smoothing
        from scipy.ndimage import gaussian_filter1d
        smoothed_signal = gaussian_filter1d(
            signal_at_grid,
            sigma=locality_scale
        )
        
        return self.perturbation_strength * smoothed_signal


class PerturbedXiOperator:
    """
    Xi Operator with biological perturbation injection.
    
    Extends the standard Xi operator with biological signal perturbations
    while maintaining Hermiticity and tracking GUE statistics.
    
    Attributes:
        base_operator: Original unperturbed operator
        perturbation: BiologicalPerturbation object
        perturbed_hamiltonian: H = H_0 + V_bio
    """
    
    def __init__(
        self,
        base_hamiltonian: np.ndarray,
        operator_grid: np.ndarray,
        perturbation: BiologicalPerturbation,
        perturbation_type: str = "diagonal"
    ):
        """
        Initialize perturbed Xi operator.
        
        Args:
            base_hamiltonian: Unperturbed Hamiltonian matrix
            operator_grid: Grid points (time/position)
            perturbation: BiologicalPerturbation object
            perturbation_type: Type of perturbation ("diagonal", "rank1", "local")
        """
        self.base_hamiltonian = base_hamiltonian
        self.operator_grid = operator_grid
        self.perturbation = perturbation
        self.perturbation_type = perturbation_type
        
        # Generate perturbation matrix
        self.perturbation_matrix = self._generate_perturbation_matrix()
        
        # Create perturbed Hamiltonian
        self.perturbed_hamiltonian = base_hamiltonian + self.perturbation_matrix
        
        # Ensure Hermiticity
        self._ensure_hermiticity()
    
    def _generate_perturbation_matrix(self) -> np.ndarray:
        """Generate perturbation matrix based on type."""
        if self.perturbation_type == "diagonal":
            diag_pert = self.perturbation.to_diagonal_perturbation(self.operator_grid)
            return np.diag(diag_pert)
        
        elif self.perturbation_type == "rank1":
            return self.perturbation.to_rank1_perturbation(self.operator_grid)
        
        elif self.perturbation_type == "local":
            diag_pert = self.perturbation.to_local_potential_perturbation(
                self.operator_grid
            )
            return np.diag(diag_pert)
        
        else:
            raise ValueError(f"Unknown perturbation type: {self.perturbation_type}")
    
    def _ensure_hermiticity(self):
        """Ensure perturbed Hamiltonian is Hermitian."""
        # Symmetrize: H = (H + H†) / 2
        self.perturbed_hamiltonian = (
            self.perturbed_hamiltonian +
            self.perturbed_hamiltonian.conj().T
        ) / 2
    
    def compute_spectrum(self) -> Dict:
        """
        Compute spectrum of perturbed operator.
        
        Returns:
            Dictionary with eigenvalues and statistics
        """
        from scipy.linalg import eigh
        
        eigenvalues, eigenvectors = eigh(self.perturbed_hamiltonian)
        
        return {
            'eigenvalues': eigenvalues,
            'eigenvectors': eigenvectors,
            'n_eigenvalues': len(eigenvalues)
        }
    
    def compute_perturbation_norm(self) -> float:
        """
        Compute operator norm of perturbation.
        
        Returns:
            ||V_bio|| in operator norm
        """
        eigenvals = np.linalg.eigvalsh(self.perturbation_matrix)
        return float(np.max(np.abs(eigenvals)))
    
    def compute_spectral_shift(
        self,
        base_eigenvalues: np.ndarray
    ) -> Tuple[float, float]:
        """
        Compute spectral shift due to perturbation.
        
        Measures how eigenvalues change: δλ = λ_perturbed - λ_base
        
        Args:
            base_eigenvalues: Eigenvalues of unperturbed operator
            
        Returns:
            Tuple of (mean_shift, max_shift)
        """
        perturbed_spectrum = self.compute_spectrum()
        perturbed_eigenvalues = perturbed_spectrum['eigenvalues']
        
        # Match lengths (take minimum)
        n = min(len(base_eigenvalues), len(perturbed_eigenvalues))
        
        shifts = perturbed_eigenvalues[:n] - base_eigenvalues[:n]
        
        mean_shift = float(np.mean(np.abs(shifts)))
        max_shift = float(np.max(np.abs(shifts)))
        
        return mean_shift, max_shift


def create_hrv_perturbation(
    hrv_signal: Dict,
    perturbation_strength: float = 0.01
) -> BiologicalPerturbation:
    """
    Create biological perturbation from HRV signal.
    
    Args:
        hrv_signal: HRVSignal object or dict with 'time' and 'rr_intervals'
        perturbation_strength: Coupling strength
        
    Returns:
        BiologicalPerturbation object
    """
    # Extract time and signal
    if hasattr(hrv_signal, 'time'):
        time = hrv_signal.time
        signal = hrv_signal.rr_intervals
    else:
        time = hrv_signal['time']
        signal = hrv_signal['rr_intervals'] if 'rr_intervals' in hrv_signal else hrv_signal['signal']
    
    return BiologicalPerturbation(
        signal_time=time,
        signal_values=signal,
        perturbation_strength=perturbation_strength,
        signal_type="hrv"
    )


def create_microtubule_perturbation(
    mt_signal: Dict,
    perturbation_strength: float = 0.01
) -> BiologicalPerturbation:
    """
    Create biological perturbation from microtubule oscillation.
    
    Args:
        mt_signal: Dict with 'time' and 'signal' keys
        perturbation_strength: Coupling strength
        
    Returns:
        BiologicalPerturbation object
    """
    return BiologicalPerturbation(
        signal_time=mt_signal['time'],
        signal_values=mt_signal['signal'],
        perturbation_strength=perturbation_strength,
        signal_type="microtubule"
    )


if __name__ == "__main__":
    # Demo usage
    print("=" * 70)
    print("Biological Perturbation Injection Demo")
    print("=" * 70)
    
    # Create synthetic HRV-like signal
    t = np.linspace(0, 100, 1000)
    hrv_signal = np.sin(2*np.pi*0.25*t) + 0.3*np.sin(2*np.pi*0.1*t)
    
    # Create perturbation
    pert = BiologicalPerturbation(
        signal_time=t,
        signal_values=hrv_signal,
        perturbation_strength=0.01
    )
    
    # Test operator grid
    operator_grid = np.linspace(0, 50, 512)
    
    # Generate diagonal perturbation
    diag_pert = pert.to_diagonal_perturbation(operator_grid)
    
    print(f"\n✓ Created biological perturbation:")
    print(f"  Signal duration: {t[-1]:.1f} s")
    print(f"  Perturbation strength: {pert.perturbation_strength}")
    print(f"  Diagonal perturbation range: [{np.min(diag_pert):.6f}, {np.max(diag_pert):.6f}]")
    
    print("\n∴ 𓂀 Ω ∞³")
