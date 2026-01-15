"""
Horizon Detector for H_Ψ Operator
==================================

Mathematical Foundation:
    Un horizonte no es un lugar; es donde el operador deja de ser invertible.
    
    Formalmente:
        Horizonte ⟺ ker(H_Ψ - λI) ≠ {0}
    
    Es decir:
    - El horizonte ocurre exactamente cuando aparecen autovalores reales
    - Los ceros son puntos donde el resolvente se vuelve singular
    - Un horizonte NO es una ubicación física, sino un punto en el espectro
      donde el operador (H_Ψ - λI) pierde su invertibilidad

Resolvent Theory:
    El resolvente R(λ) = (H_Ψ - λI)⁻¹ es singular precisamente cuando
    λ es un autovalor de H_Ψ. Los "horizontes" son estos puntos singulares.

Implementation:
    This module implements horizon detection by:
    1. Computing the spectrum of H_Ψ (eigenvalues λₙ)
    2. Identifying where ker(H_Ψ - λI) is non-trivial
    3. Analyzing resolvent singularities
    4. Connecting horizons to Riemann zeros via spectral correspondence

Author: José Manuel Mota Burruezo Ψ ∴ ∞³
Date: January 2026
DOI: 10.5281/zenodo.17379721
"""

import numpy as np
from typing import Tuple, List, Optional, Dict
from scipy.linalg import eigh, norm
from scipy.sparse.linalg import eigsh


class HorizonDetector:
    """
    Detector de horizontes espectrales para el operador H_Ψ.
    
    Un horizonte es un punto λ en el espectro donde:
        ker(H_Ψ - λI) ≠ {0}
    
    Es decir, donde el operador (H_Ψ - λI) no es invertible.
    """
    
    def __init__(self, H_psi: np.ndarray, tolerance: float = 1e-10):
        """
        Initialize horizon detector with operator H_Ψ.
        
        Args:
            H_psi: Hermitian operator matrix (n × n)
            tolerance: Numerical tolerance for kernel detection
        """
        self.H_psi = H_psi
        self.tolerance = tolerance
        self.n_dim = H_psi.shape[0]
        
        # Verify Hermiticity
        if not np.allclose(H_psi, H_psi.T.conj(), atol=tolerance):
            raise ValueError("H_Ψ must be Hermitian (self-adjoint)")
        
        # Compute spectrum once for efficiency
        self.eigenvalues, self.eigenvectors = eigh(H_psi)
        
    def is_horizon(self, lambda_val: float) -> bool:
        """
        Determina si λ es un horizonte: ker(H_Ψ - λI) ≠ {0}.
        
        Args:
            lambda_val: Value λ to test
            
        Returns:
            True if λ is a horizon (eigenvalue), False otherwise
        """
        # Un horizonte ocurre cuando λ es un autovalor
        # Es decir, cuando existe v ≠ 0 tal que (H_Ψ - λI)v = 0
        
        # Check if λ is close to any eigenvalue
        for eigenval in self.eigenvalues:
            if abs(eigenval - lambda_val) < self.tolerance:
                return True
        return False
    
    def get_kernel_dimension(self, lambda_val: float) -> int:
        """
        Calcula la dimensión del kernel: dim(ker(H_Ψ - λI)).
        
        Args:
            lambda_val: Value λ
            
        Returns:
            Dimension of the kernel (algebraic multiplicity of eigenvalue)
        """
        # Count eigenvalues close to λ (within tolerance)
        count = np.sum(np.abs(self.eigenvalues - lambda_val) < self.tolerance)
        return int(count)
    
    def get_all_horizons(self) -> np.ndarray:
        """
        Obtiene todos los horizontes (autovalores) del operador H_Ψ.
        
        Returns:
            Array of all horizons (eigenvalues λₙ)
        """
        return self.eigenvalues.copy()
    
    def resolvent_norm(self, lambda_val: float) -> float:
        """
        Calcula la norma del resolvente R(λ) = (H_Ψ - λI)⁻¹.
        
        El resolvente se vuelve singular (||R(λ)|| → ∞) en los horizontes.
        
        Args:
            lambda_val: Value λ (should not be an eigenvalue)
            
        Returns:
            Operator norm of the resolvent ||R(λ)||
            Returns inf if λ is a horizon
        """
        # Check if λ is a horizon
        if self.is_horizon(lambda_val):
            return np.inf
        
        # Compute resolvent using spectral decomposition:
        # R(λ) = Σₙ |ψₙ⟩⟨ψₙ| / (λₙ - λ)
        # where λₙ are eigenvalues and ψₙ are eigenvectors
        
        # The operator norm is the maximum absolute value of 1/(λₙ - λ)
        distances = np.abs(self.eigenvalues - lambda_val)
        
        # Avoid division by very small numbers
        if np.min(distances) < self.tolerance:
            return np.inf
        
        resolvent_eigenvalues = 1.0 / distances
        return np.max(np.abs(resolvent_eigenvalues))
    
    def resolvent_singularity_measure(self, lambda_val: float) -> float:
        """
        Mide qué tan cerca está λ de ser un horizonte.
        
        Returns a measure of singularity:
        - 0.0 if far from any horizon
        - → ∞ as λ approaches a horizon
        
        Args:
            lambda_val: Value λ to test
            
        Returns:
            Singularity measure (reciprocal of distance to nearest eigenvalue)
        """
        # Distance to nearest eigenvalue
        min_distance = np.min(np.abs(self.eigenvalues - lambda_val))
        
        if min_distance < self.tolerance:
            return np.inf
        
        return 1.0 / min_distance
    
    def nearest_horizon(self, lambda_val: float) -> Tuple[float, float]:
        """
        Encuentra el horizonte más cercano a λ.
        
        Args:
            lambda_val: Value λ
            
        Returns:
            (nearest_eigenvalue, distance)
        """
        distances = np.abs(self.eigenvalues - lambda_val)
        nearest_idx = np.argmin(distances)
        return self.eigenvalues[nearest_idx], distances[nearest_idx]
    
    def get_horizon_eigenvector(self, lambda_val: float) -> Optional[np.ndarray]:
        """
        Obtiene el vector propio asociado al horizonte en λ.
        
        Si ker(H_Ψ - λI) ≠ {0}, devuelve un vector v tal que (H_Ψ - λI)v = 0.
        
        Args:
            lambda_val: Eigenvalue λ (should be a horizon)
            
        Returns:
            Eigenvector if λ is a horizon, None otherwise
        """
        # Find eigenvalue closest to λ
        distances = np.abs(self.eigenvalues - lambda_val)
        nearest_idx = np.argmin(distances)
        
        # Check if it's actually close enough to be the same eigenvalue
        if distances[nearest_idx] < self.tolerance:
            return self.eigenvectors[:, nearest_idx]
        
        return None
    
    def analyze_horizon_structure(self) -> Dict:
        """
        Analiza la estructura completa de horizontes del operador.
        
        Returns:
            Dictionary with horizon analysis:
            - 'n_horizons': Number of distinct horizons
            - 'eigenvalues': All eigenvalues (horizons)
            - 'multiplicities': Multiplicity of each eigenvalue
            - 'spectral_gaps': Gaps between consecutive eigenvalues
            - 'min_gap': Minimum spectral gap
            - 'max_gap': Maximum spectral gap
        """
        eigenvals = self.eigenvalues
        n_horizons = len(eigenvals)
        
        # Compute multiplicities (should all be 1 for generic operators)
        unique_vals, multiplicities = np.unique(
            np.round(eigenvals / self.tolerance) * self.tolerance,
            return_counts=True
        )
        
        # Compute spectral gaps
        spectral_gaps = np.diff(eigenvals)
        
        return {
            'n_horizons': n_horizons,
            'eigenvalues': eigenvals,
            'multiplicities': multiplicities,
            'spectral_gaps': spectral_gaps,
            'min_gap': np.min(spectral_gaps) if len(spectral_gaps) > 0 else 0.0,
            'max_gap': np.max(spectral_gaps) if len(spectral_gaps) > 0 else 0.0,
            'mean_gap': np.mean(spectral_gaps) if len(spectral_gaps) > 0 else 0.0,
        }
    
    def riemann_zero_correspondence(self, riemann_zeros: np.ndarray) -> Dict:
        """
        Analiza la correspondencia entre horizontes y ceros de Riemann.
        
        En la teoría espectral de QCAL:
            Horizontes de H_Ψ ↔ Ceros de ζ(s) en Re(s) = 1/2
        
        Args:
            riemann_zeros: Known Riemann zeros γₙ
            
        Returns:
            Dictionary with correspondence analysis:
            - 'n_zeros': Number of Riemann zeros
            - 'n_horizons': Number of horizons
            - 'max_error': Maximum |λₙ - γₙ|
            - 'mean_error': Mean error
            - 'errors': Array of individual errors
        """
        n_zeros = len(riemann_zeros)
        n_horizons = len(self.eigenvalues)
        
        # Take minimum of the two for comparison
        n_compare = min(n_zeros, n_horizons)
        
        # Compute errors
        errors = np.abs(self.eigenvalues[:n_compare] - riemann_zeros[:n_compare])
        
        return {
            'n_zeros': n_zeros,
            'n_horizons': n_horizons,
            'n_compared': n_compare,
            'max_error': np.max(errors),
            'mean_error': np.mean(errors),
            'median_error': np.median(errors),
            'std_error': np.std(errors),
            'errors': errors,
        }


def detect_horizons_from_operator(H_psi: np.ndarray, 
                                   tolerance: float = 1e-10) -> np.ndarray:
    """
    Función de conveniencia para detectar horizontes en un operador.
    
    Args:
        H_psi: Hermitian operator matrix
        tolerance: Numerical tolerance
        
    Returns:
        Array of horizons (eigenvalues)
    """
    detector = HorizonDetector(H_psi, tolerance=tolerance)
    return detector.get_all_horizons()


def validate_horizon_riemann_correspondence(H_psi: np.ndarray,
                                            riemann_zeros: np.ndarray,
                                            tolerance: float = 1e-10) -> bool:
    """
    Valida que los horizontes de H_Ψ correspondan a los ceros de Riemann.
    
    Args:
        H_psi: Hermitian operator matrix
        riemann_zeros: Known Riemann zeros
        tolerance: Numerical tolerance for matching
        
    Returns:
        True if horizons match Riemann zeros within tolerance
    """
    detector = HorizonDetector(H_psi, tolerance=tolerance)
    correspondence = detector.riemann_zero_correspondence(riemann_zeros)
    
    # Check if maximum error is within tolerance
    return correspondence['max_error'] < tolerance


# Export main classes and functions
__all__ = [
    'HorizonDetector',
    'detect_horizons_from_operator',
    'validate_horizon_riemann_correspondence',
]
