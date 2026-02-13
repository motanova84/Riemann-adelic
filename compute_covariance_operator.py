#!/usr/bin/env python3
"""
compute_covariance_operator.py

Computes modal covariance operator O_nm and adjacency graph A_nm.

This module implements:
1. Covariance operator: O_nm := ⟨φ_n(t)·φ_m(t)⟩_t
2. Modal forcing operator: O_nm := ⟨φ_n φ_m · F(t)⟩ with F(t) = Σ α_k φ_k(t)
3. Adjacency graph: A_nm based on normalized inner products

Mathematical Framework:
    O_nm = ∫₀ᵀ φ_n(t) φ_m(t) dt
    
    For forcing F(t) = Σ_k α_k φ_k(t):
    O_nm^F = ∫₀ᵀ φ_n(t) φ_m(t) F(t) dt

    Adjacency graph:
    A_nm = 1 if ⟨φ_n, φ_m⟩/(‖φ_n‖·‖φ_m‖) > θ, else 0

This enables:
- Modal resonance analysis
- Spectral graph construction
- Curvature emergence detection

QCAL Integration:
    - Coherence C = 244.36 sets threshold scale
    - f₀ = 141.7001 Hz fundamental frequency
    - Compatible with spectral analysis framework

Author: José Manuel Mota Burruezo Ψ ∴ ∞³
Date: February 2026
DOI: 10.5281/zenodo.17379721
"""

import numpy as np
from typing import Optional, Tuple, Callable
import matplotlib.pyplot as plt
from build_orthonormal_basis import OrthonormalFourierBasis

# QCAL Constants
F0 = 141.7001  # Fundamental frequency (Hz)
C_QCAL = 244.36  # QCAL coherence constant


class ModalCovarianceOperator:
    """
    Modal covariance operator and adjacency graph constructor.
    
    Computes:
    1. Covariance matrix O_nm = ⟨φ_n·φ_m⟩
    2. Forcing-weighted operator O_nm = ⟨φ_n·φ_m·F⟩
    3. Adjacency graph A_nm based on threshold
    
    Attributes:
        basis: OrthonormalFourierBasis instance
        O_covariance: Covariance operator matrix
        O_forcing: Forcing-weighted operator matrix
        A_graph: Adjacency graph matrix
    """
    
    def __init__(self, basis: OrthonormalFourierBasis):
        """
        Initialize modal covariance operator.
        
        Args:
            basis: OrthonormalFourierBasis instance
        """
        self.basis = basis
        self.O_covariance = None
        self.O_forcing = None
        self.A_graph = None
        
    def compute_covariance_matrix(self, max_mode: Optional[int] = None) -> np.ndarray:
        """
        Compute covariance operator O_nm = ⟨φ_n(t)·φ_m(t)⟩_t.
        
        For orthonormal basis, this should be identity matrix.
        
        Args:
            max_mode: Maximum mode number (default: basis.n_modes)
            
        Returns:
            Covariance matrix O_nm
        """
        if max_mode is None:
            max_mode = self.basis.n_modes
        
        n_size = max_mode + 1
        O = np.zeros((n_size, n_size))
        
        for n in range(n_size):
            for m in range(n_size):
                O[n, m] = self.basis.compute_inner_product(n, m)
        
        self.O_covariance = O
        return O
    
    def compute_forcing_operator(self, forcing_coeffs: np.ndarray,
                                max_mode: Optional[int] = None) -> np.ndarray:
        """
        Compute forcing operator O_nm = ⟨φ_n φ_m · F(t)⟩.
        
        F(t) = Σ_k α_k φ_k(t) where α_k are forcing_coeffs.
        
        Args:
            forcing_coeffs: Coefficients α_k for forcing F(t)
            max_mode: Maximum mode number (default: basis.n_modes)
            
        Returns:
            Forcing operator matrix O_nm
        """
        if max_mode is None:
            max_mode = min(self.basis.n_modes, len(forcing_coeffs) - 1)
        
        n_size = max_mode + 1
        O_F = np.zeros((n_size, n_size))
        
        # Construct forcing function F(t)
        t = self.basis.t_points
        F_t = self.basis.reconstruct_function(forcing_coeffs, t)
        
        # Compute O_nm = ⟨φ_n φ_m · F⟩
        for n in range(n_size):
            phi_n = self.basis.phi_n(n, t)
            for m in range(n_size):
                phi_m = self.basis.phi_n(m, t)
                integrand = phi_n * phi_m * F_t
                O_F[n, m] = np.trapezoid(integrand, t)
        
        self.O_forcing = O_F
        return O_F
    
    def compute_adjacency_graph(self, theta: float = 0.1,
                               use_forcing: bool = False) -> np.ndarray:
        """
        Compute adjacency graph A_nm based on normalized inner products.
        
        A_nm = 1 if ⟨φ_n, φ_m⟩/(‖φ_n‖·‖φ_m‖) > θ, else 0
        
        Args:
            theta: Threshold for adjacency (default: 0.1)
            use_forcing: Use forcing operator instead of covariance (default: False)
            
        Returns:
            Adjacency matrix A_nm
        """
        if use_forcing and self.O_forcing is not None:
            O = self.O_forcing
        elif self.O_covariance is not None:
            O = self.O_covariance
        else:
            raise ValueError("Must compute covariance or forcing operator first")
        
        n_size = O.shape[0]
        A = np.zeros((n_size, n_size))
        
        # Compute norms (diagonal elements for orthonormal basis)
        norms = np.sqrt(np.diag(O))
        
        for n in range(n_size):
            for m in range(n_size):
                if norms[n] > 1e-12 and norms[m] > 1e-12:
                    normalized_inner = O[n, m] / (norms[n] * norms[m])
                    if abs(normalized_inner) > theta:
                        A[n, m] = 1
        
        self.A_graph = A
        return A
    
    def analyze_graph_properties(self) -> dict:
        """
        Analyze properties of the adjacency graph.
        
        Returns:
            Dictionary with graph properties
        """
        if self.A_graph is None:
            raise ValueError("Must compute adjacency graph first")
        
        A = self.A_graph
        n_size = A.shape[0]
        
        # Degree distribution
        degrees = np.sum(A, axis=1)
        
        # Connected components (simplified analysis)
        n_edges = np.sum(A) / 2  # Undirected graph
        density = n_edges / (n_size * (n_size - 1) / 2) if n_size > 1 else 0
        
        return {
            'n_nodes': n_size,
            'n_edges': int(n_edges),
            'density': density,
            'mean_degree': np.mean(degrees),
            'max_degree': np.max(degrees),
            'min_degree': np.min(degrees)
        }
    
    def visualize_covariance_matrix(self, matrix_type: str = 'covariance',
                                   save_path: Optional[str] = None):
        """
        Visualize covariance or forcing operator matrix.
        
        Args:
            matrix_type: 'covariance' or 'forcing'
            save_path: Path to save figure (if None, display only)
        """
        if matrix_type == 'covariance':
            if self.O_covariance is None:
                raise ValueError("Covariance matrix not computed")
            O = self.O_covariance
            title = "Covariance Operator O_nm = ⟨φ_n·φ_m⟩"
        elif matrix_type == 'forcing':
            if self.O_forcing is None:
                raise ValueError("Forcing operator not computed")
            O = self.O_forcing
            title = "Forcing Operator O_nm = ⟨φ_n·φ_m·F⟩"
        else:
            raise ValueError("matrix_type must be 'covariance' or 'forcing'")
        
        fig, ax = plt.subplots(figsize=(10, 8))
        im = ax.imshow(np.abs(O), cmap='hot', interpolation='nearest')
        ax.set_xlabel('Mode m', fontsize=14)
        ax.set_ylabel('Mode n', fontsize=14)
        ax.set_title(title, fontsize=16)
        plt.colorbar(im, ax=ax, label='|O_nm|')
        
        if save_path:
            plt.savefig(save_path, dpi=150, bbox_inches='tight')
            print(f"✓ Matrix visualization saved to {save_path}")
        else:
            plt.show()
        
        plt.close()
    
    def visualize_adjacency_graph(self, save_path: Optional[str] = None):
        """
        Visualize adjacency graph matrix.
        
        Args:
            save_path: Path to save figure (if None, display only)
        """
        if self.A_graph is None:
            raise ValueError("Adjacency graph not computed")
        
        fig, ax = plt.subplots(figsize=(10, 8))
        im = ax.imshow(self.A_graph, cmap='binary', interpolation='nearest')
        ax.set_xlabel('Mode m', fontsize=14)
        ax.set_ylabel('Mode n', fontsize=14)
        ax.set_title('Adjacency Graph A_nm', fontsize=16)
        plt.colorbar(im, ax=ax, label='Edge')
        
        if save_path:
            plt.savefig(save_path, dpi=150, bbox_inches='tight')
            print(f"✓ Graph visualization saved to {save_path}")
        else:
            plt.show()
        
        plt.close()


def demo_covariance_operator():
    """
    Demonstrate modal covariance operator computation.
    """
    print("=" * 70)
    print("MODAL COVARIANCE OPERATOR COMPUTATION")
    print("QCAL ∞³ Framework - Spectral Graph Analysis")
    print("=" * 70)
    print()
    
    # Initialize basis
    T = 1.0
    n_modes = 20
    basis = OrthonormalFourierBasis(T=T, n_modes=n_modes)
    
    print(f"Period T = {T}")
    print(f"Number of modes: {n_modes}")
    print()
    
    # Initialize covariance operator
    cov_op = ModalCovarianceOperator(basis)
    
    # Compute covariance matrix
    print("Computing covariance matrix O_nm = ⟨φ_n·φ_m⟩...")
    O_cov = cov_op.compute_covariance_matrix(max_mode=10)
    print(f"  Matrix shape: {O_cov.shape}")
    print(f"  Diagonal (should be ~1): {np.diag(O_cov)[:5]}")
    print(f"  Max off-diagonal: {np.max(np.abs(O_cov - np.eye(O_cov.shape[0]))):.2e}")
    print()
    
    # Compute forcing operator with example forcing
    print("Computing forcing operator with F(t) = φ_1(t) + 0.5·φ_3(t)...")
    forcing_coeffs = np.zeros(n_modes + 1)
    forcing_coeffs[1] = 1.0  # φ_1
    forcing_coeffs[3] = 0.5  # φ_3
    
    O_forcing = cov_op.compute_forcing_operator(forcing_coeffs, max_mode=10)
    print(f"  Matrix shape: {O_forcing.shape}")
    print(f"  Norm: {np.linalg.norm(O_forcing):.4f}")
    print()
    
    # Compute adjacency graph
    print("Computing adjacency graph with threshold θ = 0.1...")
    A_graph = cov_op.compute_adjacency_graph(theta=0.1, use_forcing=True)
    
    # Analyze graph properties
    graph_props = cov_op.analyze_graph_properties()
    print(f"  Nodes: {graph_props['n_nodes']}")
    print(f"  Edges: {graph_props['n_edges']}")
    print(f"  Density: {graph_props['density']:.4f}")
    print(f"  Mean degree: {graph_props['mean_degree']:.2f}")
    print()
    
    print("✓ Modal covariance operator computation complete")
    print("=" * 70)


if __name__ == "__main__":
    demo_covariance_operator()
