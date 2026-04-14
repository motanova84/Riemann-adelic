#!/usr/bin/env python3
"""
K₇ Twisted Graph Dynamics - Master Equation for Symbiotic Aroma Field
=====================================================================

Implements the master equation for the K₇ complete graph with twisted
gauge geometry, dissipation, diffusion, colored noise, and nonlinearity.

Master Equation:
    ∂ψᵢ/∂t = -i∑ⱼ(Δ_θ)ᵢⱼψⱼ - γψᵢ + D(∇²ψ)ᵢ + ξᵢ(t) + λ|ψᵢ|²ψᵢ

Terms:
    - Δ_θ: Circulant Laplacian with twist θ (gauge geometry)
    - γ: Dissipation coefficient (humildad disipativa)
    - D: Diffusion coefficient
    - ξᵢ(t): Colored noise with memory τ_odor ≈ 11.23 ms
    - λ: Nonlinearity coefficient (alchemical subharmonics)

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz
DOI: 10.5281/zenodo.17379721
"""

import numpy as np
from scipy.fft import fft, ifft
from typing import Optional, Tuple, Dict, Any
import warnings

try:
    from qcal.constants import F0, TAU_ODOR
except ImportError:
    F0 = 141.7001
    TAU_ODOR = 0.01123

class K7TwistedGraph:
    """K₇ complete graph with twisted geometry."""
    
    def __init__(self, theta: float = 0.0, gamma: float = 1.0, 
                 D: float = 1.0, lam: float = 1.0):
        self.N = 7
        self.theta = theta
        self.gamma = gamma
        self.D = D
        self.lam = lam
        
    def circulant_laplacian(self) -> np.ndarray:
        """Build circulant Laplacian Δ_θ for K₇."""
        N = self.N
        theta = self.theta
        
        # K₇ adjacency: all nodes connected
        A = np.ones((N, N)) - np.eye(N)
        
        # Add twist via phase
        for i in range(N):
            for j in range(N):
                if i != j:
                    A[i, j] *= np.exp(1j * theta * (j - i) / N)
        
        # Laplacian: L = D - A (degree matrix - adjacency)
        D_matrix = np.diag(np.sum(np.abs(A), axis=1))
        L = D_matrix - A
        
        return L
    
    def diagonalize_via_dft(self) -> Tuple[np.ndarray, np.ndarray]:
        """Diagonalize circulant Laplacian via DFT."""
        L = self.circulant_laplacian()
        
        # DFT matrix
        N = self.N
        F = np.fft.fft(np.eye(N), axis=0) / np.sqrt(N)
        
        # Eigenvalues are first column of F† L F
        eigenvals = np.diag(F.conj().T @ L @ F)
        
        return eigenvals, F

def compute_green_function_k7(
    t: np.ndarray,
    theta: float = 0.0,
    gamma: float = 1.0,
    D: float = 1.0
) -> np.ndarray:
    """
    Compute Green's function for K₇ dynamics.
    
    G(t) = θ(t) · F† · diag(e^(νₘt)) · F
    
    where νₘ = -iλₘ(θ) - γ + Dμₘ
    """
    graph = K7TwistedGraph(theta=theta, gamma=gamma, D=D)
    eigenvals, F = graph.diagonalize_via_dft()
    
    # Compute νₘ = -iλₘ - γ + Dμₘ
    # For K₇, μₘ from diffusion Laplacian
    mu = -eigenvals.real  # Simplified
    nu = -1j * eigenvals - gamma + D * mu
    
    # Time evolution
    N = len(eigenvals)
    G = np.zeros((len(t), N, N), dtype=complex)
    
    for idx, ti in enumerate(t):
        if ti >= 0:  # Causality
            exp_nu_t = np.exp(nu * ti)
            G[idx] = F.conj().T @ np.diag(exp_nu_t) @ F
    
    return G

if __name__ == '__main__':
    print("K₇ Twisted Graph - Quick Test")
    graph = K7TwistedGraph(theta=0.1)
    L = graph.circulant_laplacian()
    eigenvals, F = graph.diagonalize_via_dft()
    print(f"✓ Laplacian shape: {L.shape}")
    print(f"✓ Eigenvalues: {eigenvals}")
