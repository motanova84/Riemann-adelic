"""
Spectral Operator H_ε for Riemann Hypothesis Validation

This module implements the perturbed spectral operator:
    H_ε = H₀ + λ M_{Ω_{ε,R}}

where:
- H₀ = -d²/dt² is the base Laplacian operator
- M_{Ω_{ε,R}} is the multiplication operator by the oscillatory potential:
  
    Ω_{ε,R}(t) = [1 / (1 + (t/R)²)] * Σ_{n=1}^∞ cos((log p_n)t) / n^{1+ε}

- λ ≈ 141.7001 is the spectral coupling factor
- p_n are prime numbers

The eigenvalues of H_ε provide a spectral measure μ_ε that should correlate
with the distribution of Riemann zeta zeros on the critical line.

Mathematical Foundation:
    - Discretization uses tridiagonal finite difference for H₀
    - Potential Ω computed via truncated prime sum
    - Total operator H_ε = H₀ + λ diag(Ω)
    - Eigenvalues extracted via eigh_tridiagonal for efficiency

References:
    - Burruezo, J.M. (2025). DOI: 10.5281/zenodo.17116291
    - Section 3.2: Adelic Spectral Systems
"""

import numpy as np
from scipy.linalg import eigh_tridiagonal
from sympy import prime
import matplotlib.pyplot as plt
from typing import Tuple, Optional


def compute_oscillatory_potential(
    t: np.ndarray,
    epsilon: float = 0.01,
    R: float = 5.0,
    n_primes: int = 200
) -> np.ndarray:
    """
    Compute the oscillatory potential Ω_{ε,R}(t).
    
    The potential combines:
    1. Prime oscillations: cos((log p_n)t) weighted by 1/n^{1+ε}
    2. Envelope decay: 1/(1 + (t/R)²) for localization
    
    Args:
        t: Array of evaluation points
        epsilon: Convergence parameter (ε > 0, typically 0.01)
        R: Envelope decay scale (typically 5-20)
        n_primes: Number of primes in truncated sum (typically 100-500)
        
    Returns:
        Ω: Oscillatory potential values at points t
        
    Note:
        Higher n_primes increases accuracy but computation time.
        The sum converges due to the n^{-(1+ε)} decay.
    """
    Ω = np.zeros_like(t)
    
    # Compute truncated sum over primes
    for n in range(1, n_primes + 1):
        p = prime(n)
        log_p = np.log(float(p))
        weight = 1.0 / (n ** (1.0 + epsilon))
        Ω += weight * np.cos(log_p * t)
    
    # Apply envelope for localization
    envelope = 1.0 / (1.0 + (t / R) ** 2)
    Ω *= envelope
    
    return Ω


def build_H_epsilon_operator(
    N: int = 200,
    T: float = 20.0,
    epsilon: float = 0.01,
    R: float = 5.0,
    lambda_coupling: float = 141.7001,
    n_primes: int = 200
) -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
    """
    Build the spectral operator H_ε as a tridiagonal matrix.
    
    The operator is discretized on the interval [-T, T] with N points:
        H_ε = H₀ + λ M_{Ω_{ε,R}}
    
    where:
    - H₀ is the discrete Laplacian: -d²/dt² ≈ (2δ_ii - δ_{i,i±1})/dt²
    - M_{Ω_{ε,R}} is diagonal multiplication by Ω_{ε,R}(t)
    
    Args:
        N: Discretization dimension (number of grid points)
        T: Half-width of interval [-T, T]
        epsilon: Convergence parameter for potential
        R: Envelope scale parameter
        lambda_coupling: Spectral coupling factor (λ ≈ 141.7001)
        n_primes: Number of primes in potential sum
        
    Returns:
        t: Grid points in [-T, T]
        H_diag: Diagonal of H_ε operator
        H_offdiag: Off-diagonal of H_ε operator (tridiagonal structure)
        
    Note:
        Returns tridiagonal form for efficient eigenvalue computation
        with scipy.linalg.eigh_tridiagonal.
    """
    # Create uniform grid
    t = np.linspace(-T, T, N)
    dt = t[1] - t[0]
    
    # Build H₀ (discrete Laplacian)
    # Central difference: -d²f/dt² ≈ (f_{i-1} - 2f_i + f_{i+1})/dt²
    H0_diag = np.full(N, 2.0) / (dt ** 2)
    H0_offdiag = np.full(N - 1, -1.0) / (dt ** 2)
    
    # Compute oscillatory potential
    Omega = compute_oscillatory_potential(t, epsilon, R, n_primes)
    
    # Build total operator: H_ε = H₀ + λ diag(Ω)
    H_diag = H0_diag + lambda_coupling * Omega
    H_offdiag = H0_offdiag.copy()
    
    return t, H_diag, H_offdiag


def compute_spectral_measure(
    N: int = 200,
    T: float = 20.0,
    epsilon: float = 0.01,
    R: float = 5.0,
    lambda_coupling: float = 141.7001,
    n_primes: int = 200
) -> Tuple[np.ndarray, np.ndarray]:
    """
    Compute the spectral measure μ_ε from eigenvalues of H_ε.
    
    The spectral measure is:
        μ_ε = Σ_n δ_{λ_n}
    
    where {λ_n} are the eigenvalues of H_ε, sorted in ascending order.
    
    Args:
        N: Discretization dimension
        T: Half-width of interval
        epsilon: Convergence parameter
        R: Envelope scale
        lambda_coupling: Spectral coupling factor
        n_primes: Number of primes
        
    Returns:
        eigenvalues: Eigenvalues of H_ε (spectral measure support)
        eigenvectors: Corresponding eigenvectors (for visualization)
        
    Note:
        Uses eigh_tridiagonal for efficient O(N²) computation
        instead of full O(N³) dense eigendecomposition.
    """
    # Build operator
    t, H_diag, H_offdiag = build_H_epsilon_operator(
        N, T, epsilon, R, lambda_coupling, n_primes
    )
    
    # Compute eigenvalues and eigenvectors
    eigenvalues, eigenvectors = eigh_tridiagonal(H_diag, H_offdiag)
    
    return eigenvalues, eigenvectors


def load_riemann_zeros(
    filename: str = 'zeros/zeros_t1e3.txt',
    max_zeros: Optional[int] = None
) -> np.ndarray:
    """
    Load Riemann zeta zeros from file.
    
    The file contains imaginary parts γ of non-trivial zeros ρ = 1/2 + iγ
    of the Riemann zeta function ζ(s).
    
    Args:
        filename: Path to zeros file (one value per line)
        max_zeros: Maximum number of zeros to load (None = all)
        
    Returns:
        zeros: Array of zero imaginary parts γ
        
    Note:
        The zeros measure ν = Σ_ρ δ_{Im(ρ)} should correlate
        with the spectral measure μ_ε from H_ε.
    """
    zeros = []
    with open(filename, 'r') as f:
        for i, line in enumerate(f):
            if max_zeros is not None and i >= max_zeros:
                break
            try:
                gamma = float(line.strip())
                zeros.append(gamma)
            except ValueError:
                continue
    
    return np.array(zeros)


def plot_spectral_comparison(
    mu_epsilon: np.ndarray,
    zeta_zeros: np.ndarray,
    n_points: int = 50,
    save_path: Optional[str] = None
) -> None:
    """
    Create visual comparison of spectral measure μ_ε and zeta zeros ν.
    
    Plots:
    1. Overlay of first n_points eigenvalues vs zeros
    2. Histogram comparison showing distributions
    
    Args:
        mu_epsilon: Eigenvalues of H_ε (spectral measure)
        zeta_zeros: Imaginary parts of Riemann zeros
        n_points: Number of points to plot
        save_path: Path to save figure (None = display only)
        
    Note:
        The correlation quantifies how well H_ε captures
        the spectral properties of the Riemann zeta function.
    """
    # Ensure we don't exceed array bounds
    n_mu = min(n_points, len(mu_epsilon))
    n_zeros = min(n_points, len(zeta_zeros))
    
    fig, axes = plt.subplots(2, 1, figsize=(12, 8))
    
    # Plot 1: Overlay comparison
    ax1 = axes[0]
    ax1.plot(range(n_mu), mu_epsilon[:n_mu], 'bo-', 
             label=r'$\mu_\varepsilon$: espectro $H_\varepsilon$',
             markersize=5, linewidth=1.5)
    ax1.plot(range(n_zeros), zeta_zeros[:n_zeros], 'rx--',
             label=r'$\nu$: ceros de $\zeta(s)$',
             markersize=7, linewidth=1.5)
    ax1.set_xlabel('Índice n')
    ax1.set_ylabel('Valor')
    ax1.set_title(r'Comparación: $\mu_\varepsilon$ vs ceros de $\zeta(s)$')
    ax1.legend()
    ax1.grid(True, alpha=0.3)
    
    # Plot 2: Histogram comparison
    ax2 = axes[1]
    ax2.hist(mu_epsilon[:n_mu], bins=20, alpha=0.5, 
             label=r'$\mu_\varepsilon$', color='blue', density=True)
    ax2.hist(zeta_zeros[:n_zeros], bins=20, alpha=0.5,
             label=r'$\nu$', color='red', density=True)
    ax2.set_xlabel('Valor')
    ax2.set_ylabel('Densidad normalizada')
    ax2.set_title('Distribución de las medidas espectrales')
    ax2.legend()
    ax2.grid(True, alpha=0.3)
    
    plt.tight_layout()
    
    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches='tight')
        print(f"✅ Figure saved to {save_path}")
    else:
        plt.show()
    
    plt.close()


if __name__ == "__main__":
    print("=" * 80)
    print("SIMULACIÓN DEL OPERADOR H_ε Y COMPARACIÓN ESPECTRAL")
    print("=" * 80)
    print()
    
    # Parameters
    N = 200
    T = 20.0
    epsilon = 0.01
    R = 5.0
    lambda_coupling = 141.7001
    n_primes = 200
    
    print(f"Parámetros de simulación:")
    print(f"  N (dimensión): {N}")
    print(f"  T (intervalo): [-{T}, {T}]")
    print(f"  ε (convergencia): {epsilon}")
    print(f"  R (escala): {R}")
    print(f"  λ (acoplamiento): {lambda_coupling}")
    print(f"  n_primos: {n_primes}")
    print()
    
    # Compute spectral measure
    print("🔄 Calculando espectro de H_ε...")
    eigenvalues, _ = compute_spectral_measure(N, T, epsilon, R, lambda_coupling, n_primes)
    print(f"✅ Espectro calculado: {len(eigenvalues)} eigenvalores")
    print(f"   Rango: [{eigenvalues[0]:.4f}, {eigenvalues[-1]:.4f}]")
    print()
    
    # Load Riemann zeros
    print("🔄 Cargando ceros de ζ(s)...")
    try:
        zeta_zeros = load_riemann_zeros(max_zeros=200)
        print(f"✅ Ceros cargados: {len(zeta_zeros)} valores")
        print(f"   Rango: [{zeta_zeros[0]:.4f}, {zeta_zeros[-1]:.4f}]")
        print()
    except FileNotFoundError:
        print("⚠️  Archivo de ceros no encontrado, usando valores sintéticos")
        zeta_zeros = np.linspace(14.0, 150.0, 50)
        print()
    
    # Compare
    print("🔄 Generando comparación visual...")
    plot_spectral_comparison(
        eigenvalues, 
        zeta_zeros, 
        n_points=50,
        save_path='operador_H_epsilon_comparison.png'
    )
    
    # Print first few values for comparison
    print("\nPrimeros 10 valores de cada medida:")
    print("-" * 50)
    print(f"{'n':<5} {'μ_ε (H_ε)':<20} {'ν (ζ zeros)':<20}")
    print("-" * 50)
    for i in range(min(10, len(eigenvalues), len(zeta_zeros))):
        print(f"{i:<5} {eigenvalues[i]:<20.6f} {zeta_zeros[i]:<20.6f}")
    print("-" * 50)
    print()
    print("✅ Simulación completa")
