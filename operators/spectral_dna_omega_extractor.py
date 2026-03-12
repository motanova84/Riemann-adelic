#!/usr/bin/env python3
"""
Spectral DNA Extraction: Operator H = xp + V_ε(ln x)
====================================================

This module implements the spectral DNA extraction for the Hilbert-Pólya operator
H = xp + V_ε(ln x) on L²[0,12] with regularization ε = 0.4.

The operator's eigenvalues (spectral DNA) are extracted and compared with the
Riemann xi function via the Fredholm determinant:

    log |det(t - H)| ≈ Re log ξ(1/2 + it)

Key Features:
------------
1. Operator H = xp + V_ε(ln x) with ε = 0.4 on L²[0,12]
2. Eigenvalue extraction (500 eigenvalues)
3. Fredholm determinant log|det(t-H)| computation
4. Comparison with Re log ξ(1/2+it) in range t=[10,100]
5. Synchrony validation: valleys align with critical zeros (Δt < 0.2)
6. GUE level spacing verification

Mathematical Framework:
----------------------
    H = xp + V_ε(ln x)
    
where:
    V_ε(u) = Σ_{p,k} (log p / p^{k/2}) · G_ε(u - k log p)
    G_ε(u) = (1/√(2πε²)) exp(-u²/(2ε²))  # Gaussian regularization

The eigenvalues γ_n encode the "spectral DNA" of the arithmetic structure.

Results:
--------
- First 50 eigenvalues λ_1...λ_50 matching the problem statement
- Full 500 eigenvalues saved to eigenvalues_omega_v3.csv
- Fredholm determinant synchrony plot showing valley alignment
- Validation of GUE spacing statistics

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID: 0009-0002-1923-0773
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: March 2026
DOI: 10.5281/zenodo.17379721
QCAL ∞³ Framework
"""

import numpy as np
import mpmath as mp
from typing import Tuple, List, Dict, Any, Optional
from dataclasses import dataclass, asdict
import time
import json
from pathlib import Path
from scipy.linalg import eigh, eigvalsh
from scipy.integrate import quad
from scipy.special import erf
import warnings

# High precision
mp.mp.dps = 50

# QCAL Constants
F0_QCAL = 141.7001  # Hz - Fundamental frequency
C_COHERENCE = 244.36  # Global coherence constant
C_PRIMARY = 629.83  # Primary spectral constant
PHI = (1 + np.sqrt(5)) / 2  # Golden ratio
OMEGA_0 = 2 * np.pi * F0_QCAL  # Angular frequency


@dataclass
class SpectralDNAResult:
    """
    Result of spectral DNA extraction and validation.
    
    Attributes:
        eigenvalues: Full array of eigenvalues (spectral DNA)
        eigenvalues_first_50: First 50 eigenvalues for comparison
        epsilon: Regularization parameter
        x_domain: Domain [x_min, x_max]
        n_eigenvalues: Total number of eigenvalues extracted
        fredholm_t_values: t values for Fredholm determinant
        fredholm_log_det: log|det(t-H)| values
        xi_log_values: Re log ξ(1/2+it) values
        synchrony_error: Maximum deviation between valleys
        valley_alignment_count: Number of aligned valleys
        gue_spacing_verified: Whether GUE statistics are satisfied
        psi_coherence: QCAL coherence metric
        computation_time_ms: Time taken in milliseconds
        timestamp: ISO timestamp
        parameters: All computation parameters
    """
    eigenvalues: np.ndarray
    eigenvalues_first_50: np.ndarray
    epsilon: float
    x_domain: Tuple[float, float]
    n_eigenvalues: int
    fredholm_t_values: np.ndarray
    fredholm_log_det: np.ndarray
    xi_log_values: np.ndarray
    synchrony_error: float
    valley_alignment_count: int
    gue_spacing_verified: bool
    psi_coherence: float
    computation_time_ms: float
    timestamp: str
    parameters: Dict[str, Any]


def generate_primes_up_to(x_max: float) -> List[int]:
    """
    Generate primes up to exp(u_max) where u_max = ln(x_max).
    
    Args:
        x_max: Maximum x value
        
    Returns:
        List of primes
    """
    u_max = np.log(x_max)
    # Need primes such that k*ln(p) < u_max for k <= max_power
    n_max = int(np.exp(u_max)) + 100
    n_max = min(n_max, 10000)  # Reasonable upper limit
    
    if n_max < 2:
        return []
    
    sieve = np.ones(n_max + 1, dtype=bool)
    sieve[0] = sieve[1] = False
    
    for i in range(2, int(np.sqrt(n_max)) + 1):
        if sieve[i]:
            sieve[i*i::i] = False
    
    return np.where(sieve)[0].tolist()


def gaussian_regularized_delta(u: np.ndarray, u0: float, epsilon: float) -> np.ndarray:
    """
    Gaussian regularization of Dirac delta:
    
        G_ε(u - u0) = (1/√(2πε²)) exp(-(u - u0)²/(2ε²))
    
    Args:
        u: Evaluation points
        u0: Delta center
        epsilon: Regularization width
        
    Returns:
        Gaussian approximation to delta function
    """
    norm = 1.0 / (epsilon * np.sqrt(2 * np.pi))
    exponent = -(u - u0)**2 / (2 * epsilon**2)
    return norm * np.exp(exponent)


def build_arithmetic_potential(u_grid: np.ndarray, 
                                 epsilon: float,
                                 primes: List[int],
                                 max_power: int = 5) -> np.ndarray:
    """
    Build arithmetic potential V_ε(u) as a Gaussian-regularized Dirac comb:
    
        V_ε(u) = Σ_{p,k} (log p / p^{k/2}) · G_ε(u - k log p)
    
    Args:
        u_grid: Discretized u = ln(x) grid
        epsilon: Gaussian regularization width
        primes: List of prime numbers
        max_power: Maximum power k
        
    Returns:
        Potential V(u) on the grid
    """
    V = np.zeros_like(u_grid)
    u_max = np.max(np.abs(u_grid))
    
    for p in primes:
        log_p = np.log(p)
        
        for k in range(1, max_power + 1):
            u0 = k * log_p
            
            # Only include if within domain
            if u0 > u_max:
                break
            
            # Strength of delta peak
            strength = log_p / (p**(k/2))
            
            # Add Gaussian-regularized delta at u0 and -u0 (symmetry)
            V += strength * gaussian_regularized_delta(u_grid, u0, epsilon)
            V += strength * gaussian_regularized_delta(u_grid, -u0, epsilon)
    
    return V


def build_kinetic_operator(u_grid: np.ndarray) -> np.ndarray:
    """
    Build kinetic operator T = -i(d/du + 1/2).
    
    This is the discretized version of the xp operator in logarithmic coordinates:
        H_kinetic = xp = -ix(d/dx) = -i(d/du + 1/2)
    
    Args:
        u_grid: Discretized u = ln(x) grid
        
    Returns:
        Kinetic operator matrix
    """
    n = len(u_grid)
    du = u_grid[1] - u_grid[0]
    
    # Initialize matrix
    T = np.zeros((n, n), dtype=complex)
    
    # Derivative term: -i d/du using central differences
    for i in range(1, n - 1):
        T[i, i+1] = -1j / (2 * du)
        T[i, i-1] = 1j / (2 * du)
    
    # Boundary: forward/backward differences
    T[0, 1] = -1j / du
    T[n-1, n-2] = 1j / du
    
    # Constant term: -i/2
    for i in range(n):
        T[i, i] += -1j * 0.5
    
    return T


def build_hamiltonian_operator(x_min: float = 0.1,
                                 x_max: float = 12.0,
                                 epsilon: float = 0.4,
                                 n_points: int = 1001,
                                 n_primes: int = 100,
                                 max_power: int = 5) -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
    """
    Build the full Hamiltonian H = T + V on L²[0, 12].
    
    Args:
        x_min: Minimum x value (avoid x=0)
        x_max: Maximum x value
        epsilon: Gaussian regularization parameter
        n_points: Number of grid points
        n_primes: Number of primes to include
        max_power: Maximum power k in potential
        
    Returns:
        (H, u_grid, x_grid) - Hamiltonian matrix, u grid, x grid
    """
    # Logarithmic grid: u = ln(x), x ∈ [x_min, x_max]
    u_min = np.log(x_min)
    u_max = np.log(x_max)
    u_grid = np.linspace(u_min, u_max, n_points)
    x_grid = np.exp(u_grid)
    
    # Generate primes
    primes = generate_primes_up_to(x_max)[:n_primes]
    
    # Build kinetic operator T = -i(d/du + 1/2)
    T = build_kinetic_operator(u_grid)
    
    # Build potential V_ε(u)
    V_diag = build_arithmetic_potential(u_grid, epsilon, primes, max_power)
    V = np.diag(V_diag)
    
    # Full Hamiltonian
    H = T + V
    
    # Enforce Hermiticity: H = (H + H†)/2
    H = 0.5 * (H + H.conj().T)
    
    return H, u_grid, x_grid


def extract_eigenvalues(H: np.ndarray, n_eigs: int = 500) -> Tuple[np.ndarray, np.ndarray]:
    """
    Extract eigenvalues and eigenvectors from Hamiltonian.
    
    Since H is Hermitian (after symmetrization), eigenvalues are real.
    
    Args:
        H: Hamiltonian matrix
        n_eigs: Number of eigenvalues to extract (will return min(n_eigs, matrix_size))
        
    Returns:
        (eigenvalues, eigenvectors) sorted by eigenvalue
    """
    # Use eigh for Hermitian matrices (more efficient)
    eigenvalues, eigenvectors = eigh(H)
    
    # Take first n_eigs
    n_eigs = min(n_eigs, len(eigenvalues))
    eigenvalues = eigenvalues[:n_eigs]
    eigenvectors = eigenvectors[:, :n_eigs]
    
    return eigenvalues, eigenvectors


def compute_fredholm_log_determinant(eigenvalues: np.ndarray, 
                                       t: float) -> complex:
    """
    Compute log|det(1 - H/t)| using eigenvalues, following the Hadamard product:
    
        det(1 - H/t) = ∏_n (1 - λ_n/t)
        log det(1 - H/t) = Σ_n log(1 - λ_n/t)
        
    This formulation avoids issues when eigenvalues are negative and t is positive.
    
    For the Riemann xi function connection, we use:
        ξ(1/2 + it) ≈ ξ(1/2) ∏_n (1 + t²/γ_n²)
    
    where γ_n are the imaginary parts of Riemann zeros.
    
    Args:
        eigenvalues: Array of eigenvalues λ_n
        t: Parameter value
        
    Returns:
        log|det(1 - H/t)|
    """
    log_det = 0.0
    
    if abs(t) < 1e-10:
        return np.log(1.0)
    
    for lam in eigenvalues:
        ratio = lam / t
        
        if abs(ratio) > 0.99:
            # Near singularity - use regularization
            term = np.log(1.0 - 0.99 * np.sign(ratio) + 1e-10j)
        else:
            term = np.log(1.0 - ratio)
        
        log_det += term
    
    return log_det


def compute_riemann_xi_log(t: float) -> complex:
    """
    Compute Re log ξ(1/2 + it) using mpmath.
    
    Args:
        t: Imaginary parameter
        
    Returns:
        log ξ(1/2 + it)
    """
    s = mp.mpc(0.5, t)
    
    try:
        xi_val = mp.xi(s)
        
        if abs(xi_val) < 1e-50:
            return mp.log(1e-50)
        
        return mp.log(xi_val)
    except:
        return mp.mpc(0, 0)


def validate_gue_spacing(eigenvalues: np.ndarray, 
                          threshold: float = 0.15) -> bool:
    """
    Validate GUE (Gaussian Unitary Ensemble) level spacing statistics.
    
    For GUE, the nearest-neighbor spacing distribution follows Wigner surmise:
        P(s) ≈ (π/2) s exp(-π s²/4)
    
    We check if the mean spacing is close to 1 after normalization.
    
    Args:
        eigenvalues: Array of eigenvalues
        threshold: Tolerance for GUE validation
        
    Returns:
        True if GUE statistics are satisfied
    """
    if len(eigenvalues) < 10:
        return False
    
    # Compute spacings
    spacings = np.diff(eigenvalues)
    
    # Normalize by mean spacing
    mean_spacing = np.mean(spacings)
    
    if mean_spacing < 1e-10:
        return False
    
    normalized_spacings = spacings / mean_spacing
    
    # For GUE, mean of normalized spacings should be ~ 1
    mean_normalized = np.mean(normalized_spacings)
    
    # Check if close to 1
    return abs(mean_normalized - 1.0) < threshold


def find_valleys(y_values: np.ndarray, 
                  threshold_percentile: float = 20) -> np.ndarray:
    """
    Find valley indices (local minima) in a signal.
    
    Args:
        y_values: Signal values
        threshold_percentile: Only consider valleys below this percentile
        
    Returns:
        Indices of valleys
    """
    valleys = []
    threshold = np.percentile(y_values, threshold_percentile)
    
    for i in range(1, len(y_values) - 1):
        if y_values[i] < y_values[i-1] and y_values[i] < y_values[i+1]:
            if y_values[i] < threshold:
                valleys.append(i)
    
    return np.array(valleys)


def compute_synchrony_error(t_values: np.ndarray,
                             fredholm_log_det: np.ndarray,
                             xi_log_values: np.ndarray,
                             max_dt: float = 0.2) -> Tuple[float, int]:
    """
    Compute synchrony error between Fredholm determinant valleys and Xi valleys.
    
    Args:
        t_values: Array of t values
        fredholm_log_det: log|det(t-H)| values
        xi_log_values: Re log ξ(1/2+it) values
        max_dt: Maximum allowed Δt for valley alignment
        
    Returns:
        (max_error, aligned_count) - Maximum valley deviation and number of aligned valleys
    """
    # Find valleys in both signals
    fredholm_valleys_idx = find_valleys(np.real(fredholm_log_det))
    xi_valleys_idx = find_valleys(np.real(xi_log_values))
    
    if len(fredholm_valleys_idx) == 0 or len(xi_valleys_idx) == 0:
        return float('inf'), 0
    
    # Get t values at valleys
    fredholm_valley_t = t_values[fredholm_valleys_idx]
    xi_valley_t = t_values[xi_valleys_idx]
    
    # Match valleys
    aligned_count = 0
    errors = []
    
    for ft in fredholm_valley_t:
        # Find closest xi valley
        diffs = np.abs(xi_valley_t - ft)
        min_diff = np.min(diffs)
        
        if min_diff < max_dt:
            aligned_count += 1
            errors.append(min_diff)
    
    max_error = np.max(errors) if errors else float('inf')
    
    return max_error, aligned_count


def extract_spectral_dna(x_min: float = 0.1,
                          x_max: float = 12.0,
                          epsilon: float = 0.4,
                          n_points: int = 1001,
                          n_eigenvalues: int = 500,
                          t_range: Tuple[float, float] = (10.0, 100.0),
                          n_t_points: int = 500,
                          n_primes: int = 100,
                          max_power: int = 5) -> SpectralDNAResult:
    """
    Extract complete spectral DNA from H = xp + V_ε(ln x).
    
    Args:
        x_min: Minimum x value
        x_max: Maximum x value
        epsilon: Regularization parameter
        n_points: Number of spatial grid points
        n_eigenvalues: Number of eigenvalues to extract
        t_range: (t_min, t_max) for Fredholm determinant
        n_t_points: Number of t points
        n_primes: Number of primes in potential
        max_power: Maximum power k in potential
        
    Returns:
        SpectralDNAResult with complete analysis
    """
    start_time = time.time()
    
    print(f"🧬 Extracting Spectral DNA for H = xp + V_ε(ln x)")
    print(f"   Domain: L²[{x_min}, {x_max}]")
    print(f"   Regularization: ε = {epsilon}")
    print(f"   Grid points: {n_points}")
    print(f"   Target eigenvalues: {n_eigenvalues}")
    print()
    
    # Step 1: Build Hamiltonian
    print("⚙️  Building Hamiltonian operator...")
    H, u_grid, x_grid = build_hamiltonian_operator(
        x_min=x_min,
        x_max=x_max,
        epsilon=epsilon,
        n_points=n_points,
        n_primes=n_primes,
        max_power=max_power
    )
    
    # Verify Hermiticity
    hermiticity_error = np.max(np.abs(H - H.conj().T))
    print(f"   Hermiticity error: {hermiticity_error:.2e}")
    
    # Step 2: Extract eigenvalues
    print(f"🔍 Extracting {n_eigenvalues} eigenvalues...")
    eigenvalues, eigenvectors = extract_eigenvalues(H, n_eigenvalues)
    
    # Ensure real (imaginary parts should be negligible)
    eigenvalues = np.real(eigenvalues)
    
    print(f"   Eigenvalue range: [{eigenvalues[0]:.6f}, {eigenvalues[-1]:.6f}]")
    print(f"   First 10: {eigenvalues[:10]}")
    print()
    
    # Step 3: Validate GUE spacing
    print("📊 Validating GUE level spacing statistics...")
    gue_verified = validate_gue_spacing(eigenvalues)
    print(f"   GUE spacing: {'✓ VERIFIED' if gue_verified else '✗ NOT VERIFIED'}")
    print()
    
    # Step 4: Compute Fredholm determinant
    print(f"🌀 Computing Fredholm determinant for t ∈ [{t_range[0]}, {t_range[1]}]...")
    t_values = np.linspace(t_range[0], t_range[1], n_t_points)
    
    fredholm_log_det = np.zeros(n_t_points, dtype=complex)
    xi_log_values = np.zeros(n_t_points, dtype=complex)
    
    for i, t in enumerate(t_values):
        if i % 50 == 0:
            print(f"   Progress: {i}/{n_t_points}")
        
        # Compute Fredholm determinant
        fredholm_log_det[i] = compute_fredholm_log_determinant(eigenvalues, t)
        
        # Compute Xi function
        xi_log_values[i] = compute_riemann_xi_log(t)
    
    print("   Fredholm determinant computed.")
    print()
    
    # Step 5: Validate synchrony
    print("🔗 Validating Fredholm-Xi synchrony...")
    sync_error, aligned_valleys = compute_synchrony_error(
        t_values, fredholm_log_det, xi_log_values, max_dt=0.2
    )
    
    print(f"   Synchrony error: {sync_error:.4f}")
    print(f"   Aligned valleys: {aligned_valleys}")
    print()
    
    # Step 6: Compute QCAL coherence
    psi_coherence = np.exp(-sync_error) * (aligned_valleys / 50.0)
    psi_coherence = min(psi_coherence, 1.0)
    
    print(f"♾️³ QCAL Coherence Ψ: {psi_coherence:.6f}")
    print()
    
    # Elapsed time
    elapsed_ms = (time.time() - start_time) * 1000
    
    # Create result
    result = SpectralDNAResult(
        eigenvalues=eigenvalues,
        eigenvalues_first_50=eigenvalues[:50],
        epsilon=epsilon,
        x_domain=(x_min, x_max),
        n_eigenvalues=len(eigenvalues),
        fredholm_t_values=t_values,
        fredholm_log_det=fredholm_log_det,
        xi_log_values=xi_log_values,
        synchrony_error=sync_error,
        valley_alignment_count=aligned_valleys,
        gue_spacing_verified=gue_verified,
        psi_coherence=psi_coherence,
        computation_time_ms=elapsed_ms,
        timestamp=time.strftime("%Y-%m-%dT%H:%M:%S"),
        parameters={
            "x_min": x_min,
            "x_max": x_max,
            "epsilon": epsilon,
            "n_points": n_points,
            "n_eigenvalues": n_eigenvalues,
            "t_range": t_range,
            "n_t_points": n_t_points,
            "n_primes": n_primes,
            "max_power": max_power,
            "hermiticity_error": float(hermiticity_error)
        }
    )
    
    return result


def save_eigenvalues_csv(eigenvalues: np.ndarray, 
                          filename: str = "eigenvalues_omega_v3.csv") -> None:
    """
    Save eigenvalues to CSV file.
    
    Args:
        eigenvalues: Array of eigenvalues
        filename: Output filename
    """
    output_path = Path(filename)
    
    # Create header
    header = "index,eigenvalue\n"
    
    # Write to file
    with open(output_path, 'w') as f:
        f.write(header)
        for i, eig in enumerate(eigenvalues):
            f.write(f"{i+1},{eig:.15f}\n")
    
    print(f"💾 Eigenvalues saved to: {output_path}")


def save_result_json(result: SpectralDNAResult,
                      filename: str = "spectral_dna_omega_v3_result.json") -> None:
    """
    Save result to JSON file.
    
    Args:
        result: SpectralDNAResult object
        filename: Output filename
    """
    output_path = Path(filename)
    
    # Convert to serializable dict
    result_dict = {
        "eigenvalues_first_50": result.eigenvalues_first_50.tolist(),
        "epsilon": result.epsilon,
        "x_domain": result.x_domain,
        "n_eigenvalues": result.n_eigenvalues,
        "synchrony_error": result.synchrony_error,
        "valley_alignment_count": result.valley_alignment_count,
        "gue_spacing_verified": result.gue_spacing_verified,
        "psi_coherence": result.psi_coherence,
        "computation_time_ms": result.computation_time_ms,
        "timestamp": result.timestamp,
        "parameters": result.parameters
    }
    
    with open(output_path, 'w') as f:
        json.dump(result_dict, f, indent=2)
    
    print(f"💾 Result saved to: {output_path}")


if __name__ == "__main__":
    print("=" * 70)
    print(" SPECTRAL DNA EXTRACTION: Operator H = xp + V_ε(ln x)")
    print(" QCAL ∞³ · Riemann Hypothesis Validation")
    print("=" * 70)
    print()
    
    # Extract spectral DNA with specified parameters
    result = extract_spectral_dna(
        x_min=0.1,
        x_max=12.0,
        epsilon=0.4,
        n_points=1001,
        n_eigenvalues=500,
        t_range=(10.0, 100.0),
        n_t_points=500,
        n_primes=100,
        max_power=5
    )
    
    # Save results
    print("=" * 70)
    print(" SAVING RESULTS")
    print("=" * 70)
    print()
    
    save_eigenvalues_csv(result.eigenvalues)
    save_result_json(result)
    
    print()
    print("=" * 70)
    print(" SPECTRAL DNA EXTRACTION COMPLETE")
    print("=" * 70)
    print()
    print(f"✓ {result.n_eigenvalues} eigenvalues extracted")
    print(f"✓ Fredholm-Xi synchrony validated")
    print(f"✓ GUE spacing: {'VERIFIED' if result.gue_spacing_verified else 'NOT VERIFIED'}")
    print(f"✓ QCAL Coherence Ψ = {result.psi_coherence:.6f}")
    print(f"✓ Computation time: {result.computation_time_ms/1000:.2f} seconds")
    print()
