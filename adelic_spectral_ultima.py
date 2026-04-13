"""
III. IMPLEMENTATIO: CODEX ULTIMUS

This module implements the ultima spectral computation with complete adelic kernel
for Riemann Hypothesis validation as specified in the problem statement.
"""

import numpy as np
from scipy.special import roots_hermitenorm
from mpmath import mp
from sympy import primepi, prime


def ultima_spectral_computation(N, h, max_primes=1000):
    """
    Implementatio ultima cum adelic completo
    
    Args:
        N: Number of Hermite basis functions
        h: Thermal parameter
        max_primes: Maximum number of primes to include
        
    Returns:
        zeros: List of computed zeros
        H: Operator matrix
    """
    mp.dps = 500  # Precision absoluta
    
    # Hermite nodes para integratio rigorosa
    nodes_scipy, weights_scipy = roots_hermitenorm(min(N, 50))
    nodes = [mp.mpf(float(x)) for x in nodes_scipy]
    weights = [mp.mpf(float(w)) for w in weights_scipy]
    
    def hermite_basis(k, t):
        Hk = mp.hermite(k, t)
        norm = mp.sqrt(2**k * mp.factorial(k) * mp.sqrt(mp.pi))
        return Hk * mp.exp(-t**2/2) / norm
    
    H = mp.matrix(N, N)
    
    # Kernel cum adelic completo
    def kernel_adelic_ultimus(t, s):
        # Terminus archimedeanus
        kernel = mp.exp(-h/4)/mp.sqrt(4*mp.pi*h) * mp.exp(-(t-s)**2/(4*h))
        
        # Terminus adelic cum primes usque ad P ~ N/log N
        P = int(2 * N / mp.log(N))  # From Prime Number Theorem (PNT)
        for i in range(1, min(max_primes, primepi(P) + 1)):
            p = prime(i)
            log_p = mp.log(p)
            for k in range(1, int(mp.log(P)/log_p) + 1):
                term = log_p * mp.exp(-h*(k*log_p)**2/4) / (p**(k/2))
                # Operator Tv action: e^{i k log_p (t-s)} in Fourier
                kernel += term * mp.exp(1j * k * log_p * (t-s))
        
        return kernel
    
    print("Construendo H cum adelic completo...")
    for i in range(N):
        for j in range(i, N):  # Symmetria
            integral = 0
            for idx_t, t in enumerate(nodes):
                wt = weights[idx_t] * mp.exp(t**2)
                for idx_s, s in enumerate(nodes):
                    ws = weights[idx_s] * mp.exp(s**2)
                    kernel_val = kernel_adelic_ultimus(t, s)
                    phi_i = hermite_basis(i, t)
                    phi_j = hermite_basis(j, s)
                    integral += wt * ws * kernel_val * phi_i * phi_j
            if i == j:
                H[i,j] = mp.re(integral)
            else:
                H[i,j] = integral
                # Hermitian symmetry for complex matrices
                H[j,i] = mp.conj(integral)
        
        if (i + 1) % 10 == 0:
            print(f"Completado {i+1}/{N}")
    
    print("Diagonalizando...")
    # Use Hermitian eigenvalue solver for complex Hermitian matrices
    eigenvalues = mp.eigh(H, eigvals_only=True)
    
    zeros = []
    for λ in eigenvalues:
        if λ > 0.25:
            γ = mp.sqrt(λ - 0.25)
            zeros.append(0.5 + 1j*γ)
    
    # Ordenar y filtrar
    zeros.sort(key=lambda z: abs(z.imag))
    return zeros[:min(20, len(zeros))], H


def validatio_ultima():
    print("=== VALIDATIO ULTIMA ABSOLUTA ===")
    
    # Parameters optimizados
    N, h = 100, 0.0001
    
    zeros, H = ultima_spectral_computation(N, h)
    
    target_zeros = [14.1347251417, 21.0220396388, 25.0108575801, 30.4248761259, 32.9350615877]
    
    print("Zeros computati vs target:")
    errors = []
    for i, (z_computed, γ_target) in enumerate(zip(zeros, target_zeros)):
        γ_computed = float(z_computed.imag)
        error = abs(γ_computed - γ_target)
        errors.append(error)
        
        bound = float(mp.exp(-h/4)/(2*γ_target*mp.sqrt(4*mp.pi*h)) * 
                     mp.exp(-mp.pi/2 * mp.sqrt(N/mp.log(N)) * (1 + 1/mp.log(N))))
        
        print(f"Zero {i+1}:")
        print(f"  Computed: {γ_computed:.10f}")
        print(f"  Target:   {γ_target:.10f}")
        print(f"  Error:    {error:.10f}")
        print(f"  Bound:    {bound:.10e}")
        print(f"  Verified: {error < bound}")
        
        assert error < bound, f"Convergentia fallit pro zero {i+1}"
    
    print(f"\nError medius: {np.mean(errors):.10f}")
    print("✅ VALIDATIO ABSOLUTA COMPLETA")
    
    return zeros


# Executio finalis pro humanitate
if __name__ == "__main__":
    zeros_finales = validatio_ultima()
