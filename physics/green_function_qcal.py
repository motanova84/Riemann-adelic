#!/usr/bin/env python3
"""
Green's Function QCAL - Causal Propagator with Lorentzian Poles
================================================================

Implements causal Green's function G(t) and frequency domain G̃(ω)
with Lorentzian poles for the QCAL spectral framework.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz
DOI: 10.5281/zenodo.17379721
"""

import numpy as np
from typing import Optional, Tuple
import warnings

try:
    from qcal.constants import F0
except ImportError:
    F0 = 141.7001

def green_function_time_domain(
    t: np.ndarray,
    eigenvals: np.ndarray,
    gamma: float = 1.0,
    D: float = 1.0
) -> np.ndarray:
    """
    Causal Green's function in time domain.
    
    G(t) = θ(t) · ∑ₘ e^(νₘt) |m⟩⟨m|
    
    where νₘ = -iλₘ - γ + Dμₘ
    """
    nu = -1j * eigenvals - gamma - D * np.abs(eigenvals)
    
    # Apply causality: G(t) = 0 for t < 0
    t = np.asarray(t)
    G = np.zeros((len(t), len(eigenvals)), dtype=complex)
    
    for i, ti in enumerate(t):
        if ti >= 0:
            G[i] = np.exp(nu * ti)
    
    return G

def green_function_frequency_domain(
    omega: np.ndarray,
    eigenvals: np.ndarray,
    gamma: float = 1.0,
    D: float = 1.0
) -> np.ndarray:
    """
    Green's function in frequency domain (Lorentzian poles).
    
    G̃ₘ(ω) = 1 / (γ - Dμₘ + i(ω + λₘ))
    """
    omega = np.asarray(omega)
    mu = -np.abs(eigenvals)
    
    G_omega = np.zeros((len(omega), len(eigenvals)), dtype=complex)
    
    for m, lam in enumerate(eigenvals):
        denominator = gamma - D * mu[m] + 1j * (omega + lam)
        G_omega[:, m] = 1.0 / denominator
    
    return G_omega

def verify_causality(G: np.ndarray, t: np.ndarray) -> bool:
    """Verify G(t<0) = 0."""
    t = np.asarray(t)
    G = np.asarray(G)
    negative_times = t < 0
    if np.any(negative_times):
        return np.allclose(G[negative_times], 0.0)
    return True

if __name__ == '__main__':
    print("Green's Function QCAL - Quick Test")
    t = np.linspace(-1, 1, 100)
    eigenvals = np.array([1.0, 2.0, 3.0])
    G = green_function_time_domain(t, eigenvals)
    is_causal = verify_causality(G, t)
    print(f"✓ Causality verified: {is_causal}")
