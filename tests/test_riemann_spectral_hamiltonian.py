#!/usr/bin/env python3
"""Tests for Riemann Spectral Hamiltonian."""

import numpy as np
from operators.riemann_spectral_hamiltonian import (
    RiemannSpectralHamiltonian,
    compute_hamiltonian_spectrum
)

def test_hamiltonian_construction():
    """Test Hamiltonian matrix construction."""
    gamma_n = np.array([14.134725142, 21.022039639, 25.010857580])
    H_op = RiemannSpectralHamiltonian(gamma_n=gamma_n)
    H = H_op.build_hamiltonian_matrix()
    
    assert H.shape == (3, 3)
    assert np.allclose(np.diag(H), gamma_n)

def test_renormalization():
    """Test eigenvalue renormalization."""
    H_op = RiemannSpectralHamiltonian()
    gamma_renorm = H_op.renormalize_eigenvalues()
    
    # First zero should be ~510 Hz
    assert 500 < gamma_renorm[0] < 520

def test_phase_modulation():
    """Test phase modulation."""
    H_op = RiemannSpectralHamiltonian()
    result = H_op.compute_excited_modes(theta=0.1)
    
    assert result.theta == 0.1
    assert len(result.eigenvalues_modulated) == 5
    assert 0 <= result.coherence <= 1

if __name__ == '__main__':
    test_hamiltonian_construction()
    test_renormalization()
    test_phase_modulation()
    print("✓ All tests passed")
