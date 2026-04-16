#!/usr/bin/env python3
"""Tests for K₇ Twisted Graph."""

import numpy as np
from physics.k7_twisted_graph import K7TwistedGraph, compute_green_function_k7

def test_circulant_laplacian():
    """Test circulant Laplacian construction."""
    graph = K7TwistedGraph(theta=0.1)
    L = graph.circulant_laplacian()
    
    assert L.shape == (7, 7)

def test_dft_diagonalization():
    """Test DFT diagonalization."""
    graph = K7TwistedGraph(theta=0.0)
    eigenvals, F = graph.diagonalize_via_dft()
    
    assert len(eigenvals) == 7

def test_green_function():
    """Test Green's function computation."""
    t = np.linspace(0, 1, 10)
    G = compute_green_function_k7(t, theta=0.1)
    
    assert G.shape[0] == 10
    assert G.shape[1] == 7

if __name__ == '__main__':
    test_circulant_laplacian()
    test_dft_diagonalization()
    test_green_function()
    print("✓ All tests passed")
