#!/usr/bin/env python3
"""Tests for Green's Function QCAL."""

import numpy as np
from physics.green_function_qcal import (
    green_function_time_domain,
    green_function_frequency_domain,
    verify_causality
)

def test_causality():
    """Test causality condition G(t<0) = 0."""
    t = np.linspace(-1, 1, 100)
    eigenvals = np.array([1.0, 2.0, 3.0])
    G = green_function_time_domain(t, eigenvals)
    
    assert verify_causality(G, t)

def test_frequency_domain():
    """Test frequency domain Green's function."""
    omega = np.linspace(-10, 10, 50)
    eigenvals = np.array([1.0, 2.0])
    G_omega = green_function_frequency_domain(omega, eigenvals)
    
    assert G_omega.shape == (50, 2)

if __name__ == '__main__':
    test_causality()
    test_frequency_domain()
    print("✓ All tests passed")
