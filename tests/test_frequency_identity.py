#!/usr/bin/env python3
"""
Tests for the Frequency Identity (Script 18).

This module tests the high-precision validation of the frequency identity
relating the universal base frequency f₀ = 141.7001 Hz with the raw geometric
frequency f_raw = 157.9519 Hz through the scaling factor k.

The core identity validated:
    ω₀ = 2π f₀

Where:
    k = (f₀ / f_raw)²
    ω₀ = √(k × (2π × f_raw)²)

Author: José Manuel Mota Burruezo
Date: December 2025
"""

import mpmath as mp

# Precision tolerance for high-precision comparisons
TOLERANCE = 1e-40


def _setup_frequency_values():
    """Set up high-precision frequency values for testing."""
    mp.mp.dps = 50
    f0 = mp.mpf("141.7001")
    f_raw = mp.mpf("157.9519")
    k = (f0 / f_raw)**2
    omega0 = mp.sqrt(k * (2 * mp.pi * f_raw)**2)
    return f0, f_raw, k, omega0


def test_frequency_identity():
    """Test that ω₀ = 2π f₀ holds with high precision."""
    f0, f_raw, k, omega0 = _setup_frequency_values()
    lhs = omega0
    rhs = 2 * mp.pi * f0
    assert mp.almosteq(lhs, rhs, rel_eps=TOLERANCE)


def test_frequency_squared():
    """Test that ω₀² = (2π f₀)² holds with high precision."""
    f0, f_raw, k, omega0 = _setup_frequency_values()
    lhs = omega0**2
    rhs = (2 * mp.pi * f0)**2
    assert mp.almosteq(lhs, rhs, rel_eps=TOLERANCE)


def test_frequency_absolute():
    """Test that |ω₀| = 2π f₀ holds (positive root)."""
    f0, f_raw, k, omega0 = _setup_frequency_values()
    lhs = abs(omega0)
    rhs = 2 * mp.pi * f0
    assert mp.almosteq(lhs, rhs, rel_eps=TOLERANCE)
