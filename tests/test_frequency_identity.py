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

mp.mp.dps = 50

f0 = mp.mpf("141.7001")
f_raw = mp.mpf("157.9519")

k = (f0 / f_raw)**2
ω0 = mp.sqrt(k * (2 * mp.pi * f_raw)**2)


def test_frequency_identity():
    """Test that ω₀ = 2π f₀ holds with high precision."""
    lhs = ω0
    rhs = 2 * mp.pi * f0
    assert mp.almosteq(lhs, rhs, rel_eps=1e-40)


def test_frequency_squared():
    """Test that ω₀² = (2π f₀)² holds with high precision."""
    lhs = ω0**2
    rhs = (2 * mp.pi * f0)**2
    assert mp.almosteq(lhs, rhs, rel_eps=1e-40)


def test_frequency_absolute():
    """Test that |ω₀| = 2π f₀ holds (positive root)."""
    lhs = abs(ω0)
    rhs = 2 * mp.pi * f0
    assert mp.almosteq(lhs, rhs, rel_eps=1e-40)
