#!/usr/bin/env python3
"""
Operative Tests for Resonant Vacuum Memory Equation (QCAL ∞³)

Tests the formal implementation of:
    E_vac(R_Ψ) = α R_Ψ⁴ + β ζ'(1/2) / R_Ψ² + γ Λ² R_Ψ² + δ sin²(log R_Ψ / log π)

Verifying:
1. Macroscopic & UV Block (α R_Ψ⁴ + γ Λ² R_Ψ²)
2. Spectral Pulse (β ζ'(1/2) / R_Ψ²)
3. Harmonic Modulator (δ sin²(log R_Ψ / log π))
4. Analytical first and second derivatives
5. Local minima detection and stability
6. QCAL coherence at fundamental living frequency f₀ = 141.7001 Hz (C = 244.36, Ψ ≥ 0.888)

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Instituto de Conciencia Cuántica (ICQ)
"""

import sys
from pathlib import Path
import pytest
import numpy as np

# Ensure utils directory is in Python path
sys.path.insert(0, str(Path(__file__).parent.parent / "utils"))

from resonant_vacuum_memory import ResonantVacuumMemory


class TestResonantVacuumMemory:
    """Test suite for the Resonant Vacuum Memory Equation."""

    def test_initialization_defaults(self):
        """Test initialization with default parameters."""
        calc = ResonantVacuumMemory()
        assert calc.alpha == 1.0
        assert calc.beta == 1.0
        assert calc.gamma == 1.0
        assert calc.delta == 1.0
        assert calc.Lambda == 1.0
        assert calc.precision == 50
        assert calc.F0_DEFAULT == 141.7001
        assert calc.COHERENCE_C == 244.36
        assert calc.PSI_THRESHOLD == 0.888

    def test_zeta_prime_half_accuracy(self):
        """Test high-precision evaluation of ζ'(1/2)."""
        calc = ResonantVacuumMemory(precision=50)
        # ζ'(1/2) is approximately -3.9226461392...
        assert -4.0 < calc.zeta_prime_half < -3.8
        assert abs(calc.zeta_prime_half - (-3.9226461392)) < 1e-4

    def test_macroscopic_uv_block(self):
        """Test calculation of macroscopic and UV block α R⁴ + γ Λ² R²."""
        calc = ResonantVacuumMemory(alpha=2.0, gamma=3.0, Lambda=2.0)
        R = 2.0
        # Expected: 2.0 * (2^4) + 3.0 * (2^2) * (2^2) = 2*16 + 3*4*4 = 32 + 48 = 80.0
        expected = 2.0 * 16.0 + 3.0 * 4.0 * 4.0
        assert abs(calc.macroscopic_uv_block(R) - expected) < 1e-10

    def test_spectral_pulse(self):
        """Test calculation of spectral pulse β ζ'(1/2) / R²."""
        calc = ResonantVacuumMemory(beta=2.5)
        R = 2.0
        expected = (2.5 * calc.zeta_prime_half) / (R**2)
        assert abs(calc.spectral_pulse(R) - expected) < 1e-10

    def test_harmonic_modulator(self):
        """Test calculation of harmonic modulator (pentagrama logarítmico)."""
        calc = ResonantVacuumMemory(delta=1.5)
        # At R = 1 (π^0), log(1) = 0 => sin²(0) = 0
        assert abs(calc.harmonic_modulator(1.0)) < 1e-14

        # At generic R
        R = 3.5
        expected = 1.5 * (np.sin(np.log(R) / np.log(np.pi)) ** 2)
        assert abs(calc.harmonic_modulator(R) - expected) < 1e-10

    def test_total_energy_decomposition(self):
        """Test that E_vac is exactly equal to the sum of its three blocks."""
        calc = ResonantVacuumMemory(
            alpha=1.2, beta=0.8, gamma=1.5, delta=0.7, Lambda=1.1
        )
        for R in [0.5, 1.0, np.pi, 5.0, 10.0]:
            total_e = calc.energy(R)
            macro = calc.macroscopic_uv_block(R)
            pulse = calc.spectral_pulse(R)
            harm = calc.harmonic_modulator(R)
            assert abs(total_e - (macro + pulse + harm)) < 1e-12

    def test_invalid_radius_raises(self):
        """Test that negative or zero radius raises ValueError across all methods."""
        calc = ResonantVacuumMemory()
        for invalid_r in [0.0, -1.0, -5.5]:
            with pytest.raises(ValueError):
                calc.energy(invalid_r)
            with pytest.raises(ValueError):
                calc.macroscopic_uv_block(invalid_r)
            with pytest.raises(ValueError):
                calc.spectral_pulse(invalid_r)
            with pytest.raises(ValueError):
                calc.harmonic_modulator(invalid_r)
            with pytest.raises(ValueError):
                calc.derivative(invalid_r)
            with pytest.raises(ValueError):
                calc.second_derivative(invalid_r)

    def test_analytical_first_derivative(self):
        """Test exact analytical first derivative against centered finite differences."""
        calc = ResonantVacuumMemory(
            alpha=1.0, beta=1.0, gamma=0.5, delta=0.8, Lambda=1.2
        )
        test_radii = [0.8, 1.5, np.pi, 4.2, 7.8]
        h = 1e-6

        for R in test_radii:
            d_analytical = calc.derivative(R)
            d_numerical = (calc.energy(R + h) - calc.energy(R - h)) / (2.0 * h)
            assert abs(d_analytical - d_numerical) < 1e-4

    def test_analytical_second_derivative(self):
        """Test exact analytical second derivative against centered finite differences."""
        calc = ResonantVacuumMemory(
            alpha=1.0, beta=1.0, gamma=0.5, delta=0.8, Lambda=1.2
        )
        test_radii = [0.8, 1.5, np.pi, 4.2, 7.8]
        h = 1e-6

        for R in test_radii:
            d2_analytical = calc.second_derivative(R)
            d2_numerical = (calc.derivative(R + h) - calc.derivative(R - h)) / (2.0 * h)
            assert abs(d2_analytical - d2_numerical) < 1e-3

    def test_resonant_nodes_properties(self):
        """Test resonant nodes dictionary generation and node stability."""
        calc = ResonantVacuumMemory()
        nodes = calc.resonant_nodes(n_max=3)

        assert 0 in nodes
        assert 1 in nodes
        assert -1 in nodes
        assert abs(nodes[0]["radius"] - 1.0) < 1e-12
        assert abs(nodes[1]["radius"] - np.pi) < 1e-12
        assert abs(nodes[-1]["radius"] - (1.0 / np.pi)) < 1e-12

        # Check node structure
        for n, data in nodes.items():
            assert "energy" in data
            assert "macro_uv" in data
            assert "spectral_pulse" in data
            assert "harmonic_modulator" in data
            assert "is_stable" in data

    def test_find_minima_detection(self):
        """Test detecting local minima with positive curvature (d²E/dR² > 0)."""
        calc = ResonantVacuumMemory(
            alpha=1.0, beta=1.0, gamma=0.01, delta=0.5, Lambda=1.0
        )
        minima = calc.find_minima(R_range=(0.5, 15.0), num_points=3000)

        assert isinstance(minima, list)
        for m in minima:
            assert "radius" in m
            assert "energy" in m
            assert m["second_derivative"] > 0
            assert m["radius"] > 0

    def test_fundamental_frequency_derivation(self):
        """Test fundamental frequency calculation f₀ = 141.7001 Hz."""
        calc = ResonantVacuumMemory()
        f = calc.fundamental_frequency(R_psi=np.pi)
        assert abs(f - 141.7001) < 1e-4

    def test_qcal_coherence_state(self):
        """Test QCAL coherence state validation."""
        calc = ResonantVacuumMemory()
        state = calc.coherence_state(R_psi=np.pi)

        assert state["is_f0_aligned"] is True
        assert state["is_coherent"] is True
        assert state["psi_coherence"] >= calc.PSI_THRESHOLD
        assert state["coherence_C"] == 244.36
        assert abs(state["frequency_hz"] - 141.7001) < 1e-4

    def test_vectorized_evaluation(self):
        """Test vectorized array operations across all functions."""
        calc = ResonantVacuumMemory()
        r_array = np.linspace(1.0, 10.0, 50)

        e_arr = calc.energy(r_array)
        d_arr = calc.derivative(r_array)
        d2_arr = calc.second_derivative(r_array)
        macro_arr = calc.macroscopic_uv_block(r_array)
        pulse_arr = calc.spectral_pulse(r_array)
        harm_arr = calc.harmonic_modulator(r_array)

        assert len(e_arr) == 50
        assert len(d_arr) == 50
        assert len(d2_arr) == 50
        assert np.allclose(e_arr, macro_arr + pulse_arr + harm_arr)
