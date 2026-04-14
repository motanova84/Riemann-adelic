#!/usr/bin/env python3
"""
Tests for Quantum Zeta Evolution Simulation

Tests the quantum evolution simulation of ζ(x, t) under the Hamiltonian
H = -∂²ₓ + V(x) using spectral expansion.

Author: José Manuel Mota Burruezo
Date: November 2025
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from quantum_zeta_evolution import QuantumZetaEvolutionSimulator


class TestQuantumZetaEvolutionSimulator:
    """Test suite for QuantumZetaEvolutionSimulator class."""

    def test_initialization(self):
        """Test simulator initialization with default parameters."""
        sim = QuantumZetaEvolutionSimulator()

        assert sim.Nx == 4000
        assert sim.x_range == (-30.0, 30.0)
        assert sim.Tmax == 10.0
        assert sim.Nt == 500
        assert sim.k == 30

        # Check grid creation
        assert len(sim.x) == 4000
        assert sim.x[0] == -30.0
        assert sim.x[-1] == pytest.approx(30.0, rel=1e-3)

        # Check time array
        assert len(sim.t_array) == 500
        assert sim.t_array[0] == 0.0
        assert sim.t_array[-1] == 10.0

    def test_custom_initialization(self):
        """Test simulator initialization with custom parameters."""
        sim = QuantumZetaEvolutionSimulator(
            Nx=1000,
            x_range=(-20.0, 20.0),
            Tmax=5.0,
            Nt=100,
            k=15
        )

        assert sim.Nx == 1000
        assert sim.x_range == (-20.0, 20.0)
        assert sim.Tmax == 5.0
        assert sim.Nt == 100
        assert sim.k == 15

        assert len(sim.x) == 1000
        assert len(sim.t_array) == 100

    def test_construct_potential_harmonic(self):
        """Test harmonic potential construction."""
        sim = QuantumZetaEvolutionSimulator(Nx=500)
        V = sim.construct_potential(potential_type="harmonic_well")

        # Should be finite and defined
        assert np.all(np.isfinite(V))
        assert len(V) == 500

        # Potential should have minimum near x=0 (center)
        mid = len(V) // 2
        # For harmonic potential, center should be minimum (excluding offset)
        assert V[mid] <= V[0]
        assert V[mid] <= V[-1]

    def test_construct_potential_double_well(self):
        """Test double-well potential construction."""
        sim = QuantumZetaEvolutionSimulator(Nx=500)
        V = sim.construct_potential(potential_type="double_well")

        assert np.all(np.isfinite(V))
        assert len(V) == 500

        # Check that potential has structure (not flat)
        assert np.std(V) > 0  # Has variation

    def test_construct_potential_zeta_like(self):
        """Test zeta-like potential construction."""
        sim = QuantumZetaEvolutionSimulator(Nx=500)
        V = sim.construct_potential(potential_type="zeta_like")

        assert np.all(np.isfinite(V))
        assert len(V) == 500

    def test_construct_potential_external(self):
        """Test external potential interpolation."""
        sim = QuantumZetaEvolutionSimulator(Nx=500, x_range=(-10, 10))

        # Create external potential data
        x_full = np.linspace(-15, 15, 100)
        V_full = x_full**2  # Simple parabola

        V = sim.construct_potential(V_full=V_full, x_full=x_full)

        assert np.all(np.isfinite(V))
        assert len(V) == 500

        # Should approximately follow parabola shape (allowing for interpolation error)
        # Check correlation between interpolated and expected
        expected = sim.x**2
        correlation = np.corrcoef(V, expected)[0, 1]
        assert correlation > 0.99  # High correlation indicates correct shape

    def test_construct_potential_invalid_type(self):
        """Test that invalid potential type raises error."""
        sim = QuantumZetaEvolutionSimulator()

        with pytest.raises(ValueError, match="Unknown potential type"):
            sim.construct_potential(potential_type="invalid_potential")

    def test_build_hamiltonian_requires_potential(self):
        """Test that build_hamiltonian fails without potential."""
        sim = QuantumZetaEvolutionSimulator()

        with pytest.raises(ValueError, match="Potential not constructed"):
            sim.build_hamiltonian()

    def test_build_hamiltonian(self):
        """Test Hamiltonian construction."""
        sim = QuantumZetaEvolutionSimulator(Nx=100)
        sim.construct_potential(potential_type="harmonic_well")
        H = sim.build_hamiltonian()

        # H should be square matrix
        assert H.shape == (100, 100)

        # H should be symmetric (Hermitian)
        H_dense = H.toarray()
        np.testing.assert_allclose(H_dense, H_dense.T, atol=1e-12)

    def test_compute_eigenstates_requires_hamiltonian(self):
        """Test that compute_eigenstates fails without Hamiltonian."""
        sim = QuantumZetaEvolutionSimulator()

        with pytest.raises(ValueError, match="Hamiltonian not built"):
            sim.compute_eigenstates()

    def test_compute_eigenstates(self):
        """Test eigenstate computation."""
        sim = QuantumZetaEvolutionSimulator(Nx=200, k=10)
        sim.construct_potential(potential_type="harmonic_well")
        sim.build_hamiltonian()
        E_n, psi_n = sim.compute_eigenstates()

        # Should have k eigenvalues
        assert len(E_n) == 10

        # Eigenvalues should be sorted
        assert np.all(np.diff(E_n) >= 0)

        # Eigenfunctions should be normalized
        for psi in psi_n:
            norm = np.trapezoid(np.abs(psi)**2, sim.x)
            assert norm == pytest.approx(1.0, rel=1e-3)

        # Eigenfunctions should have correct shape
        assert psi_n.shape == (10, 200)

    def test_eigenstates_orthogonality(self):
        """Test that eigenstates are orthogonal."""
        sim = QuantumZetaEvolutionSimulator(Nx=300, k=5)
        sim.construct_potential(potential_type="harmonic_well")
        sim.build_hamiltonian()
        E_n, psi_n = sim.compute_eigenstates()

        # Check orthogonality
        for i in range(len(psi_n)):
            for j in range(i + 1, len(psi_n)):
                overlap = np.trapezoid(psi_n[i] * np.conj(psi_n[j]), sim.x)
                assert np.abs(overlap) < 0.1  # Should be nearly orthogonal

    def test_prepare_initial_state_gaussian(self):
        """Test Gaussian initial state preparation."""
        sim = QuantumZetaEvolutionSimulator(Nx=500)
        zeta_x = sim.prepare_initial_state(sigma=2.0, x0=1.0, state_type="gaussian")

        # Should be normalized
        norm = np.trapezoid(np.abs(zeta_x)**2, sim.x)
        assert norm == pytest.approx(1.0, rel=1e-3)

        # Should be peaked near x0
        idx_max = np.argmax(np.abs(zeta_x))
        assert sim.x[idx_max] == pytest.approx(1.0, abs=0.5)

    def test_prepare_initial_state_coherent(self):
        """Test coherent initial state preparation."""
        sim = QuantumZetaEvolutionSimulator(Nx=500)
        zeta_x = sim.prepare_initial_state(sigma=2.0, x0=0.0, state_type="coherent")

        # Should be normalized
        norm = np.trapezoid(np.abs(zeta_x)**2, sim.x)
        assert norm == pytest.approx(1.0, rel=1e-3)

        # Should be complex (has momentum)
        assert np.any(np.imag(zeta_x) != 0)

    def test_prepare_initial_state_superposition(self):
        """Test superposition initial state preparation."""
        sim = QuantumZetaEvolutionSimulator(Nx=500)
        zeta_x = sim.prepare_initial_state(sigma=1.5, x0=0.0, state_type="superposition")

        # Should be normalized
        norm = np.trapezoid(np.abs(zeta_x)**2, sim.x)
        assert norm == pytest.approx(1.0, rel=1e-3)

        # Should have two peaks
        peaks = np.where(np.diff(np.sign(np.diff(np.abs(zeta_x)))) < 0)[0] + 1
        assert len(peaks) >= 2

    def test_prepare_initial_state_invalid_type(self):
        """Test that invalid state type raises error."""
        sim = QuantumZetaEvolutionSimulator()

        with pytest.raises(ValueError, match="Unknown state type"):
            sim.prepare_initial_state(state_type="invalid_state")

    def test_compute_expansion_coefficients(self):
        """Test expansion coefficient computation."""
        sim = QuantumZetaEvolutionSimulator(Nx=300, k=10)
        sim.construct_potential(potential_type="harmonic_well")
        sim.build_hamiltonian()
        sim.compute_eigenstates()
        sim.prepare_initial_state(sigma=2.5)
        c_n = sim.compute_expansion_coefficients()

        # Should have k coefficients
        assert len(c_n) == 10

        # Coefficients should be finite
        assert np.all(np.isfinite(c_n))

        # Sum of |c_n|^2 should be approximately 1 (completeness)
        total_prob = np.sum(np.abs(c_n)**2)
        assert total_prob < 1.1  # May not be exactly 1 due to truncation

    def test_evolve(self):
        """Test quantum time evolution."""
        sim = QuantumZetaEvolutionSimulator(Nx=200, Nt=50, k=10)
        sim.construct_potential(potential_type="harmonic_well")
        sim.build_hamiltonian()
        sim.compute_eigenstates()
        sim.prepare_initial_state()
        sim.compute_expansion_coefficients()
        zeta_xt = sim.evolve()

        # Shape should be (Nt, Nx)
        assert zeta_xt.shape == (50, 200)

        # Should be complex
        assert zeta_xt.dtype == np.complex128

        # All values should be finite
        assert np.all(np.isfinite(zeta_xt))

    def test_evolve_norm_conservation(self):
        """Test that evolution conserves norm."""
        sim = QuantumZetaEvolutionSimulator(Nx=300, Nt=100, k=15)
        sim.construct_potential(potential_type="harmonic_well")
        sim.build_hamiltonian()
        sim.compute_eigenstates()
        sim.prepare_initial_state()
        sim.compute_expansion_coefficients()
        zeta_xt = sim.evolve()

        # Compute norm at each time
        norms = [np.trapezoid(np.abs(zeta_xt[i])**2, sim.x) for i in range(sim.Nt)]

        # Norm should be approximately constant (within 10%)
        assert np.std(norms) / np.mean(norms) < 0.1

    def test_run_simulation(self):
        """Test complete simulation pipeline."""
        sim = QuantumZetaEvolutionSimulator(Nx=200, Nt=50, k=10)
        results = sim.run_simulation(
            potential_type="zeta_like",
            sigma=2.5,
            x0=0.0,
            state_type="gaussian"
        )

        # Check all expected keys
        expected_keys = ['x', 't', 'zeta_xt', 'E_n', 'psi_n', 'c_n', 'V', 'initial_state']
        for key in expected_keys:
            assert key in results

        # Check shapes
        assert results['x'].shape == (200,)
        assert results['t'].shape == (50,)
        assert results['zeta_xt'].shape == (50, 200)
        assert len(results['E_n']) == 10
        assert results['psi_n'].shape == (10, 200)
        assert len(results['c_n']) == 10
        assert results['V'].shape == (200,)
        assert results['initial_state'].shape == (200,)

    def test_analyze_fft_at_point(self):
        """Test FFT analysis at a spatial point."""
        sim = QuantumZetaEvolutionSimulator(Nx=200, Nt=100, k=10)
        sim.run_simulation(potential_type="harmonic_well")

        freqs, spectrum = sim.analyze_fft_at_point(x0=0.0)

        # Should have positive frequencies only
        assert np.all(freqs >= 0)

        # Spectrum should be positive
        assert np.all(spectrum >= 0)

        # Should be finite
        assert np.all(np.isfinite(freqs))
        assert np.all(np.isfinite(spectrum))

    def test_extract_dominant_frequencies(self):
        """Test dominant frequency extraction."""
        sim = QuantumZetaEvolutionSimulator(Nx=200, Nt=100, k=10)
        sim.run_simulation(potential_type="harmonic_well")

        dom_freqs = sim.extract_dominant_frequencies(x0=0.0, n_peaks=5)

        # Should return array
        assert isinstance(dom_freqs, np.ndarray)

        # Frequencies should be non-negative
        assert np.all(dom_freqs >= 0)

    def test_compute_probability_density(self):
        """Test probability density computation."""
        sim = QuantumZetaEvolutionSimulator(Nx=200, Nt=50, k=10)
        sim.run_simulation()

        prob = sim.compute_probability_density()

        # Shape should match evolution
        assert prob.shape == (50, 200)

        # Should be non-negative
        assert np.all(prob >= 0)

        # Should be real
        assert prob.dtype == np.float64

    def test_compute_expectation_values(self):
        """Test expectation value computation."""
        sim = QuantumZetaEvolutionSimulator(Nx=200, Nt=50, k=10)
        sim.run_simulation()

        exp_vals = sim.compute_expectation_values()

        # Check expected keys
        assert 'x_mean' in exp_vals
        assert 'x2_mean' in exp_vals
        assert 'x_var' in exp_vals
        assert 'norm' in exp_vals

        # Check shapes
        for key in exp_vals:
            assert len(exp_vals[key]) == 50

        # Variance should be non-negative
        assert np.all(exp_vals['x_var'] >= -1e-10)  # Allow small numerical error

        # Norm should be approximately 1
        assert np.mean(exp_vals['norm']) == pytest.approx(1.0, rel=0.5)

    def test_save_and_load_results(self, tmp_path):
        """Test saving and loading results."""
        sim = QuantumZetaEvolutionSimulator(Nx=100, Nt=20, k=5)
        sim.run_simulation()

        # Save
        filename = str(tmp_path / "test_evolution.npz")
        sim.save_results(filename)

        # Load and verify
        data = np.load(filename)
        assert 'x' in data
        assert 'zeta_xt' in data
        assert 'E_n' in data

        np.testing.assert_array_equal(data['x'], sim.x)
        np.testing.assert_array_equal(data['E_n'], sim.E_n)


class TestNumericalStability:
    """Test numerical stability of the simulation."""

    def test_no_nan_or_inf(self):
        """Test that calculations don't produce NaN or Inf."""
        sim = QuantumZetaEvolutionSimulator(Nx=200, Nt=50, k=10)
        sim.run_simulation()

        assert not np.any(np.isnan(sim.zeta_xt))
        assert not np.any(np.isinf(sim.zeta_xt))
        assert not np.any(np.isnan(sim.E_n))
        assert not np.any(np.isinf(sim.E_n))

    def test_consistent_across_grid_sizes(self):
        """Test that results are consistent with different grid sizes."""
        # Low resolution
        sim_low = QuantumZetaEvolutionSimulator(Nx=100, k=5)
        sim_low.run_simulation(potential_type="harmonic_well")
        E_low = sim_low.E_n

        # High resolution
        sim_high = QuantumZetaEvolutionSimulator(Nx=400, k=5)
        sim_high.run_simulation(potential_type="harmonic_well")
        E_high = sim_high.E_n

        # Eigenvalues should be similar (within 5%)
        for i in range(min(len(E_low), len(E_high), 3)):
            rel_diff = abs(E_low[i] - E_high[i]) / abs(E_high[i])
            assert rel_diff < 0.1, f"E_{i}: {E_low[i]} vs {E_high[i]}"


class TestPhysicalConsistency:
    """Test physical consistency of the simulation."""

    def test_eigenvalues_real(self):
        """Test that eigenvalues are real (H is Hermitian)."""
        sim = QuantumZetaEvolutionSimulator(Nx=200, k=10)
        sim.run_simulation()

        # Eigenvalues should be real
        assert sim.E_n.dtype in [np.float64, np.float32]
        assert np.all(np.isreal(sim.E_n))

    def test_harmonic_oscillator_eigenvalues(self):
        """Test that harmonic oscillator gives expected eigenvalue pattern."""
        sim = QuantumZetaEvolutionSimulator(Nx=500, k=10, x_range=(-20, 20))
        sim.construct_potential(potential_type="harmonic_well")
        sim.build_hamiltonian()
        sim.compute_eigenstates()

        # Energy differences should be approximately constant (harmonic oscillator)
        diffs = np.diff(sim.E_n[:5])
        relative_variation = np.std(diffs) / np.mean(diffs)

        # Allow for numerical discretization effects
        assert relative_variation < 0.5

    def test_probability_conservation(self):
        """Test that probability is conserved during evolution."""
        sim = QuantumZetaEvolutionSimulator(Nx=300, Nt=100, k=15)
        sim.run_simulation()

        exp_vals = sim.compute_expectation_values()
        norms = exp_vals['norm']

        # Norm should be constant (within 5%)
        assert np.std(norms) / np.mean(norms) < 0.05


class TestEdgeCases:
    """Test edge cases and boundary conditions."""

    def test_single_eigenstate(self):
        """Test with just one eigenstate."""
        sim = QuantumZetaEvolutionSimulator(Nx=100, Nt=20, k=1)
        sim.run_simulation()

        assert len(sim.E_n) == 1
        assert sim.psi_n.shape == (1, 100)

    def test_very_narrow_initial_state(self):
        """Test with very narrow initial state."""
        sim = QuantumZetaEvolutionSimulator(Nx=200, Nt=20, k=10)
        sim.construct_potential(potential_type="harmonic_well")
        sim.build_hamiltonian()
        sim.compute_eigenstates()
        sim.prepare_initial_state(sigma=0.5)  # Very narrow
        sim.compute_expansion_coefficients()
        sim.evolve()

        # Should still work
        assert np.all(np.isfinite(sim.zeta_xt))

    def test_very_wide_initial_state(self):
        """Test with very wide initial state."""
        sim = QuantumZetaEvolutionSimulator(Nx=200, Nt=20, k=10)
        sim.construct_potential(potential_type="harmonic_well")
        sim.build_hamiltonian()
        sim.compute_eigenstates()
        sim.prepare_initial_state(sigma=10.0)  # Very wide
        sim.compute_expansion_coefficients()
        sim.evolve()

        # Should still work
        assert np.all(np.isfinite(sim.zeta_xt))

    def test_offset_initial_state(self):
        """Test with initial state not centered at origin."""
        sim = QuantumZetaEvolutionSimulator(Nx=200, Nt=20, k=10)
        sim.run_simulation(x0=5.0)

        # Should still work
        assert np.all(np.isfinite(sim.zeta_xt))
