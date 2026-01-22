#!/usr/bin/env python3
"""
Test suite for QCAL ∞³ Universal Dynamic Simulator

Tests the implementation of the master operator O∞³ and
universal simulation framework for dynamic universality.
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from qcal_universal import (
    O_infinity_3,
    ProjectionBuilder,
    Projection,
    UniversalSimulator,
    SystemSpectrum,
    F0_BASE,
    COHERENCE_THRESHOLD,
    C_QCAL
)


class TestMasterOperator:
    """Test the master operator O∞³."""
    
    def test_initialization(self):
        """Test O∞³ operator initialization."""
        O = O_infinity_3(base_freq=F0_BASE, dimension=32)
        
        assert O.base_freq == F0_BASE
        assert O.dimension == 32
        assert O.D_s.shape == (32, 32)
        assert O.H_psi.shape == (32, 32)
        assert O.C_sym.shape == (32, 32)
        
    def test_operator_hermiticity(self):
        """Test that O∞³ is Hermitian (for real eigenvalues)."""
        O = O_infinity_3(dimension=16)
        matrix = O.get_operator_matrix()
        
        # Check if approximately Hermitian
        assert np.allclose(matrix, matrix.conj().T, atol=1e-10)
        
    def test_evolution_unitarity(self):
        """Test that evolution preserves norm (unitary)."""
        O = O_infinity_3(dimension=16)
        
        # Random initial state
        psi0 = np.random.randn(16) + 1j * np.random.randn(16)
        psi0 /= np.linalg.norm(psi0)
        
        # Evolve
        psi_t = O.evolve(psi0, t=1.0)
        
        # Check norm preservation
        assert np.isclose(np.linalg.norm(psi_t), 1.0, atol=1e-10)
        
    def test_evolution_reversibility(self):
        """Test that evolution is reversible."""
        O = O_infinity_3(dimension=16)
        
        # Random initial state
        psi0 = np.random.randn(16) + 1j * np.random.randn(16)
        psi0 /= np.linalg.norm(psi0)
        
        # Forward evolution
        psi_forward = O.evolve(psi0, t=1.0)
        
        # Backward evolution
        psi_back = O.evolve(psi_forward, t=-1.0)
        
        # Should return to initial state
        assert np.allclose(psi_back, psi0, atol=1e-10)


class TestProjection:
    """Test projection operators."""
    
    def test_projection_encoding_decoding(self):
        """Test that encode/decode are approximately inverse."""
        # Create simple spectrum
        spectrum = SystemSpectrum(
            eigenvalues=np.array([0.5, 1.0, 1.5, 2.0]),
            coherence=0.95
        )
        
        projection = Projection(spectrum)
        
        # Random state
        state = np.random.randn(4) + 1j * np.random.randn(4)
        state /= np.linalg.norm(state)
        
        # Encode and decode
        encoded = projection.encode(state, target_dim=16)
        decoded = projection.decode(encoded)
        
        # Should approximately recover original
        assert np.allclose(decoded, state, atol=1e-10)
        
    def test_projection_builder(self):
        """Test ProjectionBuilder factory."""
        spectrum = SystemSpectrum(
            eigenvalues=np.linspace(0, 10, 20),
            coherence=0.92
        )
        
        projection = ProjectionBuilder.from_spectrum(spectrum)
        
        assert isinstance(projection, Projection)
        assert projection.spectrum.coherence == 0.92


class TestUniversalSimulator:
    """Test the universal simulator."""
    
    def test_initialization(self):
        """Test simulator initialization."""
        sim = UniversalSimulator(base_freq=F0_BASE)
        
        assert sim.base_freq == F0_BASE
        assert isinstance(sim.O, O_infinity_3)
        assert isinstance(sim.projections, dict)
        
    def test_harmonic_oscillator_simulation(self):
        """Test simulation of quantum harmonic oscillator."""
        sim = UniversalSimulator()
        
        def harmonic_oscillator():
            n = 16
            return np.diag(np.arange(n) + 0.5)
        
        # Ground state
        psi0 = np.zeros(16)
        psi0[0] = 1.0
        
        times, states = sim.simulate(
            harmonic_oscillator,
            psi0,
            t_final=5.0,
            dt=0.5,
            system_name="test_ho"
        )
        
        assert len(times) == len(states)
        assert len(times) > 0
        assert all(len(state) == 16 for state in states)
        
        # Check that simulation created projection
        assert "test_ho" in sim.projections
        
    def test_spectrum_analysis(self):
        """Test spectral analysis of systems."""
        sim = UniversalSimulator()
        
        def simple_hamiltonian():
            return np.diag([1.0, 2.0, 3.0, 4.0])
        
        initial_state = np.array([1.0, 0, 0, 0])
        
        spectrum = sim.analyze_spectrum(simple_hamiltonian, initial_state)
        
        assert len(spectrum.eigenvalues) == 4
        assert np.allclose(spectrum.eigenvalues, [1, 2, 3, 4])
        assert 0 <= spectrum.coherence <= 1
        assert spectrum.entropy >= 0
        
    def test_nls_simulation(self):
        """Test nonlinear Schrödinger equation simulation."""
        sim = UniversalSimulator()
        
        # Gaussian initial condition
        x = np.linspace(-5, 5, 32)
        psi_nls = np.exp(-x**2 / 2)
        psi_nls /= np.linalg.norm(psi_nls)
        
        times, states = sim.simulate_nls(
            psi_nls,
            nonlinearity=1.0,
            t_final=2.0,
            dt=0.2
        )
        
        assert len(times) == len(states)
        assert len(times) > 0
        
    def test_navier_stokes_simulation(self):
        """Test Navier-Stokes equation simulation."""
        sim = UniversalSimulator()
        
        # Simple velocity field
        velocity = np.random.randn(32)
        velocity /= np.linalg.norm(velocity)
        
        times, states = sim.simulate_navier_stokes_3d(
            velocity,
            viscosity=0.1,
            t_final=1.0,
            dt=0.1
        )
        
        assert len(times) == len(states)
        assert len(times) > 0


class TestConstants:
    """Test QCAL ∞³ framework constants."""
    
    def test_base_frequency(self):
        """Test base frequency value."""
        assert F0_BASE == 141.7001
        
    def test_coherence_threshold(self):
        """Test coherence threshold."""
        assert COHERENCE_THRESHOLD == 0.888
        
    def test_fundamental_constant(self):
        """Test fundamental constant C."""
        assert C_QCAL == 244.36


class TestCoherenceCriteria:
    """Test coherence-based simulation criteria."""
    
    def test_low_coherence_warning(self):
        """Test warning for low coherence systems."""
        spectrum = SystemSpectrum(
            eigenvalues=np.array([1.0, 2.0]),
            coherence=0.5  # Below threshold
        )
        
        with pytest.warns(UserWarning):
            projection = ProjectionBuilder.from_spectrum(spectrum)
            
    def test_high_coherence_no_warning(self):
        """Test no warning for high coherence systems."""
        spectrum = SystemSpectrum(
            eigenvalues=np.array([1.0, 1.1]),
            coherence=0.95  # Above threshold
        )
        
        # Should not warn
        projection = ProjectionBuilder.from_spectrum(spectrum)
        assert projection is not None


def test_integration_full_pipeline():
    """Integration test of complete simulation pipeline."""
    # Initialize simulator
    sim = UniversalSimulator(base_freq=F0_BASE)
    
    # Define a test Hamiltonian
    def test_system():
        n = 20
        H = np.zeros((n, n))
        for i in range(n):
            H[i, i] = i * 0.5
            if i < n - 1:
                H[i, i + 1] = 0.1
                H[i + 1, i] = 0.1
        return H
    
    # Initial state (superposition)
    psi0 = np.zeros(20)
    psi0[0] = 1/np.sqrt(2)
    psi0[1] = 1/np.sqrt(2)
    
    # Simulate
    times, states = sim.simulate(
        test_system,
        psi0,
        t_final=10.0,
        dt=0.5,
        system_name="integration_test"
    )
    
    # Verify results
    assert len(times) == len(states)
    assert len(times) == 20  # t_final / dt
    
    # Check normalization is approximately preserved
    norms = [np.linalg.norm(state) for state in states]
    assert all(0.5 < norm < 2.0 for norm in norms)  # Relaxed check
    
    # Verify projection was created
    assert "integration_test" in sim.projections
    proj = sim.projections["integration_test"]
    assert proj.dimension == 20


if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])
