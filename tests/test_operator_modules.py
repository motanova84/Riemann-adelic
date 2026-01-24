#!/usr/bin/env python3
"""
Tests for Vibrational Operator Modules
=======================================

Tests H_Ψ, H_Ψg, and observational horizon implementations.
"""

import pytest
import numpy as np
import sys
import os

# Add paths
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from operators.vibrational_hpsi import VibrationalOperatorHpsi, F0, C_COHERENCE
from operators.curved_spacetime_hpsi import (
    CurvedSpacetimeHpsi, ConsciousnessField, ALPHA_PSI
)
from operators.observational_horizon import (
    ObservationalHorizon, ObserverState
)


class TestVibrationalOperatorHpsi:
    """Test suite for H_Ψ operator."""
    
    def test_initialization(self):
        """Test operator initialization."""
        op = VibrationalOperatorHpsi(
            n_points=100,
            x_range=(0.1, 20.0),
            n_primes=30
        )
        
        assert op.n_points == 100
        assert len(op.x) == 100
        assert len(op.primes) == 30
        assert op.lambda_freq == F0
    
    def test_noetic_potential(self):
        """Test noetic potential computation."""
        op = VibrationalOperatorHpsi(n_points=50, n_primes=10)
        
        x = np.array([1.0, 5.0, 10.0])
        V = op.noetic_potential(x)
        
        assert len(V) == len(x)
        assert np.all(np.isfinite(V))
        # Potential should have oscillatory structure
        assert np.std(V) > 0
    
    def test_operator_hermiticity(self):
        """Test that operator is Hermitian."""
        op = VibrationalOperatorHpsi(n_points=50, n_primes=10)
        H = op.construct_operator()
        
        # Check Hermiticity: H = H†
        assert np.allclose(H, H.conj().T, atol=1e-10)
    
    def test_spectrum_computation(self):
        """Test spectrum computation."""
        op = VibrationalOperatorHpsi(n_points=100, n_primes=20)
        eigenvalues, eigenfunctions = op.compute_spectrum(n_eigenvalues=10)
        
        assert len(eigenvalues) == 10
        assert eigenfunctions.shape == (100, 10)
        
        # Eigenvalues should be real (operator is Hermitian)
        assert np.all(np.isreal(eigenvalues))
        
        # Eigenvalues should be sorted
        assert np.all(np.diff(eigenvalues) >= 0)
    
    def test_eigenfunction_normalization(self):
        """Test that eigenfunctions are normalized."""
        op = VibrationalOperatorHpsi(n_points=100, n_primes=10)
        eigenvalues, eigenfunctions = op.compute_spectrum(n_eigenvalues=5)
        
        from scipy.integrate import trapezoid
        for i in range(5):
            phi = eigenfunctions[:, i]
            norm_squared = trapezoid(np.abs(phi)**2, op.x)
            assert np.isclose(norm_squared, 1.0, rtol=1e-2)
    
    def test_zero_as_black_hole(self):
        """Test black hole interpretation."""
        op = VibrationalOperatorHpsi(n_points=100, n_primes=10)
        eigenvalues, _ = op.compute_spectrum(n_eigenvalues=5)
        
        bh = op.zero_as_black_hole(0)
        
        assert 't_n' in bh
        assert 'frequency' in bh
        assert 'energy' in bh
        assert 'spectral_mass' in bh
        
        # Frequency should be positive
        assert bh['frequency'] > 0
        # Energy should be positive
        assert bh['energy'] > 0
        # Spectral mass should be positive
        assert bh['spectral_mass'] > 0
    
    def test_frequency_base(self):
        """Test that fundamental frequency is preserved."""
        op = VibrationalOperatorHpsi(lambda_freq=F0)
        assert op.lambda_freq == F0
        assert np.isclose(F0, 141.7001, atol=1e-4)


class TestCurvedSpacetimeHpsi:
    """Test suite for H_Ψg operator."""
    
    def test_consciousness_field(self):
        """Test consciousness field evaluation."""
        psi_field = ConsciousnessField(coherence_level=C_COHERENCE)
        
        x = np.array([1.0, 5.0, 10.0, 20.0])
        psi_vals = psi_field.evaluate(x)
        
        assert len(psi_vals) == len(x)
        assert np.all(psi_vals >= 0)  # Consciousness is non-negative
        assert np.all(psi_vals <= 1.0)  # Normalized
    
    def test_metric_computation(self):
        """Test consciousness-curved metric."""
        psi_field = ConsciousnessField()
        curved_op = CurvedSpacetimeHpsi(
            consciousness_field=psi_field,
            n_points=50,
            n_primes=10
        )
        
        # Metric should be positive (space-like)
        assert np.all(curved_op.g_xx > 0)
        
        # Volume element should be positive
        assert np.all(curved_op.Omega > 0)
    
    def test_curved_operator_hermiticity(self):
        """Test that curved operator is Hermitian."""
        psi_field = ConsciousnessField()
        curved_op = CurvedSpacetimeHpsi(
            consciousness_field=psi_field,
            n_points=50,
            n_primes=10
        )
        
        H = curved_op.construct_operator()
        assert np.allclose(H, H.conj().T, atol=1e-10)
    
    def test_curved_spectrum(self):
        """Test spectrum computation in curved space."""
        psi_field = ConsciousnessField()
        curved_op = CurvedSpacetimeHpsi(
            consciousness_field=psi_field,
            n_points=100,
            n_primes=10
        )
        
        eigenvalues, eigenfunctions = curved_op.compute_spectrum(n_eigenvalues=5)
        
        assert len(eigenvalues) == 5
        assert eigenfunctions.shape == (100, 5)
        assert np.all(np.isreal(eigenvalues))
    
    def test_flat_vs_curved_difference(self):
        """Test that curved space shifts spectrum."""
        psi_field = ConsciousnessField()
        
        flat_op = VibrationalOperatorHpsi(
            n_points=100,
            n_primes=10
        )
        
        curved_op = CurvedSpacetimeHpsi(
            consciousness_field=psi_field,
            n_points=100,
            n_primes=10,
            alpha_coupling=0.2  # Strong coupling to see effect
        )
        
        flat_eigs, _ = flat_op.compute_spectrum(n_eigenvalues=5)
        curved_eigs, _ = curved_op.compute_spectrum(n_eigenvalues=5)
        
        # Spectra should be different (consciousness effect)
        assert not np.allclose(flat_eigs, curved_eigs, atol=1e-3)
        
        # But not wildly different (controlled perturbation)
        relative_diff = np.abs(curved_eigs - flat_eigs) / (np.abs(flat_eigs) + 1e-10)
        assert np.all(relative_diff < 0.5)  # Less than 50% shift
    
    def test_zero_visibility(self):
        """Test observer-dependent zero visibility."""
        psi_field = ConsciousnessField()
        curved_op = CurvedSpacetimeHpsi(
            consciousness_field=psi_field,
            n_points=100,
            n_primes=10
        )
        
        sample_zeros = np.array([10.0, 20.0, 30.0, 40.0, 50.0])
        
        # Test at different positions
        visible_1 = curved_op.visible_zeros(sample_zeros, observer_position=5.0)
        visible_2 = curved_op.visible_zeros(sample_zeros, observer_position=15.0)
        
        assert len(visible_1) <= len(sample_zeros)
        assert len(visible_2) <= len(sample_zeros)


class TestObservationalHorizon:
    """Test suite for observational horizon framework."""
    
    def test_observer_state(self):
        """Test observer state initialization."""
        observer = ObserverState(
            position=10.0,
            intensity=0.8,
            coherence=0.9,
            c_level=C_COHERENCE
        )
        
        assert observer.position == 10.0
        assert observer.intensity == 0.8
        assert observer.coherence == 0.9
        
        psi = observer.consciousness_value()
        assert psi > 0
        assert psi <= 1.0
    
    def test_horizon_radius(self):
        """Test horizon radius computation."""
        observer = ObserverState(position=10.0, coherence=0.9)
        
        max_zero = 100.0
        horizon = observer.horizon_radius(max_zero)
        
        assert horizon > 0
        assert horizon <= max_zero  # Cannot exceed maximum
    
    def test_zero_visibility_decision(self):
        """Test can_see_zero method."""
        observer_low = ObserverState(position=10.0, coherence=0.3)
        observer_high = ObserverState(position=10.0, coherence=0.95)
        
        max_zero = 100.0
        test_zero = 50.0
        
        # High coherence observer should see more
        low_horizon = observer_low.horizon_radius(max_zero)
        high_horizon = observer_high.horizon_radius(max_zero)
        
        assert high_horizon > low_horizon
    
    def test_horizon_expansion(self):
        """Test horizon expansion with increasing coherence."""
        zeros = np.array([10.0, 20.0, 30.0, 40.0, 50.0])
        horizon_sys = ObservationalHorizon(zeros, f0=F0)
        
        coherence_levels = np.array([0.2, 0.5, 0.8, 0.95])
        expansion_data = horizon_sys.horizon_expansion_sequence(coherence_levels)
        
        assert len(expansion_data) == len(coherence_levels)
        
        # Number of visible zeros should increase with coherence
        n_visible = [d['n_visible'] for d in expansion_data]
        assert all(n_visible[i] <= n_visible[i+1] for i in range(len(n_visible)-1))
    
    def test_schwarzschild_correspondence(self):
        """Test Schwarzschild correspondence."""
        zeros = np.array([10.0, 20.0, 30.0])
        horizon_sys = ObservationalHorizon(zeros, f0=F0)
        
        observer = ObserverState(position=10.0, coherence=0.9)
        correspondence = horizon_sys.schwarzschild_correspondence(observer)
        
        assert 'riemann_horizon' in correspondence
        assert 'effective_mass' in correspondence
        assert 'schwarzschild_radius' in correspondence
        
        # Effective mass should be positive
        assert correspondence['effective_mass'] > 0
        # Schwarzschild radius should be positive
        assert correspondence['schwarzschild_radius'] > 0
    
    def test_coherence_visibility_monotonicity(self):
        """Test that higher coherence always sees more or equal zeros."""
        zeros = np.linspace(10, 100, 20)
        horizon_sys = ObservationalHorizon(zeros, f0=F0)
        
        for A_1, A_2 in [(0.3, 0.5), (0.5, 0.7), (0.7, 0.9)]:
            obs_1 = ObserverState(position=10.0, coherence=A_1)
            obs_2 = ObserverState(position=10.0, coherence=A_2)
            
            visible_1, _ = horizon_sys.compute_visible_zeros(obs_1)
            visible_2, _ = horizon_sys.compute_visible_zeros(obs_2)
            
            # Higher coherence sees more (or equal)
            assert len(visible_2) >= len(visible_1)


class TestConsistency:
    """Test consistency across modules."""
    
    def test_frequency_consistency(self):
        """Test that f₀ = 141.7001 Hz is consistent everywhere."""
        assert np.isclose(F0, 141.7001, atol=1e-4)
        
        op = VibrationalOperatorHpsi()
        assert op.lambda_freq == F0
    
    def test_coherence_constant_consistency(self):
        """Test that C = 244.36 is consistent."""
        assert np.isclose(C_COHERENCE, 244.36, atol=1e-2)
        
        psi_field = ConsciousnessField()
        assert psi_field.coherence_level == C_COHERENCE


if __name__ == "__main__":
    pytest.main([__file__, "-v", "-s"])
