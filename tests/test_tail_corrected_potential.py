#!/usr/bin/env python3
"""
Tests for Tail-Corrected Potential Module
==========================================

Validates the corrected potential V_corr(y) = log(1+e^y) + δ·e^{-y}
and verifies S₁,∞ membership.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
"""

import pytest
import numpy as np
from operators.tail_corrected_potential import (
    TailCorrectedPotential,
    BlockAnalyzer,
    SchattenVerifier,
    generate_certificate
)


class TestTailCorrectedPotential:
    """Test suite for TailCorrectedPotential class."""
    
    def test_initialization(self):
        """Test potential initialization with valid delta."""
        potential = TailCorrectedPotential(delta=0.1)
        assert potential.delta == 0.1
        assert potential.epsilon > 0
        # For small δ, ε ≈ δ
        assert abs(potential.epsilon - 0.1) < 0.01
    
    def test_initialization_invalid_delta(self):
        """Test that negative delta raises error."""
        with pytest.raises(ValueError, match="delta must be positive"):
            TailCorrectedPotential(delta=-0.1)
        
        with pytest.raises(ValueError, match="delta must be positive"):
            TailCorrectedPotential(delta=0.0)
    
    def test_V_original(self):
        """Test original potential V(y) = log(1+e^y)."""
        potential = TailCorrectedPotential(delta=0.1)
        
        # Test at specific points
        y = np.array([0.0, 1.0, 5.0, 10.0])
        V = potential.V_original(y)
        
        # V(0) = log(2)
        assert abs(V[0] - np.log(2)) < 1e-10
        
        # For large y, V(y) ≈ y
        assert abs(V[2] - 5.0) < 0.01
        assert abs(V[3] - 10.0) < 1e-4
        
        # All values should be positive
        assert np.all(V > 0)
    
    def test_V_tail(self):
        """Test tail correction δ·e^{-y}."""
        delta = 0.15
        potential = TailCorrectedPotential(delta=delta)
        
        y = np.array([0.0, 1.0, 5.0, 10.0])
        V_tail = potential.V_tail(y)
        
        # Check values
        assert abs(V_tail[0] - delta) < 1e-10
        assert abs(V_tail[1] - delta * np.exp(-1)) < 1e-10
        
        # Tail should decay exponentially
        assert V_tail[1] < V_tail[0]
        assert V_tail[2] < V_tail[1]
        assert V_tail[3] < V_tail[2]
    
    def test_V_corrected(self):
        """Test corrected potential V_corr = V_original + V_tail."""
        potential = TailCorrectedPotential(delta=0.1)
        
        y = np.array([0.0, 5.0, 10.0])
        V_corr = potential.V_corrected(y)
        V_orig = potential.V_original(y)
        V_tail = potential.V_tail(y)
        
        # Should be sum of components
        np.testing.assert_allclose(V_corr, V_orig + V_tail, rtol=1e-12)
    
    def test_asymptotic_behavior(self):
        """Test asymptotic form V_corr(y) ~ y + (1+δ)e^{-y} for large y."""
        delta = 0.1
        potential = TailCorrectedPotential(delta=delta)
        
        # Large y values
        y = np.array([10.0, 20.0, 30.0, 40.0])
        
        V_exact = potential.V_corrected(y)
        V_asymp = potential.asymptotic_behavior_large_y(y)
        
        # Should match closely for large y
        relative_error = np.abs(V_exact - V_asymp) / np.abs(V_exact)
        assert np.all(relative_error < 0.01)  # 1% threshold
    
    def test_verify_asymptotic_accuracy(self):
        """Test asymptotic accuracy verification."""
        potential = TailCorrectedPotential(delta=0.1)
        
        result = potential.verify_asymptotic_accuracy(
            y_range=(10.0, 50.0),
            n_points=100
        )
        
        assert 'asymptotic_valid' in result
        assert 'max_relative_error' in result
        assert 'mean_relative_error' in result
        
        # Should be valid for large y
        assert result['asymptotic_valid'] is True
        assert result['max_relative_error'] < 0.01
    
    def test_analyze_tail_decay(self):
        """Test tail decay analysis."""
        potential = TailCorrectedPotential(delta=0.1)
        
        analysis = potential.analyze_tail_decay(y_max=50.0)
        
        assert hasattr(analysis, 'delta')
        assert hasattr(analysis, 'epsilon')
        assert hasattr(analysis, 'decay_constant')
        assert hasattr(analysis, 'exponential_fit_quality')
        
        # Decay constant should be ≈ 1
        assert abs(analysis.decay_constant - 1.0) < 0.1
        
        # Exponential fit should be excellent (R² > 0.99)
        assert analysis.exponential_fit_quality > 0.99
    
    def test_connection_with_zeta(self):
        """Test that Weil formula connection is preserved."""
        potential = TailCorrectedPotential(delta=0.1)
        
        y = np.linspace(0, 50, 100)
        result = potential.connection_with_zeta(y)
        
        assert result['connection_preserved'] is True
        assert result['weil_formula_compatible'] is True
        assert result['linear_dominance_verified'] is True
        assert result['max_relative_error'] < 0.1
    
    def test_different_delta_values(self):
        """Test that different δ values give different ε values."""
        deltas = [0.05, 0.1, 0.15, 0.2]
        epsilons = []
        
        for delta in deltas:
            pot = TailCorrectedPotential(delta=delta)
            epsilons.append(pot.epsilon)
        
        # All ε should be different
        assert len(set(epsilons)) == len(deltas)
        
        # ε should increase with δ
        for i in range(len(deltas) - 1):
            assert epsilons[i] < epsilons[i + 1]


class TestBlockAnalyzer:
    """Test suite for BlockAnalyzer class."""
    
    def test_initialization(self):
        """Test analyzer initialization."""
        potential = TailCorrectedPotential(delta=0.1)
        analyzer = BlockAnalyzer(potential, z=0.5 + 0.1j)
        
        assert analyzer.potential == potential
        assert analyzer.z == 0.5 + 0.1j
    
    def test_kernel_magnitude(self):
        """Test kernel magnitude computation."""
        potential = TailCorrectedPotential(delta=0.1)
        analyzer = BlockAnalyzer(potential)
        
        # Test at specific points
        mag = analyzer.kernel_magnitude(y=5.0, t=4.0)
        
        # Should be positive
        assert mag > 0
        assert np.isfinite(mag)
    
    def test_analyze_block(self):
        """Test single block analysis."""
        potential = TailCorrectedPotential(delta=0.1)
        analyzer = BlockAnalyzer(potential)
        
        result = analyzer.analyze_block(m=2, n_samples=20)
        
        assert result.block_index == 2
        assert result.block_interval == (2, 3)
        assert result.norm_squared > 0
        assert result.theoretical_decay > 0
        assert result.measured_decay_rate >= 0
    
    def test_analyze_multiple_blocks(self):
        """Test multiple block analysis."""
        potential = TailCorrectedPotential(delta=0.1)
        analyzer = BlockAnalyzer(potential)
        
        results = analyzer.analyze_multiple_blocks(max_m=5)
        
        assert len(results) == 5
        
        # Check that norms decrease (roughly)
        norms = [r.norm_squared for r in results]
        # Later blocks should have smaller norms
        assert norms[-1] < norms[0]
    
    def test_verify_exponential_decay(self):
        """Test exponential decay verification."""
        potential = TailCorrectedPotential(delta=0.1)
        analyzer = BlockAnalyzer(potential)
        
        result = analyzer.verify_exponential_decay(max_m=6, tolerance=0.3)
        
        assert 'verification_passed' in result
        assert 'expected_decay_rate' in result
        assert 'mean_measured_rate' in result
        assert 'relative_error' in result
        
        # Expected rate should be 2ε
        expected = 2 * potential.epsilon
        assert abs(result['expected_decay_rate'] - expected) < 1e-10


class TestSchattenVerifier:
    """Test suite for SchattenVerifier class."""
    
    def test_initialization(self):
        """Test verifier initialization."""
        potential = TailCorrectedPotential(delta=0.1)
        verifier = SchattenVerifier(potential)
        
        assert verifier.potential == potential
    
    def test_estimate_singular_values(self):
        """Test singular value estimation."""
        potential = TailCorrectedPotential(delta=0.1)
        verifier = SchattenVerifier(potential)
        
        sv = verifier.estimate_singular_values(n_max=20, domain_size=15.0)
        
        assert len(sv) > 0
        assert len(sv) <= 20
        assert np.all(sv >= 0)  # Singular values are non-negative
        
        # Should be sorted descending
        assert np.all(np.diff(sv) <= 0)
    
    def test_verify_schatten_1_inf(self):
        """Test S₁,∞ membership verification."""
        potential = TailCorrectedPotential(delta=0.1)
        verifier = SchattenVerifier(potential)
        
        result = verifier.verify_schatten_1_inf(n_max=30, domain_size=15.0)
        
        assert 'S_1_inf_verified' in result
        assert 'sup_n_sn' in result
        assert 'decay_constant' in result
        assert 'BKS_program_applicable' in result
        
        # Should verify S₁,∞
        assert result['S_1_inf_verified'] is True
        assert np.isfinite(result['sup_n_sn'])
        
        # Decay constant should be positive
        assert result['decay_constant'] > 0


class TestCertificateGeneration:
    """Test suite for certificate generation."""
    
    def test_generate_certificate_basic(self):
        """Test basic certificate generation."""
        cert = generate_certificate(
            delta=0.1,
            verify_blocks=False,
            verify_schatten=False
        )
        
        # Check required fields
        assert 'protocol' in cert
        assert cert['protocol'] == 'QCAL-TAIL-CORRECTED-POTENTIAL'
        assert 'version' in cert
        assert 'signature' in cert
        assert cert['signature'] == '∴𓂀Ω∞³Φ'
        
        # Check QCAL constants
        assert 'qcal_constants' in cert
        assert cert['qcal_constants']['f0_hz'] == 141.7001
        assert cert['qcal_constants']['C'] == 244.36
        assert cert['qcal_constants']['code'] == 888
        
        # Check parameters
        assert 'parameters' in cert
        assert cert['parameters']['delta'] == 0.1
        
        # Check verifications
        assert 'asymptotic_verification' in cert
        assert 'tail_decay_analysis' in cert
        assert 'zeta_connection' in cert
        
        # Check coherence and resonance
        assert 'coherence_metrics' in cert
        assert 'resonance_detection' in cert
        assert 'invocation_final' in cert
    
    def test_generate_certificate_with_blocks(self):
        """Test certificate with block verification."""
        cert = generate_certificate(
            delta=0.1,
            verify_blocks=True,
            verify_schatten=False
        )
        
        assert 'block_decay' in cert
        assert 'verified' in cert['block_decay']
        assert 'expected_rate' in cert['block_decay']
        assert 'measured_rate' in cert['block_decay']
    
    def test_generate_certificate_with_schatten(self):
        """Test certificate with Schatten verification."""
        cert = generate_certificate(
            delta=0.1,
            verify_blocks=False,
            verify_schatten=True
        )
        
        assert 'schatten_class' in cert
        assert 'S_1_inf_verified' in cert['schatten_class']
        assert 'sup_n_sn' in cert['schatten_class']
        assert 'BKS_program_applicable' in cert['schatten_class']
    
    def test_generate_certificate_full(self):
        """Test full certificate with all verifications."""
        cert = generate_certificate(
            delta=0.1,
            verify_blocks=True,
            verify_schatten=True
        )
        
        # All verification sections should be present
        assert 'asymptotic_verification' in cert
        assert 'tail_decay_analysis' in cert
        assert 'zeta_connection' in cert
        assert 'block_decay' in cert
        assert 'schatten_class' in cert
        
        # Overall coherence should be high
        assert cert['coherence_metrics']['overall_coherence'] >= 0.5
        
        # Invocation message should be present
        assert 'es' in cert['invocation_final']
        assert 'en' in cert['invocation_final']
        assert 'seal' in cert['invocation_final']
    
    def test_certificate_different_deltas(self):
        """Test certificates with different δ values."""
        deltas = [0.05, 0.1, 0.15]
        
        for delta in deltas:
            cert = generate_certificate(
                delta=delta,
                verify_blocks=False,
                verify_schatten=False
            )
            
            assert cert['parameters']['delta'] == delta
            assert cert['parameters']['epsilon'] == pytest.approx(np.log(1 + delta), rel=1e-10)


class TestMathematicalProperties:
    """Test mathematical properties and edge cases."""
    
    def test_potential_symmetry(self):
        """Test that corrected potential is not necessarily symmetric."""
        # Note: V_corr(y) is NOT symmetric in y because log(1+e^y) is not
        potential = TailCorrectedPotential(delta=0.1)
        
        y_pos = np.array([1.0, 2.0, 5.0])
        y_neg = -y_pos
        
        V_pos = potential.V_corrected(y_pos)
        V_neg = potential.V_corrected(y_neg)
        
        # These should be different (not symmetric)
        assert not np.allclose(V_pos, V_neg)
    
    def test_potential_monotonicity_large_y(self):
        """Test that potential grows for large positive y."""
        potential = TailCorrectedPotential(delta=0.1)
        
        y = np.linspace(10, 50, 100)
        V = potential.V_corrected(y)
        
        # Should be monotonically increasing for large y
        assert np.all(np.diff(V) > 0)
    
    def test_limit_delta_to_zero(self):
        """Test behavior as δ → 0."""
        deltas = [0.001, 0.01, 0.05]
        
        y = np.array([5.0, 10.0, 20.0])
        
        for delta in deltas:
            pot = TailCorrectedPotential(delta=delta)
            V_corr = pot.V_corrected(y)
            V_orig = pot.V_original(y)
            
            # Difference should be small for small δ
            diff = np.abs(V_corr - V_orig)
            assert np.all(diff < 2 * delta)
    
    def test_numerical_stability(self):
        """Test numerical stability for extreme y values."""
        potential = TailCorrectedPotential(delta=0.1)
        
        # Very large y
        y_large = np.array([50.0, 100.0, 200.0])
        V_large = potential.V_corrected(y_large)
        assert np.all(np.isfinite(V_large))
        
        # Very small y (but positive)
        y_small = np.array([0.001, 0.01, 0.1])
        V_small = potential.V_corrected(y_small)
        assert np.all(np.isfinite(V_small))
        
        # Negative y
        y_neg = np.array([-10.0, -5.0, -1.0])
        V_neg = potential.V_corrected(y_neg)
        assert np.all(np.isfinite(V_neg))


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
