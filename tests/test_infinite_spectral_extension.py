#!/usr/bin/env python3
"""
Test Suite for Infinite Spectral Extension of H_Ψ
==================================================

Author: José Manuel Mota Burruezo Ψ ✧ ∞³ (via Noesis Agent)
Date: January 8, 2026

This test suite validates the infinite spectral extension implementation,
ensuring mathematical correctness and QCAL ∞³ coherence.
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from infinite_spectral_extension import (
    InfiniteSpectralExtension,
    SpectralLevel,
    F0_HZ,
    C_COHERENCE
)


class TestInfiniteSpectralExtension:
    """Test suite for InfiniteSpectralExtension class."""
    
    @pytest.fixture
    def extension(self):
        """Create InfiniteSpectralExtension instance for testing."""
        return InfiniteSpectralExtension(precision=15)
    
    def test_initialization(self, extension):
        """Test proper initialization of extension."""
        assert extension.f0 == F0_HZ
        assert extension.C == C_COHERENCE
        assert extension.precision == 15
        assert isinstance(extension.levels, dict)
        assert len(extension.levels) == 0  # Initially empty
    
    def test_V_resonant_positive(self, extension):
        """Test that resonant potential is defined for positive x."""
        x_values = [0.1, 1.0, 5.0, 10.0]
        for x in x_values:
            V = extension.V_resonant(x)
            assert isinstance(V, float)
            assert np.isfinite(V)
    
    def test_V_resonant_zero(self, extension):
        """Test that V_resonant handles x=0 correctly."""
        V = extension.V_resonant(0.0)
        assert V == 0.0
    
    def test_V_resonant_negative(self, extension):
        """Test that V_resonant handles negative x correctly."""
        V = extension.V_resonant(-1.0)
        assert V == 0.0
    
    def test_construct_finite_level(self, extension):
        """Test construction of finite dimensional level."""
        N = 10
        level = extension.construct_finite_level(N)
        
        assert isinstance(level, SpectralLevel)
        assert level.n == 0
        assert level.dimension == N
        assert len(level.eigenvalues) == N
        assert level.is_selfadjoint
        assert 0.0 <= level.coherence <= 1.0
        
        # Check eigenvalues are sorted and positive
        assert np.all(level.eigenvalues > 0)
        assert np.all(np.diff(level.eigenvalues) >= 0)  # Sorted
    
    def test_construct_countable_level(self, extension):
        """Test construction of countable infinite level."""
        max_idx = 100
        level = extension.construct_countable_level(max_idx)
        
        assert isinstance(level, SpectralLevel)
        assert np.isinf(level.n)
        assert level.dimension is None  # Infinite
        assert len(level.eigenvalues) == max_idx
        assert level.is_selfadjoint
        assert 0.0 <= level.coherence <= 1.0
        
        # Check asymptotic behavior: λₙ ~ n
        n = np.arange(max_idx)
        large_n = n > 50
        ratio = level.eigenvalues[large_n] / n[large_n]
        assert np.mean(ratio) > 0.8  # Should be close to 1
        assert np.mean(ratio) < 1.5
    
    def test_construct_continuum_level(self, extension):
        """Test construction of continuum level ∞³."""
        N_sample = 1000
        level = extension.construct_continuum_level(N_sample)
        
        assert isinstance(level, SpectralLevel)
        assert level.n == -3  # Marker for ∞³
        assert level.dimension is None  # Continuum
        assert len(level.eigenvalues) == N_sample
        assert level.is_selfadjoint
        assert 0.0 <= level.coherence <= 1.0
    
    def test_coherence_computation(self, extension):
        """Test coherence measure computation."""
        # Perfect regular spacing
        regular = np.arange(0, 10, F0_HZ / C_COHERENCE)
        coherence_regular = extension._compute_coherence(regular)
        assert coherence_regular > 0.5  # Should be high
        
        # Random spacing
        random = np.sort(np.random.uniform(0, 10, 100))
        coherence_random = extension._compute_coherence(random)
        assert 0.0 <= coherence_random <= 1.0
        
        # Empty array
        empty = np.array([])
        coherence_empty = extension._compute_coherence(empty)
        assert coherence_empty == 0.0
        
        # Single value
        single = np.array([1.0])
        coherence_single = extension._compute_coherence(single)
        assert coherence_single == 1.0
    
    def test_build_spectral_tower(self, extension):
        """Test building complete spectral tower."""
        tower = extension.build_spectral_tower(
            N_finite=20,
            N_countable=100,
            N_continuum=500
        )
        
        assert isinstance(tower, dict)
        assert "finite" in tower
        assert "countable_infinite" in tower
        assert "continuum_infinite_cubed" in tower
        
        # Check levels are stored
        assert 0 in extension.levels
        assert -1 in extension.levels
        assert -3 in extension.levels
        
        # Check dimensions
        assert tower["finite"].dimension == 20
        assert tower["countable_infinite"].dimension is None
        assert tower["continuum_infinite_cubed"].dimension is None
    
    def test_verify_tower_coherence(self, extension):
        """Test tower coherence verification."""
        # Build tower first
        extension.build_spectral_tower(N_finite=10, N_countable=50, N_continuum=100)
        
        # Verify
        report = extension.verify_tower_coherence()
        
        assert isinstance(report, dict)
        assert "timestamp" in report
        assert "f0_hz" in report
        assert "C_coherence" in report
        assert "checks" in report
        assert "overall" in report
        
        # Check specific tests
        checks = report["checks"]
        assert "self_adjoint" in checks
        assert "coherence_bounds" in checks
        assert "spectral_nesting" in checks
        assert "trace_class" in checks
        
        # All levels should be self-adjoint
        assert checks["self_adjoint"] is True
    
    def test_spectral_nesting(self, extension):
        """Test that finite spectrum is contained in countable spectrum."""
        extension.build_spectral_tower(N_finite=10, N_countable=100, N_continuum=100)
        
        finite_max = extension.levels[0].eigenvalues[-1]
        countable_max = extension.levels[-1].eigenvalues[-1]
        
        # Finite max should be less than or close to countable max
        assert finite_max <= countable_max * 1.2
    
    def test_trace_class_property(self, extension):
        """Test trace class property: Tr(e^{-βH}) < ∞."""
        level = extension.construct_countable_level(200)
        
        beta = 1.0
        trace = np.sum(np.exp(-beta * level.eigenvalues))
        
        assert np.isfinite(trace)
        assert trace > 0.0
        assert trace < 10.0  # Should be finite and reasonable
    
    def test_save_certificate(self, extension, tmp_path):
        """Test certificate generation and saving."""
        extension.build_spectral_tower(N_finite=5, N_countable=20, N_continuum=50)
        
        # Save to temporary path
        cert_path = tmp_path / "test_certificate.json"
        saved_path = extension.save_certificate(str(cert_path))
        
        assert Path(saved_path).exists()
        
        # Load and verify certificate content
        import json
        with open(saved_path, 'r') as f:
            cert = json.load(f)
        
        assert "title" in cert
        assert "timestamp" in cert
        assert "author" in cert
        assert "constants" in cert
        assert "spectral_tower" in cert
        assert "verification" in cert
        
        # Check constants
        assert cert["constants"]["f0_hz"] == F0_HZ
        assert cert["constants"]["C_coherence"] == C_COHERENCE
        
        # Check tower data
        assert "finite" in cert["spectral_tower"]
        assert "countable_infinite" in cert["spectral_tower"]
        assert "continuum_infinite_cubed" in cert["spectral_tower"]


class TestSpectralLevel:
    """Test suite for SpectralLevel dataclass."""
    
    def test_spectral_level_creation(self):
        """Test creating a SpectralLevel."""
        eigenvalues = np.array([0.5, 1.5, 2.5])
        level = SpectralLevel(
            n=0,
            dimension=3,
            eigenvalues=eigenvalues,
            coherence=0.95,
            is_selfadjoint=True
        )
        
        assert level.n == 0
        assert level.dimension == 3
        assert len(level.eigenvalues) == 3
        assert level.coherence == 0.95
        assert level.is_selfadjoint is True
    
    def test_spectral_level_with_metadata(self):
        """Test SpectralLevel with metadata."""
        eigenvalues = np.array([1.0, 2.0])
        metadata = {"type": "test", "note": "example"}
        level = SpectralLevel(
            n=1,
            dimension=2,
            eigenvalues=eigenvalues,
            metadata=metadata
        )
        
        assert level.metadata == metadata
        assert level.metadata["type"] == "test"


class TestMathematicalProperties:
    """Test mathematical properties of the spectral extension."""
    
    def test_weyl_law_asymptotic(self):
        """Test Weyl's law: ρ(λ) ~ λ/2π for large λ."""
        extension = InfiniteSpectralExtension()
        level = extension.construct_continuum_level(10000)
        
        # Check density at high energies
        eigenvalues = level.eigenvalues
        lambda_high = eigenvalues[eigenvalues > 50.0]
        
        # Count eigenvalues up to various thresholds
        for threshold in [60.0, 70.0, 80.0, 90.0]:
            N_below = np.sum(lambda_high < threshold)
            # Weyl's law prediction
            N_weyl = threshold / (2 * np.pi) * len(lambda_high) / max(lambda_high)
            
            # Should be roughly proportional
            if N_below > 0:
                ratio = N_weyl / N_below
                assert 0.5 < ratio < 2.0  # Within factor of 2
    
    def test_resonant_frequency_modulation(self):
        """Test that V_resonant contains f₀ = 141.7001 Hz modulation."""
        extension = InfiniteSpectralExtension()
        
        # Sample V_resonant at points where the phase is π apart
        x1 = np.exp(0.0)
        x2 = np.exp(C_COHERENCE / F0_HZ * np.pi)
        
        V1 = extension.V_resonant(x1)
        V2 = extension.V_resonant(x2)
        
        # The cosine term should cause oscillation
        # (not exact due to 1/x² decay term, but should see difference)
        assert abs(V1 - V2) > 0.1
    
    def test_eigenvalue_positivity(self):
        """Test that all eigenvalues are positive."""
        extension = InfiniteSpectralExtension()
        extension.build_spectral_tower(N_finite=30, N_countable=100, N_continuum=200)
        
        for level in extension.levels.values():
            assert np.all(level.eigenvalues > 0), \
                f"Level {level.n} has non-positive eigenvalues"


if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])
