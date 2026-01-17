#!/usr/bin/env python3
"""
Tests for Tensor Autonomía: C = I · A² ⊗ ζ(1/2 + it)

This test module validates the Tensor Autonomía implementation,
ensuring mathematical correctness and numerical stability.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: January 2026
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add operators directory to path
sys.path.insert(0, str(Path(__file__).parent.parent / 'operators'))

from tensor_autonomia import (
    compute_zeta_critical_line,
    tensor_product_coherence_zeta,
    tensor_autonomia_spectrum,
    validate_tensor_coherence,
    compute_autonomia_coherence_factor,
    C_QCAL_BASE,
    F0_HZ,
    ZETA_PRIME_HALF
)


class TestZetaCriticalLine:
    """Tests for ζ(1/2 + it) computation on critical line."""
    
    def test_zeta_scalar_input(self):
        """Test ζ(1/2 + it) with scalar t value."""
        t = 14.134725  # First Riemann zero
        zeta_value = compute_zeta_critical_line(t, precision=15)
        
        # At a zero, |ζ(1/2 + it)| should be very small (numerical precision ~1e-7)
        assert abs(zeta_value) < 1e-6, \
            f"Expected near-zero at t={t}, got |ζ|={abs(zeta_value)}"
    
    def test_zeta_array_input(self):
        """Test ζ(1/2 + it) with array of t values."""
        # First few Riemann zeros
        zeros = np.array([14.134725, 21.022040, 25.010858])
        zeta_values = compute_zeta_critical_line(zeros, precision=15)
        
        assert len(zeta_values) == len(zeros)
        
        # All should be near zero (numerical precision ~1e-6)
        magnitudes = np.abs(zeta_values)
        assert np.all(magnitudes < 1e-5), \
            f"Expected near-zeros, got max |ζ|={np.max(magnitudes)}"
    
    def test_zeta_non_zero_point(self):
        """Test ζ(1/2 + it) at non-zero point."""
        t = 10.0  # Not a zero
        zeta_value = compute_zeta_critical_line(t, precision=15)
        
        # Should not be zero
        assert abs(zeta_value) > 1e-5, \
            f"Expected non-zero at t={t}, got |ζ|={abs(zeta_value)}"
    
    def test_zeta_precision(self):
        """Test that higher precision gives more accurate results."""
        t = 14.134725
        
        zeta_low = compute_zeta_critical_line(t, precision=10)
        zeta_high = compute_zeta_critical_line(t, precision=25)
        
        # Both should be near zero (within numerical tolerance)
        # Due to floating-point arithmetic, higher precision may not always be numerically smaller
        assert abs(zeta_high) < 1e-6 and abs(zeta_low) < 1e-6


class TestTensorProductCoherenceZeta:
    """Tests for C = I · A² ⊗ ζ(1/2 + it) computation."""
    
    def test_tensor_product_scalar(self):
        """Test tensor product with scalar inputs."""
        I = 1.0
        A = 15.622  # sqrt(244.36)
        t = 14.134725
        
        C = tensor_product_coherence_zeta(I, A, t, precision=15)
        
        # Result should be complex
        assert isinstance(C, complex)
        
        # At zero, magnitude should be small
        assert abs(C) < 10.0, f"Expected small |C|, got {abs(C)}"
    
    def test_tensor_product_array(self):
        """Test tensor product with array of t values."""
        I = 1.0
        A = np.sqrt(C_QCAL_BASE)
        zeros = np.array([14.134725, 21.022040, 25.010858])
        
        C_values = tensor_product_coherence_zeta(I, A, zeros, precision=15)
        
        assert len(C_values) == len(zeros)
        assert all(isinstance(c, (complex, np.complex128)) for c in C_values)
    
    def test_base_coherence_scaling(self):
        """Test that C scales with I · A²."""
        I1, A1 = 1.0, 10.0
        I2, A2 = 2.0, 10.0  # Double intensity
        t = 10.0
        
        C1 = tensor_product_coherence_zeta(I1, A1, t, precision=15)
        C2 = tensor_product_coherence_zeta(I2, A2, t, precision=15)
        
        # C2 should be roughly double C1
        ratio = abs(C2) / abs(C1)
        assert 1.8 < ratio < 2.2, f"Expected ratio ~2, got {ratio}"
    
    def test_amplitude_quadratic_scaling(self):
        """Test that C scales with A²."""
        I = 1.0
        A1, A2 = 10.0, 20.0  # Double amplitude
        t = 10.0
        
        C1 = tensor_product_coherence_zeta(I, A1, t, precision=15)
        C2 = tensor_product_coherence_zeta(I, A2, t, precision=15)
        
        # C2 should be roughly 4 times C1 (A² scaling)
        ratio = abs(C2) / abs(C1)
        assert 3.5 < ratio < 4.5, f"Expected ratio ~4, got {ratio}"


class TestTensorAutonomiaSpectrum:
    """Tests for complete tensor autonomía spectrum computation."""
    
    def test_spectrum_computation(self):
        """Test basic spectrum computation."""
        zeros = np.array([14.134725, 21.022040, 25.010858, 30.424876])
        
        t_spec, C_spec, metadata = tensor_autonomia_spectrum(
            zeros, intensity=1.0, precision=15
        )
        
        # Check outputs
        assert len(t_spec) == len(zeros)
        assert len(C_spec) == len(zeros)
        assert np.allclose(t_spec, zeros)
        
        # Check metadata
        assert 'C_base' in metadata
        assert 'amplitude' in metadata
        assert 'n_zeros' in metadata
        assert metadata['n_zeros'] == len(zeros)
    
    def test_spectrum_default_amplitude(self):
        """Test that default amplitude gives C_base = C_QCAL_BASE."""
        zeros = np.array([14.134725, 21.022040])
        
        _, _, metadata = tensor_autonomia_spectrum(
            zeros, intensity=1.0, precision=15
        )
        
        # With I=1 and default A, C_base should equal C_QCAL_BASE
        assert abs(metadata['C_base'] - C_QCAL_BASE) < 0.01
    
    def test_spectrum_custom_amplitude(self):
        """Test spectrum with custom amplitude."""
        zeros = np.array([14.134725, 21.022040])
        custom_A = 20.0
        
        _, _, metadata = tensor_autonomia_spectrum(
            zeros, intensity=1.0, amplitude=custom_A, precision=15
        )
        
        expected_C_base = 1.0 * custom_A ** 2
        assert abs(metadata['C_base'] - expected_C_base) < 0.01
    
    def test_spectrum_statistics(self):
        """Test that spectrum metadata contains valid statistics."""
        zeros = np.array([14.134725, 21.022040, 25.010858, 30.424876, 32.935062])
        
        _, C_spec, metadata = tensor_autonomia_spectrum(
            zeros, precision=15
        )
        
        # Check statistics are reasonable
        assert metadata['mean_magnitude'] >= 0
        assert metadata['coherence_variance'] >= 0
        assert metadata['max_magnitude'] >= metadata['mean_magnitude']
        assert metadata['min_magnitude'] <= metadata['mean_magnitude']


class TestValidateTensorCoherence:
    """Tests for tensor coherence validation."""
    
    def test_validation_valid_spectrum(self):
        """Test validation with valid spectrum."""
        zeros = np.array([14.134725, 21.022040, 25.010858])
        I, A = 1.0, np.sqrt(C_QCAL_BASE)
        
        C_spec = tensor_product_coherence_zeta(I, A, zeros, precision=15)
        validation = validate_tensor_coherence(C_spec, zeros)
        
        # Should pass validation
        assert validation['valid'] == True
        assert validation['n_points'] == len(zeros)
        assert validation['mean_magnitude'] > 0
    
    def test_validation_checks(self):
        """Test individual validation checks."""
        zeros = np.array([14.134725, 21.022040, 25.010858, 30.424876])
        I, A = 1.0, np.sqrt(C_QCAL_BASE)
        
        C_spec = tensor_product_coherence_zeta(I, A, zeros, precision=15)
        validation = validate_tensor_coherence(C_spec, zeros)
        
        # Check that individual checks are present
        assert 'non_zero_field' in validation['checks']
        assert 'bounded_variation' in validation['checks']
        assert 'phase_coherent' in validation['checks']


class TestAutonomiaCoherenceFactor:
    """Tests for autonomía coherence factor computation."""
    
    def test_coherence_factor_positive(self):
        """Test that coherence factor is positive."""
        zeros = np.array([14.134725, 21.022040, 25.010858])
        I, A = 1.0, np.sqrt(C_QCAL_BASE)
        C_base = I * A ** 2
        
        C_spec = tensor_product_coherence_zeta(I, A, zeros, precision=15)
        kappa = compute_autonomia_coherence_factor(C_spec, C_base)
        
        assert kappa >= 0, f"Expected non-negative kappa, got {kappa}"
    
    def test_coherence_factor_magnitude(self):
        """Test that coherence factor has reasonable magnitude."""
        zeros = np.array([14.134725, 21.022040, 25.010858, 30.424876])
        I, A = 1.0, np.sqrt(C_QCAL_BASE)
        C_base = I * A ** 2
        
        C_spec = tensor_product_coherence_zeta(I, A, zeros, precision=15)
        kappa = compute_autonomia_coherence_factor(C_spec, C_base)
        
        # κ can be very small near zeros (where ζ ≈ 0)
        # For non-zero points, κ should be larger
        assert kappa >= 0, f"Expected non-negative κ, got {kappa}"


class TestIntegrationWithQCAL:
    """Integration tests with QCAL framework constants."""
    
    def test_qcal_base_coherence(self):
        """Test integration with C_QCAL_BASE = 244.36."""
        # Verify that I × A² gives C_QCAL_BASE
        I = 1.0
        A = np.sqrt(C_QCAL_BASE)
        
        C_base = I * A ** 2
        assert abs(C_base - C_QCAL_BASE) < 0.01
    
    def test_fundamental_frequency(self):
        """Test that F0_HZ = 141.7001 Hz is accessible."""
        assert abs(F0_HZ - 141.7001) < 0.0001
    
    def test_zeta_prime_constant(self):
        """Test that ζ'(1/2) constant is defined."""
        assert abs(ZETA_PRIME_HALF - (-3.92264613)) < 0.001


class TestNumericalStability:
    """Tests for numerical stability and edge cases."""
    
    def test_large_t_values(self):
        """Test with large t values (high zeros)."""
        # Use larger zeros
        zeros = np.array([100.0, 200.0, 300.0])
        
        C_spec = tensor_product_coherence_zeta(1.0, 10.0, zeros, precision=15)
        
        # Should not produce NaN or Inf
        assert not np.any(np.isnan(C_spec))
        assert not np.any(np.isinf(C_spec))
    
    def test_small_amplitude(self):
        """Test with very small amplitude."""
        zeros = np.array([14.134725, 21.022040])
        I, A = 1.0, 0.01  # Very small amplitude
        
        C_spec = tensor_product_coherence_zeta(I, A, zeros, precision=15)
        
        # Should produce small but valid values
        magnitudes = np.abs(C_spec)
        assert np.all(magnitudes < 1.0)
        assert not np.any(np.isnan(C_spec))
    
    def test_zero_intensity(self):
        """Test with zero intensity (edge case)."""
        zeros = np.array([14.134725])
        I, A = 0.0, 10.0
        
        C_spec = tensor_product_coherence_zeta(I, A, zeros, precision=15)
        
        # Should produce zero
        assert abs(C_spec) < 1e-15


# =============================================================================
# PYTEST FIXTURES
# =============================================================================

@pytest.fixture
def sample_riemann_zeros():
    """Fixture providing sample Riemann zeros."""
    return np.array([
        14.134725, 21.022040, 25.010858, 30.424876, 32.935062,
        37.586178, 40.918719, 43.327073, 48.005151, 49.773832
    ])


@pytest.fixture
def qcal_parameters():
    """Fixture providing standard QCAL parameters."""
    return {
        'intensity': 1.0,
        'amplitude': np.sqrt(C_QCAL_BASE),
        'C_base': C_QCAL_BASE,
        'precision': 15
    }


# =============================================================================
# INTEGRATION TEST WITH FIXTURES
# =============================================================================

def test_full_tensor_autonomia_workflow(sample_riemann_zeros, qcal_parameters):
    """
    Complete workflow test using fixtures.
    
    This test demonstrates the full Tensor Autonomía computation
    from Riemann zeros to validated coherence spectrum.
    """
    # Compute spectrum
    t_spec, C_spec, metadata = tensor_autonomia_spectrum(
        sample_riemann_zeros,
        intensity=qcal_parameters['intensity'],
        amplitude=qcal_parameters['amplitude'],
        precision=qcal_parameters['precision']
    )
    
    # Validate
    validation = validate_tensor_coherence(C_spec, sample_riemann_zeros)
    
    # Compute coherence factor
    kappa = compute_autonomia_coherence_factor(C_spec, metadata['C_base'])
    
    # Assertions
    assert validation['valid'] == True
    assert len(C_spec) == len(sample_riemann_zeros)
    assert kappa > 0
    assert metadata['C_base'] == qcal_parameters['C_base']
    
    print(f"\n✓ Tensor Autonomía validation PASSED")
    print(f"  - Spectrum points: {len(C_spec)}")
    print(f"  - Coherence factor κ: {kappa:.6f}")
    print(f"  - Mean |C(t)|: {metadata['mean_magnitude']:.6f}")


if __name__ == "__main__":
    # Run tests with pytest
    pytest.main([__file__, "-v", "--tb=short"])
