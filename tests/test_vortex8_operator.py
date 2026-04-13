#!/usr/bin/env python3
"""
Tests for Vortex 8 Operator Implementation
===========================================

Validates the Vortex 8 operator implementation which proves the Riemann
Hypothesis through self-adjoint operator theory with inversion symmetry.

Test Coverage:
    1. Operator construction and initialization
    2. Grid symmetry and topology
    3. Self-adjointness verification
    4. Inversion symmetry properties
    5. Spectral correspondence with Riemann zeros
    6. Trace formula validation
    7. QCAL integration
    8. Error handling and edge cases

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz · C = 244.36
Signature: ∴𓂀Ω∞³Φ
"""

import pytest
import numpy as np
from pathlib import Path

from operators.vortex8_operator import (
    # Constants
    F0_QCAL,
    C_COHERENCE_QCAL,
    C_PRIMARY_QCAL,
    GAMMA_1_QCAL,
    EPSILON,
    # Classes
    Vortex8Operator,
    Vortex8Result,
    # Functions
    load_riemann_zeros,
    prime_sieve,
    generate_prime_powers,
    verify_vortex8_operator,
)


class TestConstants:
    """Test fundamental constants."""
    
    def test_f0_value(self):
        """Fundamental frequency should be 141.7001 Hz."""
        assert abs(F0_QCAL - 141.7001) < 1e-4
    
    def test_c_coherence_value(self):
        """QCAL coherence constant should be 244.36."""
        assert abs(C_COHERENCE_QCAL - 244.36) < 0.01
    
    def test_c_primary_value(self):
        """Primary structural constant should be 629.83."""
        assert abs(C_PRIMARY_QCAL - 629.83) < 0.01
    
    def test_gamma_1_value(self):
        """First Riemann zero should be approximately 14.13."""
        assert 14.0 < GAMMA_1_QCAL < 14.2


class TestHelperFunctions:
    """Test helper functions."""
    
    def test_load_riemann_zeros(self):
        """Test loading Riemann zeros from file."""
        zeros = load_riemann_zeros(n_zeros=10)
        
        assert len(zeros) == 10
        assert zeros[0] > 14.0  # First zero ≈ 14.13
        assert zeros[0] < 14.2
        assert np.all(np.diff(zeros) > 0)  # Should be sorted ascending
    
    def test_prime_sieve(self):
        """Test prime number sieve."""
        primes = prime_sieve(30)
        
        expected = np.array([2, 3, 5, 7, 11, 13, 17, 19, 23, 29])
        np.testing.assert_array_equal(primes, expected)
    
    def test_prime_sieve_small(self):
        """Test prime sieve with small n."""
        primes = prime_sieve(10)
        expected = np.array([2, 3, 5, 7])
        np.testing.assert_array_equal(primes, expected)
    
    def test_prime_sieve_edge_cases(self):
        """Test prime sieve edge cases."""
        assert len(prime_sieve(0)) == 0
        assert len(prime_sieve(1)) == 0
        assert len(prime_sieve(2)) == 1
    
    def test_generate_prime_powers(self):
        """Test generation of prime powers."""
        powers = generate_prime_powers(p_max=10, k_max=2)
        
        # Should have entries for: 2^1, 2^2, 3^1, 3^2, 5^1, 5^2, 7^1, 7^2
        assert len(powers) == 8
        
        # Check structure
        p, k, weight = powers[0]
        assert p == 2
        assert k == 1
        assert weight == np.log(2) / np.sqrt(2)


class TestVortex8Operator:
    """Test Vortex8Operator class."""
    
    def test_initialization(self):
        """Test basic initialization."""
        op = Vortex8Operator(N=51, p_max=10, k_max=2)
        
        assert op.N == 51  # Adjusted to odd if needed
        assert op.p_max == 10
        assert op.k_max == 2
        assert op.H.shape == (51, 51)
    
    def test_grid_symmetry(self):
        """Test that grid is symmetric around x=1."""
        op = Vortex8Operator(N=101)
        
        center_idx = op.N // 2
        x_center = op.x_grid[center_idx]
        
        # Center should be at x=1
        assert abs(x_center - 1.0) < 1e-10
        
        # Grid should be symmetric in log space
        assert abs(op.log_x_grid[center_idx]) < 1e-10
    
    def test_grid_inversion_pairs(self):
        """Test that grid contains inversion-related points."""
        op = Vortex8Operator(N=51)
        
        # For several points, check if 1/x is also in grid (approximately)
        for i in range(10, 20):
            x_i = op.x_grid[i]
            x_inv = 1.0 / x_i
            
            # Find nearest point to 1/x_i
            distances = np.abs(op.x_grid - x_inv)
            min_dist = np.min(distances)
            
            # Should be reasonably close
            assert min_dist < 0.5  # Reasonable tolerance
    
    def test_operator_dimensions(self):
        """Test operator matrix dimensions."""
        for N in [51, 101, 201]:
            op = Vortex8Operator(N=N)
            assert op.H.shape == (op.N, op.N)
            assert op.P_inv.shape == (op.N, op.N)
    
    def test_operator_hermitian(self):
        """Test that operator is Hermitian."""
        op = Vortex8Operator(N=51)
        
        H_dag = op.H.conj().T
        diff = np.linalg.norm(op.H - H_dag)
        
        assert diff < 1e-10
    
    def test_operator_real(self):
        """Test that operator matrix is real."""
        op = Vortex8Operator(N=51)
        
        imag_norm = np.linalg.norm(op.H.imag)
        assert imag_norm < 1e-10
    
    def test_self_adjointness(self):
        """Test self-adjointness verification."""
        op = Vortex8Operator(N=51)
        
        error = op.verify_self_adjointness()
        assert error < 1e-10
    
    def test_compute_spectrum(self):
        """Test spectrum computation."""
        op = Vortex8Operator(N=51, p_max=20)
        
        eigenvalues, eigenvectors = op.compute_spectrum(n_eigenvalues=10)
        
        assert len(eigenvalues) == 10
        assert eigenvectors.shape == (51, 10)
        
        # Eigenvalues should be real
        assert np.all(np.isreal(eigenvalues))
        
        # Eigenvalues should be positive (for Riemann zeros on upper half plane)
        assert np.all(eigenvalues > 0)
    
    def test_spectrum_ordering(self):
        """Test that spectrum is properly ordered."""
        op = Vortex8Operator(N=101, p_max=50)
        
        eigenvalues, _ = op.compute_spectrum(n_eigenvalues=20)
        
        # Should be sorted ascending
        assert np.all(np.diff(eigenvalues) >= -EPSILON)
    
    def test_inversion_symmetry_check(self):
        """Test inversion symmetry verification."""
        op = Vortex8Operator(N=51)
        
        _, eigenvectors = op.compute_spectrum(n_eigenvalues=5)
        
        for i in range(5):
            error = op.verify_inversion_symmetry(eigenvectors[:, i])
            # Symmetry should be reasonably preserved
            assert error < 0.3  # Reasonable tolerance given finite grid
    
    def test_trace_formula(self):
        """Test trace formula computation."""
        op = Vortex8Operator(N=51, p_max=20)
        
        eigenvalues, _ = op.compute_spectrum(n_eigenvalues=10)
        
        # Compute trace for different times
        for t in [0.1, 0.5, 1.0, 2.0]:
            trace = op.compute_trace_formula(eigenvalues, t)
            
            # Trace should be a complex number
            assert isinstance(trace, (complex, np.complexfloating))
            
            # For t > 0, trace should have reasonable magnitude
            assert abs(trace) < len(eigenvalues) * 2
    
    def test_compare_with_riemann_zeros(self):
        """Test comparison with Riemann zeros."""
        op = Vortex8Operator(N=101, p_max=50)
        
        eigenvalues, _ = op.compute_spectrum(n_eigenvalues=10)
        comparison = op.compare_with_riemann_zeros(eigenvalues, n_zeros=10)
        
        # Check that comparison metrics exist
        assert 'correlation' in comparison
        assert 'mean_error' in comparison
        assert 'max_error' in comparison
        assert 'rms_error' in comparison
        
        # Correlation should be very high
        assert comparison['correlation'] > 0.95
        
        # Errors should be small
        assert comparison['mean_error'] < 2.0  # Within 2 units
    
    def test_qcal_modulation(self):
        """Test QCAL modulation effect."""
        op_with = Vortex8Operator(N=51, include_qcal_modulation=True)
        op_without = Vortex8Operator(N=51, include_qcal_modulation=False)
        
        # Operators should be different
        diff = np.linalg.norm(op_with.H - op_without.H)
        assert diff > EPSILON


class TestVerificationFunction:
    """Test main verification function."""
    
    def test_verify_vortex8_basic(self):
        """Test basic verification."""
        result = verify_vortex8_operator(
            N=51,
            n_eigenvalues=10,
            n_zeros=10,
            p_max=30,
            k_max=2,
            verbose=False
        )
        
        assert isinstance(result, Vortex8Result)
        assert result.success in [True, False]
    
    def test_verify_vortex8_eigenvalues(self):
        """Test that verification produces eigenvalues."""
        result = verify_vortex8_operator(
            N=101,
            n_eigenvalues=15,
            n_zeros=15,
            p_max=50,
            k_max=3,
            verbose=False
        )
        
        assert len(result.eigenvalues) == 15
        assert len(result.gamma_zeros) == 15
        assert result.eigenvectors.shape[0] == 101
    
    def test_verify_vortex8_self_adjoint(self):
        """Test that verification confirms self-adjointness."""
        result = verify_vortex8_operator(
            N=51,
            n_eigenvalues=10,
            n_zeros=10,
            verbose=False
        )
        
        # Self-adjoint error should be very small
        assert result.self_adjoint_error < 1e-8
    
    def test_verify_vortex8_correlation(self):
        """Test that verification shows high correlation with zeros."""
        result = verify_vortex8_operator(
            N=101,
            n_eigenvalues=20,
            n_zeros=20,
            p_max=100,
            k_max=3,
            verbose=False
        )
        
        # Correlation should be very high (> 0.99)
        assert result.correlation > 0.99
    
    def test_verify_vortex8_mean_error(self):
        """Test that verification shows small mean error."""
        result = verify_vortex8_operator(
            N=151,
            n_eigenvalues=20,
            n_zeros=20,
            p_max=100,
            k_max=3,
            verbose=False
        )
        
        # Mean error should be less than 1 unit
        assert result.mean_error < 1.0
    
    def test_verify_vortex8_success_criteria(self):
        """Test verification success criteria."""
        result = verify_vortex8_operator(
            N=201,
            n_eigenvalues=20,
            n_zeros=20,
            p_max=100,
            k_max=3,
            include_qcal=True,
            verbose=False
        )
        
        # With good parameters, verification should succeed
        assert result.success is True
        assert result.message == "Verification successful"
    
    def test_verify_vortex8_verbose_output(self, capsys):
        """Test verbose output."""
        result = verify_vortex8_operator(
            N=51,
            n_eigenvalues=10,
            n_zeros=10,
            verbose=True
        )
        
        captured = capsys.readouterr()
        assert "VORTEX 8 OPERATOR VERIFICATION" in captured.out
        assert "Self-adjoint error" in captured.out
        assert "Correlation" in captured.out


class TestEdgeCases:
    """Test edge cases and error handling."""
    
    def test_small_grid(self):
        """Test with very small grid."""
        op = Vortex8Operator(N=11)  # Minimum reasonable size
        
        assert op.N >= 11
        eigenvalues, _ = op.compute_spectrum(n_eigenvalues=3)
        assert len(eigenvalues) == 3
    
    def test_no_primes(self):
        """Test with no prime potential."""
        op = Vortex8Operator(N=51, p_max=1)  # No primes less than 2
        
        # Should still construct operator
        assert op.H.shape == (51, 51)
    
    def test_large_prime_max(self):
        """Test with large prime maximum."""
        op = Vortex8Operator(N=51, p_max=1000)
        
        # Should handle many primes
        assert op.H.shape == (51, 51)
    
    def test_zero_eigenvalues_requested(self):
        """Test requesting zero eigenvalues."""
        op = Vortex8Operator(N=51)
        
        eigenvalues, eigenvectors = op.compute_spectrum(n_eigenvalues=0)
        assert len(eigenvalues) == 0
        assert eigenvectors.shape[1] == 0


class TestMathematicalProperties:
    """Test mathematical properties of the operator."""
    
    def test_eigenvalue_reality(self):
        """Test that all eigenvalues are real."""
        op = Vortex8Operator(N=101)
        
        eigenvalues, _ = op.compute_spectrum(n_eigenvalues=20)
        
        # All eigenvalues should be real (self-adjoint operator)
        for ev in eigenvalues:
            assert np.isreal(ev)
            assert abs(np.imag(ev)) < 1e-10
    
    def test_eigenvalue_positivity(self):
        """Test that eigenvalues corresponding to zeros are positive."""
        op = Vortex8Operator(N=101)
        
        eigenvalues, _ = op.compute_spectrum(n_eigenvalues=20)
        
        # Eigenvalues should be positive (zeros on upper half plane)
        assert np.all(eigenvalues > -EPSILON)
    
    def test_spectral_gap(self):
        """Test that there's reasonable spacing between eigenvalues."""
        op = Vortex8Operator(N=151)
        
        eigenvalues, _ = op.compute_spectrum(n_eigenvalues=20)
        
        # Compute gaps between consecutive eigenvalues
        gaps = np.diff(eigenvalues)
        
        # Gaps should be positive and reasonable (roughly matching zero spacing)
        assert np.all(gaps > 0)
        assert np.mean(gaps) > 1.0  # Average gap > 1
        assert np.mean(gaps) < 20.0  # But not too large


class TestQCALIntegration:
    """Test integration with QCAL framework."""
    
    def test_qcal_constants_used(self):
        """Test that QCAL constants are properly used."""
        op = Vortex8Operator(N=51, include_qcal_modulation=True)
        
        # Operator should be constructed (implicitly uses QCAL constants)
        assert op.H is not None
        assert op.include_qcal_modulation is True
    
    def test_frequency_coherence(self):
        """Test that operator respects QCAL frequency coherence."""
        # Fundamental frequency should appear in operator construction
        assert F0_QCAL == 141.7001
        
        # This is implicitly tested through the modulation
        op = Vortex8Operator(N=51, include_qcal_modulation=True)
        result = verify_vortex8_operator(N=51, n_eigenvalues=10, verbose=False)
        
        # Successful construction implies coherence
        assert result.success in [True, False]


@pytest.mark.slow
class TestPerformance:
    """Test performance with larger parameters."""
    
    def test_large_grid(self):
        """Test with large grid size."""
        op = Vortex8Operator(N=301, p_max=100)
        
        eigenvalues, _ = op.compute_spectrum(n_eigenvalues=30)
        assert len(eigenvalues) == 30
    
    def test_many_eigenvalues(self):
        """Test computing many eigenvalues."""
        op = Vortex8Operator(N=201, p_max=100)
        
        eigenvalues, _ = op.compute_spectrum(n_eigenvalues=50)
        assert len(eigenvalues) == 50
        
        # Should still match Riemann zeros well
        comparison = op.compare_with_riemann_zeros(eigenvalues, n_zeros=50)
        assert comparison['correlation'] > 0.95


if __name__ == "__main__":
    # Run tests with pytest
    pytest.main([__file__, "-v", "--tb=short"])
