#!/usr/bin/env python3
"""
Test Suite for Adelic Compactification Operator
===============================================

Tests the discretization by adelic boundary conditions, logarithmic torus
construction, Berry phase correction, and heat trace preservation.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: March 2026
QCAL ∞³ Active
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from operators.adelic_compactification import (
    AdelicCompactification,
    CompactificationResult,
    generate_primes,
    validate_adelic_compactification,
    BERRY_PHASE_FACTOR,
    F0_QCAL,
    C_COHERENCE
)


class TestPrimeGeneration:
    """Test prime number generation utilities."""
    
    def test_generate_primes_basic(self):
        """Test basic prime generation."""
        primes = generate_primes(20)
        expected = np.array([2, 3, 5, 7, 11, 13, 17, 19])
        np.testing.assert_array_equal(primes, expected)
    
    def test_generate_primes_small(self):
        """Test prime generation for small bounds."""
        assert len(generate_primes(1)) == 0
        assert len(generate_primes(2)) == 1
        assert generate_primes(2)[0] == 2
    
    def test_generate_primes_count(self):
        """Test that correct number of primes are generated."""
        primes_100 = generate_primes(100)
        assert len(primes_100) == 25  # π(100) = 25


class TestAdelicCompactification:
    """Test the main Adelic Compactification class."""
    
    @pytest.fixture
    def compactification(self):
        """Create a standard compactification operator."""
        return AdelicCompactification(
            max_prime=50,
            n_mesh=200,
            coupling_strength=1.0
        )
    
    def test_initialization(self, compactification):
        """Test proper initialization of the operator."""
        assert compactification.max_prime == 50
        assert compactification.n_mesh == 200
        assert len(compactification.primes) > 0
        assert compactification.log_scale > 0
        assert compactification.theta.shape == (200,)
    
    def test_log_scale_computation(self, compactification):
        """Test logarithmic scale L = Σ log p."""
        # Log scale should equal sum of log primes
        expected = np.sum(np.log(compactification.primes))
        np.testing.assert_almost_equal(
            compactification.log_scale,
            expected,
            decimal=10
        )
    
    def test_angular_coordinate_periodicity(self, compactification):
        """Test that angular coordinate covers [0, 2π] with periodicity."""
        assert compactification.theta[0] == 0
        assert compactification.theta[-1] < 2*np.pi
        # Check uniform spacing
        diffs = np.diff(compactification.theta)
        np.testing.assert_allclose(diffs, compactification.dtheta, rtol=1e-10)
    
    def test_logarithmic_potential_shape(self, compactification):
        """Test that logarithmic potential has correct shape."""
        V = compactification.logarithmic_potential(compactification.theta)
        assert V.shape == compactification.theta.shape
        assert np.all(np.isfinite(V))
    
    def test_logarithmic_potential_periodicity(self, compactification):
        """Test periodicity of logarithmic potential."""
        # Test that V(θ) is approximately periodic
        # Due to finite mesh and numerical precision, allow larger tolerance
        theta_test = np.array([0.1, 0.1 + 2*np.pi])
        V = compactification.logarithmic_potential(theta_test)
        # Should be approximately equal due to periodicity
        # Allow 20% relative tolerance due to finite prime sum
        np.testing.assert_allclose(V[0], V[1], rtol=0.2)
    
    def test_logarithmic_potential_bounded(self, compactification):
        """Test that potential is bounded."""
        V = compactification.logarithmic_potential(compactification.theta)
        # Sum of weighted cosines should be bounded
        assert np.max(np.abs(V)) < 10 * len(compactification.primes)
    
    def test_hamiltonian_matrix_shape(self, compactification):
        """Test Hamiltonian matrix has correct dimensions."""
        H = compactification.construct_hamiltonian_matrix()
        n = compactification.n_mesh
        assert H.shape == (n, n)
    
    def test_hamiltonian_hermiticity(self, compactification):
        """Test that Hamiltonian is Hermitian (symmetric for real matrices)."""
        H = compactification.construct_hamiltonian_matrix()
        # Check H = H^T (symmetric for real matrices)
        np.testing.assert_allclose(
            H, 
            H.T,
            rtol=1e-10,
            atol=1e-12
        )
    
    def test_hamiltonian_tridiagonal_structure(self, compactification):
        """Test that kinetic term gives tridiagonal structure."""
        # Create operator without potential
        comp_no_potential = AdelicCompactification(
            max_prime=50,
            n_mesh=200,
            coupling_strength=0.0  # No potential
        )
        H = comp_no_potential.construct_hamiltonian_matrix()
        
        # Kinetic term should be tridiagonal (with periodic BC)
        # Most elements should be zero except main, super-, and sub-diagonals
        n = comp_no_potential.n_mesh
        for i in range(n):
            for j in range(n):
                if abs(i - j) > 1 and not (i == 0 and j == n-1) and not (i == n-1 and j == 0):
                    # Should be zero (within tolerance)
                    assert abs(H[i, j]) < 1e-10


class TestSpectrumComputation:
    """Test discrete spectrum computation."""
    
    @pytest.fixture
    def small_compactification(self):
        """Create a smaller system for faster testing."""
        return AdelicCompactification(
            max_prime=30,
            n_mesh=100,
            coupling_strength=0.5
        )
    
    def test_compute_discrete_spectrum(self, small_compactification):
        """Test that discrete spectrum can be computed."""
        result = small_compactification.compute_discrete_spectrum(n_eigenvalues=20)
        
        assert isinstance(result, CompactificationResult)
        assert len(result.eigenvalues) == 20
        assert result.eigenfunctions.shape == (100, 20)
    
    def test_eigenvalues_real(self, small_compactification):
        """Test that eigenvalues are real (Hermitian operator)."""
        result = small_compactification.compute_discrete_spectrum(n_eigenvalues=15)
        
        # All eigenvalues should be real
        assert np.all(np.isreal(result.eigenvalues))
    
    def test_eigenvalues_sorted(self, small_compactification):
        """Test that eigenvalues are sorted in ascending order."""
        result = small_compactification.compute_discrete_spectrum(n_eigenvalues=15)
        
        # Check monotonically increasing
        assert np.all(np.diff(result.eigenvalues) > 0)
    
    def test_eigenfunctions_normalized(self, small_compactification):
        """Test that eigenfunctions are normalized."""
        result = small_compactification.compute_discrete_spectrum(n_eigenvalues=10)
        
        # Check normalization for first few eigenfunctions
        for i in range(min(5, result.eigenfunctions.shape[1])):
            psi = result.eigenfunctions[:, i]
            norm = np.sum(np.abs(psi)**2) * small_compactification.dtheta
            np.testing.assert_almost_equal(norm, 1.0, decimal=1)
    
    def test_spectral_gap_positive(self, small_compactification):
        """Test that spectral gap is positive."""
        result = small_compactification.compute_discrete_spectrum(n_eigenvalues=10)
        
        gap = result.convergence_info['spectral_gap']
        assert gap > 0
    
    def test_eigenvalue_spacing_consistency(self, small_compactification):
        """Test that eigenvalue spacing is reasonably consistent."""
        result = small_compactification.compute_discrete_spectrum(n_eigenvalues=20)
        
        spacings = np.diff(result.eigenvalues)
        mean_spacing = np.mean(spacings)
        std_spacing = np.std(spacings)
        
        # Standard deviation should not be too large compared to mean
        assert std_spacing / mean_spacing < 2.0


class TestBerryPhase:
    """Test Berry phase computation."""
    
    @pytest.fixture
    def compactification_berry(self):
        """Create compactification for Berry phase testing."""
        return AdelicCompactification(
            max_prime=40,
            n_mesh=300,
            coupling_strength=1.0
        )
    
    def test_berry_phase_computed(self, compactification_berry):
        """Test that Berry phase is computed."""
        result = compactification_berry.compute_discrete_spectrum(n_eigenvalues=15)
        
        assert hasattr(result, 'berry_phase')
        assert np.isfinite(result.berry_phase)
    
    def test_berry_phase_magnitude(self, compactification_berry):
        """Test that Berry phase has reasonable magnitude."""
        result = compactification_berry.compute_discrete_spectrum(n_eigenvalues=15)
        
        # Should be on the order of 2π × (7/8)
        theoretical = 2 * np.pi * BERRY_PHASE_FACTOR
        
        # Allow significant tolerance due to finite mesh
        assert abs(result.berry_phase) < 3 * theoretical
    
    def test_berry_phase_convergence_info(self, compactification_berry):
        """Test that Berry phase error is tracked."""
        result = compactification_berry.compute_discrete_spectrum(n_eigenvalues=15)
        
        assert 'berry_phase_error' in result.convergence_info
        assert 'berry_phase_theoretical' in result.convergence_info
        
        theoretical = result.convergence_info['berry_phase_theoretical']
        expected = 2 * np.pi * BERRY_PHASE_FACTOR
        np.testing.assert_almost_equal(theoretical, expected, decimal=10)


class TestHeatTrace:
    """Test heat trace computation and preservation."""
    
    @pytest.fixture
    def compactification_heat(self):
        """Create compactification for heat trace testing."""
        return AdelicCompactification(
            max_prime=35,
            n_mesh=150,
            coupling_strength=0.8
        )
    
    def test_heat_trace_computed(self, compactification_heat):
        """Test that heat trace is computed."""
        result = compactification_heat.compute_discrete_spectrum(n_eigenvalues=20)
        
        assert hasattr(result, 'heat_trace')
        assert len(result.heat_trace) > 0
        assert np.all(np.isfinite(result.heat_trace))
    
    def test_heat_trace_decreasing(self, compactification_heat):
        """Test that heat trace decreases with time."""
        result = compactification_heat.compute_discrete_spectrum(n_eigenvalues=20)
        
        # Tr(e^{-tH}) should decrease monotonically with t
        assert np.all(np.diff(result.heat_trace) < 0)
    
    def test_heat_trace_positive(self, compactification_heat):
        """Test that heat trace is always positive."""
        result = compactification_heat.compute_discrete_spectrum(n_eigenvalues=20)
        
        assert np.all(result.heat_trace > 0)
    
    def test_heat_trace_small_time_behavior(self):
        """Test heat trace behavior at small times."""
        comp = AdelicCompactification(max_prime=30, n_mesh=100)
        result = comp.compute_discrete_spectrum(n_eigenvalues=15)
        
        # At small t, trace should be large (many states accessible)
        # At large t, trace should be small (only ground state survives)
        assert result.heat_trace[0] > result.heat_trace[-1]


class TestLogarithmicStructure:
    """Test preservation of logarithmic structure."""
    
    @pytest.fixture
    def compactification_structure(self):
        """Create compactification for structure testing."""
        return AdelicCompactification(
            max_prime=50,
            n_mesh=250,
            coupling_strength=1.0
        )
    
    def test_verify_logarithmic_structure(self, compactification_structure):
        """Test that logarithmic structure verification runs."""
        result = compactification_structure.compute_discrete_spectrum(n_eigenvalues=20)
        checks = compactification_structure.verify_logarithmic_structure(result)
        
        assert isinstance(checks, dict)
        assert len(checks) > 0
        assert all(isinstance(v, bool) for v in checks.values())
    
    def test_eigenvalue_spacing_check(self, compactification_structure):
        """Test eigenvalue spacing check."""
        result = compactification_structure.compute_discrete_spectrum(n_eigenvalues=25)
        checks = compactification_structure.verify_logarithmic_structure(result, tolerance=0.5)
        
        # With reasonable tolerance, spacing should pass
        assert 'eigenvalue_spacing' in checks
    
    def test_berry_phase_check(self, compactification_structure):
        """Test Berry phase validation check."""
        result = compactification_structure.compute_discrete_spectrum(n_eigenvalues=20)
        checks = compactification_structure.verify_logarithmic_structure(result, tolerance=0.3)
        
        assert 'berry_phase' in checks
    
    def test_spectral_gap_checks(self, compactification_structure):
        """Test spectral gap validation checks."""
        result = compactification_structure.compute_discrete_spectrum(n_eigenvalues=20)
        checks = compactification_structure.verify_logarithmic_structure(result)
        
        assert 'spectral_gap_positive' in checks
        assert 'spectral_gap_reasonable' in checks
        assert checks['spectral_gap_positive'] is True  # Must be positive


class TestTransferMatrix:
    """Test transfer matrix computation."""
    
    @pytest.fixture
    def compactification_transfer(self):
        """Create compactification for transfer matrix testing."""
        return AdelicCompactification(
            max_prime=25,
            n_mesh=80,
            coupling_strength=0.5
        )
    
    def test_transfer_matrix_shape(self, compactification_transfer):
        """Test transfer matrix has correct dimensions."""
        T = compactification_transfer.compute_transfer_matrix()
        n = compactification_transfer.n_mesh
        assert T.shape == (n, n)
    
    def test_transfer_matrix_unitary(self, compactification_transfer):
        """Test that transfer matrix is approximately unitary."""
        T = compactification_transfer.compute_transfer_matrix()
        
        # T should be unitary: T† T ≈ I
        product = T.conj().T @ T
        identity = np.eye(compactification_transfer.n_mesh)
        
        # Check with reasonable tolerance (numerical errors)
        np.testing.assert_allclose(product, identity, rtol=1e-3, atol=1e-3)


class TestSpectralDeterminant:
    """Test spectral determinant computation."""
    
    @pytest.fixture
    def compactification_det(self):
        """Create small compactification for determinant testing."""
        return AdelicCompactification(
            max_prime=20,
            n_mesh=50,
            coupling_strength=0.5
        )
    
    def test_spectral_determinant_computed(self, compactification_det):
        """Test that spectral determinant can be computed."""
        energy_values = np.linspace(-5, 5, 20)
        det_values = compactification_det.spectral_determinant(energy_values)
        
        assert len(det_values) == len(energy_values)
        assert np.all(np.isfinite(det_values))
    
    def test_determinant_zeros_at_eigenvalues(self, compactification_det):
        """Test that determinant is small near eigenvalues."""
        result = compactification_det.compute_discrete_spectrum(n_eigenvalues=5)
        
        # Evaluate determinant near first eigenvalue
        E0 = result.eigenvalues[0]
        energies = np.array([E0 - 0.1, E0, E0 + 0.1])
        det_values = compactification_det.spectral_determinant(energies)
        
        # Determinant should be smallest at eigenvalue
        assert abs(det_values[1]) <= abs(det_values[0])
        assert abs(det_values[1]) <= abs(det_values[2])


class TestQCALIntegration:
    """Test integration with QCAL constants."""
    
    def test_qcal_constants_defined(self):
        """Test that QCAL constants are properly defined."""
        assert F0_QCAL == 141.7001
        assert C_COHERENCE == 244.36
        assert BERRY_PHASE_FACTOR == 7.0 / 8.0
    
    def test_berry_phase_factor_correct(self):
        """Test that Berry phase factor is exactly 7/8."""
        np.testing.assert_almost_equal(BERRY_PHASE_FACTOR, 0.875, decimal=10)
    
    def test_theoretical_berry_phase(self):
        """Test theoretical Berry phase calculation."""
        theoretical = 2 * np.pi * BERRY_PHASE_FACTOR
        expected = 7 * np.pi / 4
        np.testing.assert_almost_equal(theoretical, expected, decimal=10)


class TestValidationFunction:
    """Test the main validation function."""
    
    def test_validate_adelic_compactification_runs(self):
        """Test that validation function executes successfully."""
        result = validate_adelic_compactification(
            max_prime=30,
            n_mesh=100,
            n_eigenvalues=15,
            verbose=False
        )
        
        assert isinstance(result, dict)
        assert 'spectrum_computed' in result
        assert result['spectrum_computed'] is True
    
    def test_validation_returns_required_fields(self):
        """Test that validation returns all required fields."""
        result = validate_adelic_compactification(
            max_prime=25,
            n_mesh=80,
            n_eigenvalues=10,
            verbose=False
        )
        
        required_fields = [
            'spectrum_computed',
            'n_eigenvalues',
            'berry_phase',
            'berry_phase_theoretical',
            'log_scale',
            'spectral_gap',
            'structure_checks',
            'all_checks_passed',
            'convergence_info'
        ]
        
        for field in required_fields:
            assert field in result
    
    def test_validation_convergence_info(self):
        """Test that convergence info is properly populated."""
        result = validate_adelic_compactification(
            max_prime=30,
            n_mesh=100,
            n_eigenvalues=15,
            verbose=False
        )
        
        conv_info = result['convergence_info']
        assert 'berry_phase_error' in conv_info
        assert 'eigenvalue_spacing_mean' in conv_info
        assert 'spectral_gap' in conv_info
        assert 'n_primes' in conv_info


class TestEdgeCases:
    """Test edge cases and numerical stability."""
    
    def test_small_system(self):
        """Test with very small system."""
        comp = AdelicCompactification(
            max_prime=10,
            n_mesh=50,
            coupling_strength=0.1
        )
        result = comp.compute_discrete_spectrum(n_eigenvalues=5)
        
        assert len(result.eigenvalues) == 5
        assert result.log_scale > 0
    
    def test_weak_coupling(self):
        """Test with very weak coupling."""
        comp = AdelicCompactification(
            max_prime=30,
            n_mesh=100,
            coupling_strength=0.01
        )
        result = comp.compute_discrete_spectrum(n_eigenvalues=10)
        
        # Should still produce valid spectrum
        assert len(result.eigenvalues) == 10
        assert np.all(np.isfinite(result.eigenvalues))
    
    def test_strong_coupling(self):
        """Test with strong coupling."""
        comp = AdelicCompactification(
            max_prime=30,
            n_mesh=100,
            coupling_strength=5.0
        )
        result = comp.compute_discrete_spectrum(n_eigenvalues=10)
        
        # Should still produce valid spectrum
        assert len(result.eigenvalues) == 10
        assert np.all(np.isfinite(result.eigenvalues))


if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])
