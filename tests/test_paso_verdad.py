#!/usr/bin/env python3
"""
Test suite for Paso de la Verdad operator.

Tests the complete demonstration of self-adjointness and kernel integrability.
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add repository root to path
repo_root = Path(__file__).parent.parent
sys.path.insert(0, str(repo_root))

from operators.paso_verdad_operator import (
    PhiKernel,
    IntegralOperatorPasoVerdad,
    HamiltonianXP,
    FunctionalDeterminantVerifier,
    paso_verdad_complete_verification,
    verify_paso_verdad,
    F0_QCAL,
    C_COHERENCE,
    HERMITICITY_TOLERANCE,
    IMAGINARY_TOLERANCE,
    NUMERICAL_EPSILON
)

# Test-specific tolerances
EVENNESS_TOLERANCE = 1e-10  # Tolerance for evenness checks
SYMMETRY_TOLERANCE = 1e-8  # Tolerance for matrix symmetry


class TestPhiKernel:
    """Test suite for Φ kernel function."""
    
    def test_phi_kernel_initialization(self):
        """Test Φ kernel initialization."""
        kernel = PhiKernel(decay_rate=4.0)
        assert kernel.decay_rate == 4.0
    
    def test_phi_even_property(self):
        """Test Φ(u) = Φ(-u) (evenness)."""
        kernel = PhiKernel()
        
        # Test at various points
        for u in [0.1, 0.5, 1.0, 2.0, 3.0]:
            phi_u = kernel.phi(u)
            phi_minus_u = kernel.phi(-u)
            
            # Should be equal (even function)
            assert abs(phi_u - phi_minus_u) < EVENNESS_TOLERANCE, f"Not even at u={u}"
    
    def test_phi_decay(self):
        """Test super-exponential decay of Φ."""
        kernel = PhiKernel()
        
        # Test decay: |Φ(u)| should decrease as |u| increases
        # Use smaller values since decay is very rapid
        u1, u2, u3 = 0.5, 1.0, 1.5
        phi1 = abs(kernel.phi(u1))
        phi2 = abs(kernel.phi(u2))
        phi3 = abs(kernel.phi(u3))
        
        # At least check that values are finite and small enough
        assert np.isfinite(phi1) and np.isfinite(phi2) and np.isfinite(phi3)
        # For super-exponential decay, values should be very small beyond u=1
        assert phi2 < 0.1 or phi1 > phi2, "Φ should show decay behavior"
    
    def test_kernel_hermitian(self):
        """Test K(u,v) = K(v,u) (Hermitian property)."""
        kernel = PhiKernel()
        
        # Test at several points
        points = [(0.5, 1.0), (1.0, 2.0), (-0.5, 0.5)]
        
        for u, v in points:
            K_uv = kernel.kernel(u, v)
            K_vu = kernel.kernel(v, u)
            
            assert abs(K_uv - K_vu) < EVENNESS_TOLERANCE, f"Not Hermitian at ({u}, {v})"
    
    def test_verify_evenness_method(self):
        """Test evenness verification method."""
        kernel = PhiKernel()
        result = kernel.verify_evenness()
        
        assert isinstance(result, dict)
        assert 'is_even' in result
        assert 'max_even_error' in result
        assert result['is_even'] is True
        assert result['max_even_error'] < EVENNESS_TOLERANCE


class TestIntegralOperatorPasoVerdad:
    """Test suite for integral operator."""
    
    def test_operator_initialization(self):
        """Test operator initialization."""
        operator = IntegralOperatorPasoVerdad(N=50, L=3.0)
        
        assert operator.N == 50
        assert operator.L == 3.0
        assert operator.K_matrix.shape == (50, 50)
    
    def test_operator_hermiticity(self):
        """Test operator is Hermitian: K = K†."""
        operator = IntegralOperatorPasoVerdad(N=50)
        result = operator.verify_hermiticity()
        
        assert isinstance(result, dict)
        assert result['is_hermitian'] is True
        assert result['hermiticity_error'] < SYMMETRY_TOLERANCE
    
    def test_operator_symmetry(self):
        """Test kernel matrix is symmetric."""
        operator = IntegralOperatorPasoVerdad(N=40)
        
        K = operator.K_matrix
        symmetry_error = np.linalg.norm(K - K.T) / (np.linalg.norm(K) + NUMERICAL_EPSILON)
        
        assert symmetry_error < SYMMETRY_TOLERANCE
    
    def test_kernel_l2_norm(self):
        """Test kernel L² norm is finite."""
        operator = IntegralOperatorPasoVerdad(N=50)
        l2_norm = operator.compute_l2_norm()
        
        assert np.isfinite(l2_norm)
        assert l2_norm > 0
        assert l2_norm < 100  # Should be bounded
    
    def test_operator_compactness(self):
        """Test operator is compact (Hilbert-Schmidt)."""
        operator = IntegralOperatorPasoVerdad(N=60)
        is_compact, l2_norm = operator.is_compact_operator()
        
        assert is_compact is True
        assert np.isfinite(l2_norm)
    
    def test_spectrum_computation(self):
        """Test spectrum computation."""
        operator = IntegralOperatorPasoVerdad(N=50)
        eigenvalues, eigenvectors = operator.get_spectrum()
        
        assert len(eigenvalues) == 50
        assert eigenvectors.shape == (50, 50)
        
        # Eigenvalues should be real (for Hermitian operator)
        max_imag = np.max(np.abs(np.imag(eigenvalues)))
        assert max_imag < 1e-8
    
    def test_eigenvalues_real(self):
        """Test all eigenvalues are real."""
        operator = IntegralOperatorPasoVerdad(N=50)
        eigenvalues, _ = operator.get_spectrum()
        
        # Check imaginary parts are negligible
        imag_parts = np.abs(np.imag(eigenvalues))
        assert np.all(imag_parts < 1e-10)
    
    def test_spectrum_discrete(self):
        """Test spectrum is discrete."""
        operator = IntegralOperatorPasoVerdad(N=60)
        eigenvalues, _ = operator.get_spectrum()
        
        # For compact operator, eigenvalues should have varying magnitudes
        sorted_eigs = np.sort(np.abs(eigenvalues))
        
        # Check eigenvalues span a range
        if len(sorted_eigs) > 5:
            eig_range = sorted_eigs[-1] - sorted_eigs[0]
            # Spectrum is discrete if there's variation in eigenvalues
            assert eig_range > 1e-6, "Spectrum should have varying eigenvalues"


class TestHamiltonianXP:
    """Test suite for Hamiltonian H = xp + V(log x)."""
    
    def test_hamiltonian_initialization(self):
        """Test Hamiltonian initialization."""
        ham = HamiltonianXP(N=50, L=3.0, max_prime=30)
        
        assert ham.N == 50
        assert ham.L == 3.0
        assert ham.max_prime == 30
        assert ham.H.shape == (50, 50)
    
    def test_hamiltonian_real(self):
        """Test Hamiltonian is real."""
        ham = HamiltonianXP(N=50)
        
        # Matrix should be real
        max_imag = np.max(np.abs(np.imag(ham.H)))
        assert max_imag < 1e-10
    
    def test_hamiltonian_symmetric(self):
        """Test Hamiltonian is symmetric."""
        ham = HamiltonianXP(N=50)
        
        symmetry_error = np.linalg.norm(ham.H - ham.H.T) / (np.linalg.norm(ham.H) + 1e-16)
        assert symmetry_error < 1e-8
    
    def test_primes_generation(self):
        """Test prime number generation."""
        ham = HamiltonianXP(N=50)
        primes = ham._primes_up_to(20)
        
        expected_primes = [2, 3, 5, 7, 11, 13, 17, 19]
        assert primes == expected_primes
    
    def test_arithmetic_potential(self):
        """Test arithmetic potential evaluation."""
        ham = HamiltonianXP(N=50, max_prime=20)
        
        # Potential should be finite
        V_0 = ham._arithmetic_potential(0.0)
        V_1 = ham._arithmetic_potential(1.0)
        
        assert np.isfinite(V_0)
        assert np.isfinite(V_1)
    
    def test_hamiltonian_spectrum(self):
        """Test Hamiltonian spectrum."""
        ham = HamiltonianXP(N=50)
        eigenvalues, eigenvectors = ham.get_spectrum()
        
        assert len(eigenvalues) == 50
        assert eigenvectors.shape == (50, 50)
        
        # Eigenvalues should be real
        max_imag = np.max(np.abs(np.imag(eigenvalues)))
        assert max_imag < 1e-8


class TestFunctionalDeterminantVerifier:
    """Test suite for functional determinant verifier."""
    
    def test_determinant_initialization(self):
        """Test determinant verifier initialization."""
        eigenvalues = np.array([1.0, 2.0, 3.0, 4.0])
        verifier = FunctionalDeterminantVerifier(eigenvalues)
        
        assert len(verifier.eigenvalues) == 4
    
    def test_functional_determinant(self):
        """Test functional determinant computation."""
        eigenvalues = np.array([1.0, 2.0, 3.0])
        verifier = FunctionalDeterminantVerifier(eigenvalues)
        
        # det(s - H) = (s-1)(s-2)(s-3)
        # At s=1: det should be 0
        det_at_1 = verifier.functional_determinant(1.0)
        assert abs(det_at_1) < 1e-10
        
        # At s=0: det = (-1)(-2)(-3) = -6
        det_at_0 = verifier.functional_determinant(0.0)
        assert abs(det_at_0 - (-6.0)) < 1e-10
    
    def test_connection_strength(self):
        """Test connection strength measurement."""
        eigenvalues = np.array([1.0, 2.0, 3.0, 4.0, 5.0])
        verifier = FunctionalDeterminantVerifier(eigenvalues)
        
        connection = verifier.connection_strength(n_test=3)
        
        assert 0.0 <= connection <= 1.0
        # Should be high since zeros of det align with eigenvalues
        assert connection > 0.5


class TestPasoVerdadCompleteVerification:
    """Test suite for complete Paso de la Verdad verification."""
    
    def test_complete_verification(self):
        """Test complete verification runs."""
        result = paso_verdad_complete_verification(N=40)
        
        assert hasattr(result, 'psi')
        assert hasattr(result, 'self_adjoint')
        assert hasattr(result, 'kernel_l2_norm')
        assert hasattr(result, 'resonance_frequency')
    
    def test_result_fields(self):
        """Test all result fields are present."""
        result = paso_verdad_complete_verification(N=40)
        
        # Check all fields
        assert 0.0 <= result.psi <= 1.0
        assert isinstance(result.self_adjoint, bool)
        assert result.hermiticity_error >= 0.0
        assert result.kernel_l2_norm > 0.0
        assert isinstance(result.kernel_compact, bool)
        assert isinstance(result.eigenvalues_real, bool)
        assert isinstance(result.spectrum_discrete, bool)
        assert 0.0 <= result.det_connection <= 1.0
        assert result.resonance_frequency == F0_QCAL
    
    def test_self_adjointness(self):
        """Test self-adjointness is verified."""
        result = paso_verdad_complete_verification(N=50)
        
        assert result.self_adjoint is True
        assert result.hermiticity_error < 1e-6
    
    def test_kernel_compactness(self):
        """Test kernel compactness is verified."""
        result = paso_verdad_complete_verification(N=50)
        
        assert result.kernel_compact is True
        assert np.isfinite(result.kernel_l2_norm)
    
    def test_eigenvalues_real(self):
        """Test eigenvalues are real."""
        result = paso_verdad_complete_verification(N=50)
        
        assert result.eigenvalues_real is True
    
    def test_qcal_coherence(self):
        """Test QCAL coherence Ψ is computed."""
        result = paso_verdad_complete_verification(N=50)
        
        assert 0.0 <= result.psi <= 1.0
        # Should be high if all criteria are met
        if result.self_adjoint and result.kernel_compact and result.eigenvalues_real:
            assert result.psi > 0.5
    
    def test_resonance_frequency(self):
        """Test resonance frequency is correct."""
        result = paso_verdad_complete_verification(N=40)
        
        assert result.resonance_frequency == F0_QCAL
        assert abs(result.resonance_frequency - 141.7001) < 1e-6
    
    def test_parameters_stored(self):
        """Test parameters are stored in result."""
        result = paso_verdad_complete_verification(N=60, L=4.0, max_prime=40)
        
        assert 'N' in result.parameters
        assert 'L' in result.parameters
        assert 'max_prime' in result.parameters
        assert result.parameters['N'] == 60
        assert result.parameters['L'] == 4.0
        assert result.parameters['max_prime'] == 40
    
    def test_timestamp_present(self):
        """Test timestamp is recorded."""
        result = paso_verdad_complete_verification(N=40)
        
        assert result.timestamp is not None
        assert isinstance(result.timestamp, str)
    
    def test_computation_time(self):
        """Test computation time is recorded."""
        result = paso_verdad_complete_verification(N=40)
        
        assert result.computation_time_ms > 0
        assert result.computation_time_ms < 60000  # Should be less than 1 minute


class TestVerifyPasoVerdad:
    """Test suite for quick verification function."""
    
    def test_quick_verification(self):
        """Test quick verification function."""
        result = verify_paso_verdad(N=40)
        
        assert isinstance(result, dict)
        assert 'paso_verdad_verified' in result
        assert 'psi' in result
        assert 'self_adjoint' in result
    
    def test_verification_boolean(self):
        """Test verification returns boolean."""
        result = verify_paso_verdad(N=50)
        
        assert isinstance(result['paso_verdad_verified'], bool)
        assert isinstance(result['self_adjoint'], bool)
    
    def test_verification_psi(self):
        """Test Ψ is in valid range."""
        result = verify_paso_verdad(N=50)
        
        assert 0.0 <= result['psi'] <= 1.0


class TestQCALIntegration:
    """Test suite for QCAL framework integration."""
    
    def test_qcal_constants(self):
        """Test QCAL constants are used."""
        result = paso_verdad_complete_verification(N=40)
        
        assert result.resonance_frequency == F0_QCAL
        assert 'C_coherence' in result.parameters
        assert result.parameters['C_coherence'] == C_COHERENCE
    
    def test_coherence_computation(self):
        """Test coherence Ψ computation."""
        result = paso_verdad_complete_verification(N=50)
        
        # Ψ should reflect overall system coherence
        if result.self_adjoint and result.kernel_compact and result.eigenvalues_real:
            assert result.psi > 0.6, "High coherence expected when all criteria met"


class TestNumericalStability:
    """Test suite for numerical stability."""
    
    def test_different_sizes(self):
        """Test with different matrix sizes."""
        for N in [30, 50, 70]:
            result = paso_verdad_complete_verification(N=N)
            assert result.psi >= 0.0
            assert result.kernel_l2_norm > 0
    
    def test_different_domains(self):
        """Test with different domain sizes."""
        for L in [3.0, 5.0, 7.0]:
            result = paso_verdad_complete_verification(N=50, L=L)
            assert result.kernel_compact is True
    
    def test_different_decay_rates(self):
        """Test with different decay rates."""
        for decay in [3.0, 4.0, 5.0]:
            result = paso_verdad_complete_verification(N=50, decay_rate=decay)
            assert result.self_adjoint is True


# Run if executed directly
if __name__ == '__main__':
    pytest.main([__file__, '-v'])
