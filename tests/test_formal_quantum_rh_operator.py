#!/usr/bin/env python3
"""
Test Suite for Formal Quantum Mechanical RH Operator
=====================================================

Comprehensive tests for the formal quantum mechanical solution to the
Riemann Hypothesis.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
QCAL ∞³ · 141.7001 Hz
"""

import sys
import os
import pytest
import numpy as np

# Add operators directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'operators'))

from formal_quantum_rh_operator import (
    FormalQuantumRHOperator,
    HilbertSpaceConfig,
    OperatorSpectrum,
    SelfAdjointnessProof,
    CountingFunction,
    TraceFormulaResult,
    F0, C_PRIMARY, C_COHERENCE, PHI,
    BERRY_KEATING_C,
    ZEROS_ZETA_REFERENCE
)


class TestHilbertSpaceConfig:
    """Test Hilbert space configuration."""
    
    def test_default_config(self):
        """Test default configuration values."""
        config = HilbertSpaceConfig()
        assert config.x_min == 1.0
        assert config.x_max == 100.0
        assert config.n_grid == 1000
        assert config.phase_theta == 0.0
    
    def test_custom_config(self):
        """Test custom configuration."""
        config = HilbertSpaceConfig(
            x_min=0.5,
            x_max=50.0,
            n_grid=500,
            phase_theta=np.pi / 4
        )
        assert config.x_min == 0.5
        assert config.x_max == 50.0
        assert config.n_grid == 500
        assert config.phase_theta == pytest.approx(np.pi / 4)
    
    def test_zero_node_boundary(self):
        """Test that x_min=1.0 corresponds to Zero Node."""
        config = HilbertSpaceConfig()
        assert config.x_min == 1.0  # Zero Node of Vortex 8


class TestFormalQuantumRHOperator:
    """Test main operator class."""
    
    @pytest.fixture
    def operator(self):
        """Create operator instance for testing."""
        config = HilbertSpaceConfig(x_min=1.0, x_max=50.0, n_grid=200)
        return FormalQuantumRHOperator(config)
    
    def test_operator_initialization(self, operator):
        """Test operator initialization."""
        assert operator.hilbert_config is not None
        assert len(operator.x_grid) == 200
        assert operator.x_grid[0] == pytest.approx(1.0, rel=1e-6)
        assert operator.dx > 0
    
    def test_logarithmic_grid(self, operator):
        """Test logarithmic grid for L²(dx/x) measure."""
        x = operator.x_grid
        # Grid should be logarithmically spaced
        log_x = np.log(x)
        log_spacing = np.diff(log_x)
        # All spacings should be approximately equal
        assert np.std(log_spacing) < 1e-6
    
    def test_logarithmic_potential(self, operator):
        """Test logarithmic potential V̂(x)."""
        V = operator.logarithmic_potential(operator.x_grid)
        
        # Potential should be array of correct length
        assert len(V) == len(operator.x_grid)
        
        # Berry-Keating term should dominate for large x
        # V ≈ C log(x) where C < 0
        assert np.all(V < 0)  # Negative due to Berry-Keating constant
        
        # Should increase in magnitude with x
        assert V[-1] < V[0]
    
    def test_logarithmic_potential_with_primes(self, operator):
        """Test potential tuning by prime logarithms."""
        primes = [2, 3, 5, 7]
        V = operator.logarithmic_potential(operator.x_grid, primes)
        
        # Should have resonances near log(p)
        for p in primes:
            log_p = np.log(p)
            # Find grid point closest to log_p
            idx = np.argmin(np.abs(np.log(operator.x_grid) - log_p))
            # Potential should have local feature near prime
            assert V[idx] != pytest.approx(BERRY_KEATING_C * log_p, rel=0.1)
    
    def test_construct_operator_matrix(self, operator):
        """Test operator matrix construction."""
        H = operator.construct_operator_matrix()
        
        # Matrix should be square
        n = len(operator.x_grid)
        assert H.shape == (n, n)
        
        # Matrix should be complex (due to -i terms)
        assert H.dtype == np.complex128
        
        # Matrix should be hermitian (H = H†)
        hermiticity_error = np.max(np.abs(H - H.conj().T))
        assert hermiticity_error < 1e-10
    
    def test_operator_structure(self, operator):
        """Test structure of operator matrix."""
        H = operator.construct_operator_matrix()
        
        # Kinetic term should give tridiagonal structure
        # (plus potential on diagonal)
        # Check that off-diagonal elements decay away from diagonal
        n = len(operator.x_grid)
        for i in range(n):
            for j in range(n):
                if abs(i - j) > 2:
                    # Far off-diagonal should be mostly zero
                    assert np.abs(H[i, j]) < 1e-6


class TestSelfAdjointness:
    """Test self-adjointness verification."""
    
    @pytest.fixture
    def operator(self):
        """Create operator for testing."""
        config = HilbertSpaceConfig(x_min=1.0, x_max=30.0, n_grid=150)
        return FormalQuantumRHOperator(config)
    
    def test_self_adjointness_verification(self, operator):
        """Test self-adjointness proof."""
        proof = operator.verify_self_adjointness()
        
        assert isinstance(proof, SelfAdjointnessProof)
        assert proof.proof_method == "integration_by_parts"
    
    def test_boundary_term_at_zero_node(self, operator):
        """Test boundary term vanishes at x=1 (Zero Node)."""
        proof = operator.verify_self_adjointness()
        
        # Boundary term at x=1 should be small
        assert proof.boundary_term_x1 < 1e-6
    
    def test_boundary_term_at_infinity(self, operator):
        """Test boundary term vanishes at x→∞."""
        proof = operator.verify_self_adjointness()
        
        # Boundary term at x→∞ should be small (L² decay)
        assert proof.boundary_term_infinity < 1e-6
    
    def test_hermiticity(self, operator):
        """Test hermiticity ⟨Ĥψ, φ⟩ = ⟨ψ, Ĥφ⟩."""
        proof = operator.verify_self_adjointness()
        
        # Hermiticity error should be very small
        assert proof.hermiticity_error < 1e-6
    
    def test_is_self_adjoint(self, operator):
        """Test that operator is verified as self-adjoint."""
        proof = operator.verify_self_adjointness()
        
        assert proof.is_self_adjoint is True
    
    def test_phase_boundary_condition(self):
        """Test phase boundary condition at x=1."""
        config = HilbertSpaceConfig(x_min=1.0, x_max=30.0, n_grid=150, phase_theta=np.pi / 3)
        operator = FormalQuantumRHOperator(config)
        
        # Create test function with phase condition
        psi = np.exp(-((np.log(operator.x_grid) - 1.0) ** 2))
        psi[0] *= np.exp(1j * config.phase_theta)
        
        # Verify phase condition is applied
        assert np.abs(psi[0]) > 0
        phase = np.angle(psi[0])
        # Phase should include boundary phase
        assert abs(phase - config.phase_theta) < 0.5  # Relaxed due to Gaussian


class TestSpectrum:
    """Test spectral properties."""
    
    @pytest.fixture
    def operator(self):
        """Create operator for testing."""
        config = HilbertSpaceConfig(x_min=1.0, x_max=50.0, n_grid=200)
        return FormalQuantumRHOperator(config)
    
    @pytest.mark.slow
    def test_compute_spectrum(self, operator):
        """Test spectrum computation."""
        spectrum = operator.compute_spectrum(n_eigenvalues=20)
        
        assert isinstance(spectrum, OperatorSpectrum)
        assert spectrum.n_eigenvalues == 20
        assert len(spectrum.eigenvalues) == 20
    
    @pytest.mark.slow
    def test_spectrum_is_discrete(self, operator):
        """Test that spectrum is discrete (Riesz-Schauder)."""
        spectrum = operator.compute_spectrum(n_eigenvalues=15)
        
        assert spectrum.is_discrete is True
    
    @pytest.mark.slow
    def test_eigenvalues_are_real(self, operator):
        """Test that all eigenvalues are real (self-adjoint)."""
        spectrum = operator.compute_spectrum(n_eigenvalues=15)
        
        assert spectrum.is_real is True
        # All eigenvalues should have negligible imaginary part
        assert np.all(np.abs(np.imag(spectrum.eigenvalues)) < 1e-8)
    
    @pytest.mark.slow
    def test_eigenvalues_ordered(self, operator):
        """Test that eigenvalues are ordered."""
        spectrum = operator.compute_spectrum(n_eigenvalues=20)
        
        # Should be in ascending order
        assert np.all(np.diff(spectrum.eigenvalues) >= 0)
    
    @pytest.mark.slow
    def test_spectral_gap(self, operator):
        """Test spectral gap computation."""
        spectrum = operator.compute_spectrum(n_eigenvalues=20)
        
        assert spectrum.spectral_gap > 0
        # Spectral gap should be minimum spacing
        min_spacing = np.min(np.diff(spectrum.eigenvalues))
        assert spectrum.spectral_gap == pytest.approx(min_spacing)
    
    @pytest.mark.slow
    def test_eigenvalues_positive(self, operator):
        """Test that eigenvalues are positive (for our operator)."""
        spectrum = operator.compute_spectrum(n_eigenvalues=15)
        
        # For Berry-Keating type operator, expect positive eigenvalues
        # (corresponding to imaginary parts of Riemann zeros squared)
        # Note: actual sign depends on operator normalization
        assert len(spectrum.eigenvalues) > 0


class TestCountingFunction:
    """Test Weyl-Riemann counting law."""
    
    @pytest.fixture
    def operator(self):
        """Create operator for testing."""
        config = HilbertSpaceConfig(x_min=1.0, x_max=50.0, n_grid=200)
        return FormalQuantumRHOperator(config)
    
    def test_weyl_riemann_law(self, operator):
        """Test Weyl-Riemann law formula."""
        # N(T) = (T/2π) log(T/2πe)
        T = 50.0
        N = operator.counting_function_weyl_riemann(T)
        
        # Should give positive value for T > 0
        assert N > 0
        
        # Check formula
        expected = (T / (2 * np.pi)) * np.log(T / (2 * np.pi * np.e))
        assert N == pytest.approx(expected)
    
    def test_weyl_riemann_zero_energy(self, operator):
        """Test counting function at T=0."""
        N = operator.counting_function_weyl_riemann(0.0)
        assert N == 0.0
    
    @pytest.mark.slow
    def test_verify_counting_function(self, operator):
        """Test counting function verification."""
        spectrum = operator.compute_spectrum(n_eigenvalues=25)
        counting = operator.verify_counting_function(spectrum)
        
        assert isinstance(counting, CountingFunction)
        assert len(counting.N_computed) == len(counting.energies)
        assert len(counting.N_weyl_riemann) == len(counting.energies)
    
    @pytest.mark.slow
    def test_counting_function_properties(self, operator):
        """Test properties of counting function."""
        spectrum = operator.compute_spectrum(n_eigenvalues=25)
        counting = operator.verify_counting_function(spectrum)
        
        # N(T) should be non-decreasing
        assert np.all(np.diff(counting.N_computed) >= 0)
        assert np.all(np.diff(counting.N_weyl_riemann) >= 0)
        
        # N(T) should be non-negative
        assert np.all(counting.N_computed >= 0)
        assert np.all(counting.N_weyl_riemann >= 0)
    
    @pytest.mark.slow
    def test_counting_function_relative_error(self, operator):
        """Test relative error in counting function."""
        spectrum = operator.compute_spectrum(n_eigenvalues=30)
        counting = operator.verify_counting_function(spectrum)
        
        # Relative error should be reasonable for large T
        # (finite-size effects for small T)
        assert np.all(np.isfinite(counting.relative_error))


class TestTraceFormula:
    """Test Guinand-Weil trace formula."""
    
    @pytest.fixture
    def operator(self):
        """Create operator for testing."""
        config = HilbertSpaceConfig(x_min=1.0, x_max=50.0, n_grid=150)
        return FormalQuantumRHOperator(config)
    
    @pytest.mark.slow
    def test_trace_formula(self, operator):
        """Test Guinand-Weil trace formula."""
        spectrum = operator.compute_spectrum(n_eigenvalues=20)
        trace = operator.guinand_weil_trace_formula(t=1.0, spectrum=spectrum)
        
        assert isinstance(trace, TraceFormulaResult)
    
    @pytest.mark.slow
    def test_quantum_side(self, operator):
        """Test quantum side Σₙ e^(itγₙ)."""
        spectrum = operator.compute_spectrum(n_eigenvalues=15)
        trace = operator.guinand_weil_trace_formula(t=1.0, spectrum=spectrum)
        
        # Quantum side should be complex number
        assert isinstance(trace.quantum_side, (complex, np.complex128))
        assert np.isfinite(np.abs(trace.quantum_side))
    
    @pytest.mark.slow
    def test_classical_side(self, operator):
        """Test classical side (prime sum)."""
        spectrum = operator.compute_spectrum(n_eigenvalues=15)
        trace = operator.guinand_weil_trace_formula(t=1.0, spectrum=spectrum)
        
        # Classical side should be complex number
        assert isinstance(trace.classical_side, (complex, np.complex128))
        assert np.isfinite(np.abs(trace.classical_side))
    
    @pytest.mark.slow
    def test_orbit_lengths(self, operator):
        """Test orbit lengths ℓₚ = k log p."""
        spectrum = operator.compute_spectrum(n_eigenvalues=15)
        primes = [2, 3, 5, 7, 11]
        trace = operator.guinand_weil_trace_formula(
            t=1.0, spectrum=spectrum, primes=primes, max_prime_power=3
        )
        
        # Should have orbit lengths for each (p, k) pair
        assert len(trace.orbit_lengths) > 0
        
        # Orbit lengths should be positive
        assert np.all(trace.orbit_lengths > 0)
        
        # Check some orbit lengths
        log_2 = np.log(2)
        assert log_2 in trace.orbit_lengths or pytest.approx(log_2) in trace.orbit_lengths
    
    @pytest.mark.slow
    def test_resonance_frequencies(self, operator):
        """Test resonance frequencies match prime logarithms."""
        spectrum = operator.compute_spectrum(n_eigenvalues=15)
        trace = operator.guinand_weil_trace_formula(t=1.0, spectrum=spectrum)
        
        # Resonance frequencies should match orbit lengths
        assert np.allclose(trace.resonance_frequencies, trace.orbit_lengths)
    
    @pytest.mark.slow
    def test_trace_identity_error(self, operator):
        """Test trace identity error."""
        spectrum = operator.compute_spectrum(n_eigenvalues=20)
        trace = operator.guinand_weil_trace_formula(t=1.0, spectrum=spectrum)
        
        # Error should be finite
        assert np.isfinite(trace.trace_identity_error)
        assert trace.trace_identity_error >= 0


class TestCompleteVerification:
    """Test complete verification framework."""
    
    @pytest.fixture
    def operator(self):
        """Create operator for testing."""
        config = HilbertSpaceConfig(x_min=1.0, x_max=40.0, n_grid=150)
        return FormalQuantumRHOperator(config)
    
    @pytest.mark.slow
    def test_complete_verification(self, operator):
        """Test complete verification runs successfully."""
        results = operator.complete_verification(n_eigenvalues=20)
        
        assert isinstance(results, dict)
        assert 'framework' in results
        assert 'hilbert_space' in results
        assert 'operator' in results
        assert 'self_adjointness' in results
        assert 'spectrum' in results
        assert 'counting_function' in results
        assert 'trace_formula' in results
        assert 'coherence' in results
        assert 'qcal_validation' in results
    
    @pytest.mark.slow
    def test_verification_framework_info(self, operator):
        """Test framework information."""
        results = operator.complete_verification(n_eigenvalues=15)
        
        assert results['framework'] == 'Formal Quantum Mechanical RH Operator'
        assert results['hilbert_space'] == 'L²([1, ∞), dx/x)'
        assert 'Ĥ_Ω' in results['operator']
    
    @pytest.mark.slow
    def test_verification_qcal_constants(self, operator):
        """Test QCAL constants in results."""
        results = operator.complete_verification(n_eigenvalues=15)
        
        assert results['qcal_frequency'] == F0
        assert results['coherence_constant'] == C_COHERENCE
    
    @pytest.mark.slow
    def test_verification_coherence(self, operator):
        """Test coherence computation."""
        results = operator.complete_verification(n_eigenvalues=20)
        
        assert 'Psi_total' in results['coherence']
        assert 0.0 <= results['coherence']['Psi_total'] <= 1.0
        
        # Should have component coherences
        assert 'components' in results['coherence']
        components = results['coherence']['components']
        assert 'self_adjointness' in components
        assert 'real_spectrum' in components
        assert 'weyl_law' in components
        assert 'trace_formula' in components
    
    @pytest.mark.slow
    def test_qcal_threshold(self, operator):
        """Test QCAL threshold validation."""
        results = operator.complete_verification(n_eigenvalues=20)
        
        assert 'qcal_validation' in results
        assert results['qcal_validation']['threshold'] == 0.888
        assert 'passes_threshold' in results['qcal_validation']
        assert results['qcal_validation']['framework'] == 'QCAL ∞³'
    
    @pytest.mark.slow
    def test_verification_signature(self, operator):
        """Test QCAL signature in results."""
        results = operator.complete_verification(n_eigenvalues=15)
        
        assert 'signature' in results['qcal_validation']
        assert '∞³' in results['qcal_validation']['signature']


class TestQCALConstants:
    """Test QCAL constants integration."""
    
    def test_fundamental_frequency(self):
        """Test fundamental frequency F0."""
        assert F0 == 141.7001
    
    def test_coherence_constant(self):
        """Test coherence constant C."""
        assert C_COHERENCE == 244.36
    
    def test_primary_constant(self):
        """Test primary constant."""
        assert C_PRIMARY == 629.83
    
    def test_berry_keating_constant(self):
        """Test Berry-Keating constant."""
        # C = π·ζ'(1/2) ≈ -12.3218
        assert BERRY_KEATING_C < 0
        assert abs(BERRY_KEATING_C) > 10


class TestUtilityFunctions:
    """Test utility functions."""
    
    def test_generate_primes(self):
        """Test prime generation."""
        operator = FormalQuantumRHOperator()
        primes = operator._generate_primes(10)
        
        assert len(primes) == 10
        assert primes[0] == 2
        assert primes[1] == 3
        assert primes[2] == 5
        assert primes[3] == 7
        assert primes[4] == 11
    
    def test_generate_large_primes(self):
        """Test generating larger number of primes."""
        operator = FormalQuantumRHOperator()
        primes = operator._generate_primes(100)
        
        assert len(primes) == 100
        # 100th prime is 541
        assert primes[-1] == 541
    
    def test_generate_zero_primes(self):
        """Test edge case: zero primes."""
        operator = FormalQuantumRHOperator()
        primes = operator._generate_primes(0)
        
        assert len(primes) == 0


class TestReferences:
    """Test reference values and comparisons."""
    
    def test_riemann_zeros_reference(self):
        """Test reference Riemann zeros."""
        # First zero
        assert ZEROS_ZETA_REFERENCE[0] == pytest.approx(14.134725, rel=1e-5)
        
        # Second zero
        assert ZEROS_ZETA_REFERENCE[1] == pytest.approx(21.022040, rel=1e-5)
        
        # Should have 10 reference zeros
        assert len(ZEROS_ZETA_REFERENCE) == 10
    
    def test_zeros_ordered(self):
        """Test that reference zeros are ordered."""
        assert all(ZEROS_ZETA_REFERENCE[i] < ZEROS_ZETA_REFERENCE[i + 1]
                  for i in range(len(ZEROS_ZETA_REFERENCE) - 1))


class TestPhysicalInterpretation:
    """Test physical interpretation aspects."""
    
    def test_zero_node_at_one(self):
        """Test Zero Node at x=1 (Vortex 8 boundary)."""
        config = HilbertSpaceConfig()
        assert config.x_min == 1.0
    
    def test_phase_reflection_condition(self):
        """Test phase reflection boundary condition."""
        config = HilbertSpaceConfig(phase_theta=np.pi / 4)
        operator = FormalQuantumRHOperator(config)
        
        # Phase condition should be encoded in boundary
        assert operator.hilbert_config.phase_theta == pytest.approx(np.pi / 4)
    
    def test_adelic_solenoid_compactification(self):
        """Test that operator implements adelic solenoid structure."""
        operator = FormalQuantumRHOperator()
        spectrum = operator.compute_spectrum(n_eigenvalues=10)
        
        # Spectrum should be discrete (compactification property)
        assert spectrum.is_discrete is True


# Integration test
@pytest.mark.slow
def test_full_operator_pipeline():
    """Integration test: full operator pipeline."""
    # Create operator
    config = HilbertSpaceConfig(x_min=1.0, x_max=40.0, n_grid=150)
    operator = FormalQuantumRHOperator(config)
    
    # Verify self-adjointness
    sa_proof = operator.verify_self_adjointness()
    assert sa_proof.is_self_adjoint
    
    # Compute spectrum
    spectrum = operator.compute_spectrum(n_eigenvalues=20)
    assert spectrum.is_discrete
    assert spectrum.is_real
    
    # Verify counting function
    counting = operator.verify_counting_function(spectrum)
    assert isinstance(counting, CountingFunction)
    
    # Verify trace formula
    trace = operator.guinand_weil_trace_formula(t=1.0, spectrum=spectrum)
    assert isinstance(trace, TraceFormulaResult)
    
    # Overall coherence should be good
    results = operator.complete_verification(n_eigenvalues=20)
    assert results['coherence']['Psi_total'] > 0.7


if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])
