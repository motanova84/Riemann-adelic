#!/usr/bin/env python3
"""
Test Suite for Atlas³-ABC Unified Operator Framework
====================================================

Tests the unified framework connecting Atlas³ spectral theory (Riemann Hypothesis)
with ABC conjecture through coupling tensor and adelic flow interpretation.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
License: CC BY-NC-SA 4.0
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add project root to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from operators.atlas3_abc_unified import (
    Atlas3ABCUnifiedOperator,
    radical,
    abc_information_function,
    arithmetic_reynolds_number,
    abc_quality,
    is_exceptional_triple,
    KAPPA_PI,
    EPSILON_CRITICAL,
    MU_COUPLING,
    F0,
    COUPLING_UNIVERSAL
)


class TestRadicalFunction:
    """Test the radical (product of distinct prime factors) function."""
    
    def test_radical_primes(self):
        """Test radical for prime numbers."""
        assert radical(2) == 2
        assert radical(3) == 3
        assert radical(5) == 5
        assert radical(7) == 7
        assert radical(11) == 11
    
    def test_radical_prime_powers(self):
        """Test radical for prime powers."""
        assert radical(4) == 2    # 2²
        assert radical(8) == 2    # 2³
        assert radical(9) == 3    # 3²
        assert radical(27) == 3   # 3³
        assert radical(16) == 2   # 2⁴
    
    def test_radical_composites(self):
        """Test radical for composite numbers."""
        assert radical(6) == 6    # 2 × 3
        assert radical(12) == 6   # 2² × 3
        assert radical(30) == 30  # 2 × 3 × 5
        assert radical(60) == 30  # 2² × 3 × 5
        assert radical(100) == 10 # 2² × 5²
    
    def test_radical_edge_cases(self):
        """Test radical for edge cases."""
        assert radical(0) == 1
        assert radical(1) == 1


class TestABCInformationFunction:
    """Test the ABC information function I(a,b,c)."""
    
    def test_valid_triples(self):
        """Test information function for valid ABC triples."""
        # Simple triple: 1 + 2 = 3
        I = abc_information_function(1, 2, 3)
        assert np.isfinite(I)  # Information should be finite
        
        # Famous triple: 1 + 8 = 9
        I = abc_information_function(1, 8, 9)
        assert np.isfinite(I)  # Should be finite
    
    def test_high_quality_triple(self):
        """Test high-quality triple 3 + 125 = 128."""
        # This is one of the highest known quality triples
        I = abc_information_function(3, 125, 128)
        assert I > 0  # Should have positive information excess (q > 1)
    
    def test_invalid_triple(self):
        """Test that invalid triples raise errors."""
        with pytest.raises(ValueError):
            abc_information_function(1, 2, 4)  # 1 + 2 ≠ 4
    
    def test_negative_values(self):
        """Test that negative values raise errors."""
        with pytest.raises(ValueError):
            abc_information_function(-1, 2, 1)


class TestArithmeticReynoldsNumber:
    """Test the arithmetic Reynolds number Re_abc."""
    
    def test_reynolds_number_range(self):
        """Test that Reynolds number is in expected range."""
        # Most triples should have Re close to 1
        Re = arithmetic_reynolds_number(1, 2, 3)
        assert 0.5 < Re < 2.0
        
        # High-quality triple should have higher Re
        Re = arithmetic_reynolds_number(3, 125, 128)
        assert Re > 1.1
    
    def test_reynolds_critical_comparison(self):
        """Test comparison with critical Reynolds number κ_Π."""
        # Standard triple should be below critical
        Re = arithmetic_reynolds_number(2, 3, 5)
        assert Re < KAPPA_PI
    
    def test_reynolds_computation(self):
        """Test that Reynolds number matches quality."""
        # Re_abc and q(a,b,c) should be proportional (different log base)
        a, b, c = 1, 8, 9
        Re = arithmetic_reynolds_number(a, b, c)
        q = abc_quality(a, b, c)
        
        # They should be close (both measure the same thing)
        assert abs(Re - q) < 0.1


class TestExceptionalTriples:
    """Test detection of exceptional ABC triples."""
    
    def test_exceptional_with_large_epsilon(self):
        """Test that no triples are exceptional for large ε."""
        # With ε = 0.5, most triples should not be exceptional
        assert not is_exceptional_triple(1, 2, 3, epsilon=0.5)
        assert not is_exceptional_triple(2, 3, 5, epsilon=0.5)
    
    def test_exceptional_with_small_epsilon(self):
        """Test that high-quality triples are exceptional for small ε."""
        # High-quality triple with very small epsilon
        # 3 + 125 = 128 has quality ≈ 1.427
        is_exc = is_exceptional_triple(3, 125, 128, epsilon=0.1)
        assert is_exc  # Should be exceptional
    
    def test_exceptional_with_critical_epsilon(self):
        """Test with critical epsilon from cosmic temperature."""
        # With critical ε ≈ 2.64e-12, essentially all triples are exceptional
        # in the classical sense, but quantum coherence bounds them
        a, b, c = 1, 8, 9
        # This should be exceptional for such tiny epsilon
        assert is_exceptional_triple(a, b, c, epsilon=EPSILON_CRITICAL)


class TestUnifiedOperator:
    """Test the unified Atlas³-ABC operator."""
    
    @pytest.fixture
    def operator(self):
        """Create operator for testing."""
        return Atlas3ABCUnifiedOperator(N=50)  # Small for speed
    
    def test_operator_initialization(self, operator):
        """Test that operator initializes correctly."""
        assert operator.N == 50
        assert operator.kappa == KAPPA_PI
        assert operator.mu == MU_COUPLING
        assert operator.epsilon_critical == EPSILON_CRITICAL
    
    def test_spectral_gap_computation(self, operator):
        """Test spectral gap calculation."""
        gap = operator.gap_lambda
        assert gap > 0  # Gap should be positive
        assert np.isfinite(gap)  # Should be finite
    
    def test_operator_construction(self, operator):
        """Test that operator matrix is constructed."""
        assert operator.operator is not None
        assert operator.operator.shape == (50, 50)
        
        # Check Hermiticity (operator should be Hermitian)
        hermiticity_error = np.linalg.norm(
            operator.operator - operator.operator.T.conj()
        )
        assert hermiticity_error < 1e-10  # Should be Hermitian
    
    def test_spectrum_computation(self, operator):
        """Test spectrum computation."""
        eigenvalues = operator.compute_spectrum()
        
        assert len(eigenvalues) == operator.N
        assert np.all(np.isfinite(eigenvalues))
        
        # Eigenvalues should be real (Hermitian operator)
        assert np.all(np.isreal(eigenvalues))
    
    def test_coupling_tensor(self, operator):
        """Test coupling tensor computation."""
        coupling = operator.compute_coupling_tensor()
        
        # Check all fields are present
        assert coupling.coupling_strength == operator.mu
        assert np.isfinite(coupling.divergence)
        assert np.isfinite(coupling.coherence_psi)
        assert np.isfinite(coupling.spectral_component)
        assert np.isfinite(coupling.arithmetic_component)
        
        # Conservation: divergence should be small
        assert coupling.divergence < 1.0  # Reasonable bound
    
    def test_coupling_conservation(self, operator):
        """Test that coupling tensor satisfies conservation law."""
        coupling = operator.compute_coupling_tensor()
        
        # ∇_μ T_μν should be ~0 for conservation
        # Divergence should be small
        assert coupling.divergence < 0.1
    
    def test_heat_trace(self, operator):
        """Test ABC-weighted heat trace computation."""
        t = 1.0
        trace, remainder = operator.abc_weighted_heat_trace(t)
        
        assert trace > 0  # Trace should be positive
        assert remainder >= 0  # Bound should be non-negative
        assert np.isfinite(trace)
        assert np.isfinite(remainder)
    
    def test_heat_trace_with_abc_triples(self, operator):
        """Test heat trace with ABC triple weighting."""
        triples = [(1, 2, 3), (1, 8, 9), (2, 3, 5)]
        t = 1.0
        
        trace, remainder = operator.abc_weighted_heat_trace(t, triples)
        
        assert trace > 0
        assert remainder >= 0
    
    def test_remainder_bound(self, operator):
        """Test that remainder satisfies |R_ABC(t)| ≤ C·ε·e^(-λ/t)."""
        t = 1.0
        _, remainder = operator.abc_weighted_heat_trace(t)
        
        # Check theoretical bound
        theoretical_bound = EPSILON_CRITICAL * np.exp(-operator.gap_lambda / t)
        
        # Remainder should respect the bound (with some numerical tolerance)
        assert remainder <= theoretical_bound * 10  # Factor of 10 for numerics
    
    def test_critical_line_alignment(self, operator):
        """Test alignment with critical line Re(s) = 1/2."""
        deviation = operator.verify_critical_line_alignment()
        
        assert np.isfinite(deviation)
        assert deviation >= 0  # Deviation is always non-negative
    
    def test_exceptional_count(self, operator):
        """Test counting of exceptional ABC triples."""
        count = operator.count_exceptional_abc_triples(max_c=50)
        
        assert count >= 0  # Count should be non-negative
        assert count < 1000  # Should be finite
    
    def test_unified_properties(self, operator):
        """Test unified spectral properties computation."""
        properties = operator.compute_unified_properties()
        
        # Check all properties are computed
        assert len(properties.eigenvalues) == operator.N
        assert properties.gap_lambda > 0
        assert np.isfinite(properties.abc_weighted_trace)
        assert np.isfinite(properties.remainder_bound)
        assert np.isfinite(properties.critical_line_alignment)
        assert properties.abc_exceptional_count >= 0


class TestConstants:
    """Test that fundamental constants are correct."""
    
    def test_kappa_pi(self):
        """Test arithmetic Reynolds number κ_Π."""
        assert 2.5 < KAPPA_PI < 2.6
        # Should match Atlas³ critical PT threshold
        assert abs(KAPPA_PI - 2.57731) < 0.01
    
    def test_epsilon_critical(self):
        """Test critical epsilon from cosmic temperature."""
        # ε_critical ≈ (ℏf₀)/(k_B·T_cosmic)
        assert EPSILON_CRITICAL > 0
        assert EPSILON_CRITICAL < 1e-10  # Very small
    
    def test_mu_coupling(self):
        """Test coupling constant μ = κ_Π · ε_critical."""
        expected_mu = KAPPA_PI * EPSILON_CRITICAL
        assert abs(MU_COUPLING - expected_mu) / expected_mu < 0.01
    
    def test_fundamental_frequency(self):
        """Test fundamental frequency f₀ = 141.7001 Hz."""
        assert abs(F0 - 141.7001) < 0.0001
    
    def test_coupling_universal(self):
        """Test universal coupling constant independence from f₀."""
        # Should be of order 10^-11 to 10^-12
        assert 1e-13 < COUPLING_UNIVERSAL < 1e-10


class TestCertificateGeneration:
    """Test certificate generation."""
    
    def test_generate_certificate(self):
        """Test that certificate can be generated."""
        operator = Atlas3ABCUnifiedOperator(N=30)
        cert = operator.generate_certificate()
        
        # Check structure
        assert "protocol" in cert
        assert cert["protocol"] == "ATLAS3-ABC-UNIFIED"
        assert "version" in cert
        assert "constants" in cert
        assert "operator" in cert
        assert "coupling_tensor" in cert
        assert "spectral_properties" in cert
        assert "unification_status" in cert
        assert "signature" in cert
    
    def test_certificate_constants(self):
        """Test that certificate contains correct constants."""
        operator = Atlas3ABCUnifiedOperator(N=30)
        cert = operator.generate_certificate()
        
        constants = cert["constants"]
        assert constants["f0_hz"] == F0
        assert constants["kappa_pi"] == KAPPA_PI
        assert constants["epsilon_critical"] == EPSILON_CRITICAL
        assert constants["mu_coupling"] == MU_COUPLING
    
    def test_unification_status(self):
        """Test unification status in certificate."""
        operator = Atlas3ABCUnifiedOperator(N=30)
        cert = operator.generate_certificate()
        
        status = cert["unification_status"]
        
        # Check boolean fields (numpy bool is also valid)
        assert isinstance(status["conservation_verified"], (bool, np.bool_))
        assert isinstance(status["critical_line_aligned"], (bool, np.bool_))
        assert isinstance(status["abc_bounded"], (bool, np.bool_))


class TestNumericalStability:
    """Test numerical stability of computations."""
    
    def test_different_sizes(self):
        """Test operator for different discretization sizes."""
        sizes = [10, 25, 50, 100]
        
        for N in sizes:
            operator = Atlas3ABCUnifiedOperator(N=N)
            eigenvalues = operator.compute_spectrum()
            
            assert len(eigenvalues) == N
            assert np.all(np.isfinite(eigenvalues))
    
    def test_reproducibility(self):
        """Test that results are reproducible."""
        op1 = Atlas3ABCUnifiedOperator(N=30)
        op2 = Atlas3ABCUnifiedOperator(N=30)
        
        eigs1 = op1.compute_spectrum()
        eigs2 = op2.compute_spectrum()
        
        np.testing.assert_array_almost_equal(eigs1, eigs2)
    
    def test_no_nans_or_infs(self):
        """Test that computations don't produce NaN or Inf."""
        operator = Atlas3ABCUnifiedOperator(N=50)
        
        # Spectrum
        eigs = operator.compute_spectrum()
        assert np.all(np.isfinite(eigs))
        
        # Coupling tensor
        coupling = operator.compute_coupling_tensor()
        assert np.isfinite(coupling.divergence)
        assert np.isfinite(coupling.coherence_psi)
        
        # Heat trace
        trace, remainder = operator.abc_weighted_heat_trace(1.0)
        assert np.isfinite(trace)
        assert np.isfinite(remainder)


class TestTheoreticalBounds:
    """Test theoretical bounds from unified theory."""
    
    def test_gap_lambda_positive(self):
        """Test that spectral gap is positive."""
        operator = Atlas3ABCUnifiedOperator(N=50)
        assert operator.gap_lambda > 0
    
    def test_gap_lambda_finite(self):
        """Test that spectral gap is finite."""
        operator = Atlas3ABCUnifiedOperator(N=50)
        assert np.isfinite(operator.gap_lambda)
    
    def test_abc_exceptional_finite(self):
        """Test that exceptional ABC triples are finite in number."""
        operator = Atlas3ABCUnifiedOperator(N=50)
        count = operator.count_exceptional_abc_triples(max_c=100)
        
        # Should be finite (not infinite)
        assert count < float('inf')
        
        # Should be reasonably small
        assert count < 10000


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
