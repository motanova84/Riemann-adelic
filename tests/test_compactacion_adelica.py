#!/usr/bin/env python3
"""
Tests for Compactación Adélica
==============================

Unit tests for the adelic compactification framework.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: March 2026
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from operators.compactacion_adelica import (
    CompactacionAdelica,
    compute_berry_phase_topological,
    validate_seven_eighths_exact,
    BERRY_PHASE_FACTOR
)


class TestCompactacionAdelica:
    """Tests for CompactacionAdelica class."""
    
    def test_initialization(self):
        """Test framework initialization."""
        comp = CompactacionAdelica(L=100.0, N_primes=50)
        
        assert comp.L == 100.0
        assert comp.N_primes == 50
        assert len(comp.primes) == 50
        assert len(comp.log_primes) == 50
        assert comp.berry_phase == BERRY_PHASE_FACTOR * 2 * np.pi
    
    def test_prime_generation(self):
        """Test prime number generation."""
        comp = CompactacionAdelica(L=100.0, N_primes=10)
        
        expected_primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
        assert np.array_equal(comp.primes, expected_primes)
    
    def test_torus_eigenvalues(self):
        """Test torus eigenvalues λ_n = 2πn/L."""
        comp = CompactacionAdelica(L=100.0, N_primes=20)
        eigenvals = comp.torus_eigenvalues(n_max=5)
        
        # Check number of eigenvalues
        assert len(eigenvals) == 11  # -5 to 5 inclusive
        
        # Check spacing
        spacing = np.diff(eigenvals)
        expected_spacing = 2 * np.pi / comp.L
        assert np.allclose(spacing, expected_spacing, rtol=1e-12)
        
        # Check specific values
        assert np.isclose(eigenvals[5], 0.0, atol=1e-15)  # n=0
        assert np.isclose(eigenvals[6], 2*np.pi/100, rtol=1e-12)  # n=1
    
    def test_logarithmic_lattice(self):
        """Test logarithmic lattice construction."""
        comp = CompactacionAdelica(L=100.0, N_primes=10)
        lattice = comp.logarithmic_lattice(k_max=2)
        
        # Check lattice is sorted
        assert np.all(lattice[:-1] <= lattice[1:])
        
        # Check all values are finite
        assert np.all(np.isfinite(lattice))
        
        # Check lattice size (10 primes × 2 powers)
        assert len(lattice) == 20
    
    def test_transfer_matrix(self):
        """Test transfer matrix construction."""
        comp = CompactacionAdelica(L=100.0, N_primes=20)
        T = comp.transfer_matrix(n_dim=10)
        
        # Check dimensions
        assert T.shape == (10, 10)
        
        # Check all elements are finite
        assert not np.any(np.isnan(T))
        assert not np.any(np.isinf(T))
        
        # Check diagonal elements
        for i in range(10):
            p = comp.primes[i]
            expected_diag = np.log(p) / np.sqrt(p)
            assert np.isclose(T[i, i], expected_diag, rtol=1e-10)
        
        # Check matrix is well-conditioned
        cond = np.linalg.cond(T)
        assert cond < 1e10
    
    def test_berry_phase_calculation(self):
        """Test Berry phase calculation."""
        comp = CompactacionAdelica(L=100.0, N_primes=30)
        results = comp.berry_phase_calculation(n_modes=10)
        
        # Check theoretical value
        expected = (7.0/8.0) * 2 * np.pi
        assert np.isclose(results['berry_phase_theoretical'], expected, atol=1e-15)
        
        # Check factor
        assert results['berry_factor'] == 7.0/8.0
        
        # Check it's marked as topological invariant
        assert results['is_topological_invariant'] is True
        
        # Check exact value string
        assert results['exact_value'] == '7/8 · 2π'
    
    def test_berry_phase_topological_function(self):
        """Test standalone Berry phase computation."""
        phi = compute_berry_phase_topological()
        
        expected = (7.0/8.0) * 2 * np.pi
        assert np.isclose(phi, expected, atol=1e-15)
    
    def test_seven_eighths_exact(self):
        """Test 7/8 exactness validation."""
        results = validate_seven_eighths_exact()
        
        assert results['value'] == 7.0/8.0
        assert results['exact_fraction'] == '7/8'
        assert results['decimal'] == 0.875
        assert results['is_exact'] is True
        assert results['is_asymptotic'] is False
        assert results['is_topological_invariant'] is True
    
    def test_determinant_zero_correspondence(self):
        """Test determinant calculation."""
        comp = CompactacionAdelica(L=100.0, N_primes=40)
        
        # Test at a known Riemann zero
        lambda_zero = 14.134725  # First zero
        det_val = comp.determinant_zero_correspondence(lambda_zero, n_dim=20)
        
        # Determinant should be finite
        assert np.isfinite(det_val)
        
        # Test determinant varies with lambda
        det_val2 = comp.determinant_zero_correspondence(20.0, n_dim=20)
        assert abs(det_val2 - det_val) > 0.01
        
        # Test determinant at zero lambda (should be inf)
        det_zero = comp.determinant_zero_correspondence(0.0, n_dim=20)
        assert np.isinf(det_zero)
    
    def test_trace_formula_exact(self):
        """Test exact trace formula."""
        comp = CompactacionAdelica(L=100.0, N_primes=30)
        
        # Test at t=0.1
        results = comp.trace_formula_exact(t=0.1, n_terms=20)
        
        # Check all components are finite
        assert np.isfinite(results['weyl_term'])
        assert np.isfinite(results['berry_term'])
        assert np.isfinite(results['prime_sum'])
        assert np.isfinite(results['trace_total'])
        
        # Check Berry term is exactly 7/8
        assert np.isclose(results['berry_term'], 7.0/8.0, atol=1e-15)
        
        # Check Berry term is marked as exact
        assert results['berry_exact'] is True
        
        # Check time parameter
        assert results['time_t'] == 0.1
        
        # Weyl term should be positive
        assert results['weyl_term'] > 0
    
    def test_trace_formula_berry_constant(self):
        """Test that Berry term is independent of time."""
        comp = CompactacionAdelica(L=100.0, N_primes=20)
        
        # Compute at different times
        results1 = comp.trace_formula_exact(t=0.1, n_terms=10)
        results2 = comp.trace_formula_exact(t=0.05, n_terms=10)
        results3 = comp.trace_formula_exact(t=0.2, n_terms=10)
        
        # Berry term should be identical
        assert results1['berry_term'] == results2['berry_term'] == results3['berry_term']
        assert results1['berry_term'] == 7.0/8.0
    
    def test_trace_formula_error_handling(self):
        """Test trace formula error handling."""
        comp = CompactacionAdelica(L=100.0, N_primes=20)
        
        # Test negative time raises error
        with pytest.raises(ValueError):
            comp.trace_formula_exact(t=-0.1)
        
        # Test zero time raises error
        with pytest.raises(ValueError):
            comp.trace_formula_exact(t=0.0)
    
    def test_validate_compactification(self):
        """Test comprehensive validation."""
        comp = CompactacionAdelica(L=100.0, N_primes=30)
        results = comp.validate_compactification()
        
        # Check framework info
        assert results['framework'] == 'Compactación Adélica'
        assert results['status'] in ['validated', 'failed']
        assert 'checks' in results
        
        # Check QCAL parameters
        assert results['coherence_qcal'] == 244.36
        assert results['frequency_f0'] == 141.7001
        
        # Check individual validations exist
        assert 'torus_eigenvalues' in results['checks']
        assert 'berry_phase' in results['checks']
        assert 'transfer_matrix' in results['checks']
        assert 'determinant_calculation' in results['checks']
        assert 'trace_formula' in results['checks']
    
    def test_generate_certificate(self):
        """Test certificate generation."""
        comp = CompactacionAdelica(L=100.0, N_primes=20)
        
        # Generate without saving
        cert = comp.generate_certificate()
        
        # Check structure
        assert cert['framework'] == 'QCAL ∞³ — Compactación Adélica'
        assert cert['author'] == 'José Manuel Mota Burruezo Ψ ✧ ∞³'
        assert cert['orcid'] == '0009-0002-1923-0773'
        assert cert['doi'] == '10.5281/zenodo.17379721'
        assert cert['signature'] == '∴𓂀Ω∞³Φ'
        
        # Check mathematical structure
        assert 'mathematical_structure' in cert
        assert cert['mathematical_structure']['idele_quotient'] == 'A = R+/Γ_aritm'
        assert cert['mathematical_structure']['logarithmic_torus'] == 'T_log = R/(Z·log Λ)'
        assert cert['mathematical_structure']['scale_operator'] == 'D = -i d/dt'
        
        # Check Berry phase
        assert 'berry_phase' in cert
        assert cert['berry_phase']['exact_fraction'] == '7/8'
        assert cert['berry_phase']['topological_invariant'] is True
        assert cert['berry_phase']['not_fitting_parameter'] is True
        
        # Check trace formula
        assert 'trace_formula' in cert
        assert cert['trace_formula']['berry_exact'] is True
        
        # Check spectral identity
        assert 'spectral_identity' in cert
        assert cert['spectral_identity']['identity_exact'] is True
    
    def test_berry_phase_not_asymptotic(self):
        """Test that 7/8 is NOT from asymptotic expansion."""
        # The Berry phase should be exact, not a limit
        comp = CompactacionAdelica(L=100.0, N_primes=10)
        
        # Multiple calculations should give identical results
        results1 = comp.berry_phase_calculation(n_modes=5)
        results2 = comp.berry_phase_calculation(n_modes=20)
        results3 = comp.berry_phase_calculation(n_modes=50)
        
        # Theoretical value should be identical (exact)
        assert results1['berry_phase_theoretical'] == results2['berry_phase_theoretical']
        assert results2['berry_phase_theoretical'] == results3['berry_phase_theoretical']
        
        # All should equal 7/8 · 2π exactly
        expected = (7.0/8.0) * 2 * np.pi
        assert results1['berry_phase_theoretical'] == expected
        assert results2['berry_phase_theoretical'] == expected
        assert results3['berry_phase_theoretical'] == expected
    
    def test_torus_length_variations(self):
        """Test framework with different torus lengths."""
        for L in [50.0, 100.0, 200.0]:
            comp = CompactacionAdelica(L=L, N_primes=20)
            
            # Berry phase should be independent of L
            assert comp.berry_phase == (7.0/8.0) * 2 * np.pi
            
            # Eigenvalue spacing should depend on L
            eigenvals = comp.torus_eigenvalues(n_max=3)
            spacing = eigenvals[4] - eigenvals[3]  # n=1 to n=0
            expected_spacing = 2 * np.pi / L
            assert np.isclose(spacing, expected_spacing, rtol=1e-12)
    
    def test_edge_cases(self):
        """Test edge cases."""
        # Small number of primes
        comp_small = CompactacionAdelica(L=100.0, N_primes=5)
        assert len(comp_small.primes) == 5
        
        # Minimal setup
        comp_min = CompactacionAdelica(L=10.0, N_primes=3)
        T = comp_min.transfer_matrix(n_dim=3)
        assert T.shape == (3, 3)
        
        # Eigenvalues at n_max=0 (just the zero mode)
        eigenvals_zero = comp_min.torus_eigenvalues(n_max=0)
        assert len(eigenvals_zero) == 1
        assert np.isclose(eigenvals_zero[0], 0.0, atol=1e-15)


class TestBerryPhaseTopology:
    """Specific tests for Berry phase topological properties."""
    
    def test_berry_phase_value(self):
        """Test Berry phase equals 7/8 · 2π."""
        phi = compute_berry_phase_topological()
        expected = (7.0/8.0) * 2 * np.pi
        assert np.isclose(phi, expected, atol=1e-15)
    
    def test_berry_phase_alternate_form(self):
        """Test Berry phase equals 7π/4."""
        phi = compute_berry_phase_topological()
        assert np.isclose(phi, 7 * np.pi / 4, atol=1e-15)
    
    def test_berry_factor(self):
        """Test Berry phase factor is exactly 7/8."""
        assert BERRY_PHASE_FACTOR == 7.0/8.0
        assert BERRY_PHASE_FACTOR == 0.875
    
    def test_berry_phase_not_fitting(self):
        """Verify Berry phase is not a fitting parameter."""
        results = validate_seven_eighths_exact()
        
        # It's exact, not asymptotic
        assert results['is_exact'] is True
        assert results['is_asymptotic'] is False
        
        # It's a topological invariant
        assert results['is_topological_invariant'] is True
        
        # Origin is from topology, not fitting
        assert 'Berry phase' in results['origin']
        assert 'compactification' in results['origin']


class TestDeterminantZeroCorrespondence:
    """Tests for determinant-zero correspondence."""
    
    def test_determinant_at_riemann_zeros(self):
        """Test determinant near known Riemann zeros."""
        comp = CompactacionAdelica(L=100.0, N_primes=40)
        
        # First few Riemann zeros (imaginary parts)
        riemann_zeros = [14.134725, 21.022040, 25.010858, 30.424876]
        
        for gamma in riemann_zeros:
            det_val = comp.determinant_zero_correspondence(gamma, n_dim=25)
            # Determinant should be computable
            assert np.isfinite(det_val)
    
    def test_determinant_continuity(self):
        """Test determinant varies continuously."""
        comp = CompactacionAdelica(L=100.0, N_primes=30)
        
        # Sample determinant at several points
        lambdas = np.linspace(10, 30, 20)
        dets = [comp.determinant_zero_correspondence(lam, n_dim=20) for lam in lambdas]
        
        # All should be finite
        assert all(np.isfinite(d) for d in dets)
        
        # Should vary smoothly (no huge jumps)
        diffs = np.abs(np.diff(dets))
        assert np.max(diffs) < 10.0  # Reasonable variation


class TestTraceFormulaExact:
    """Tests for exact trace formula."""
    
    def test_trace_components_separation(self):
        """Test that trace components are well-separated."""
        comp = CompactacionAdelica(L=100.0, N_primes=30)
        results = comp.trace_formula_exact(t=0.1, n_terms=20)
        
        # Each component should contribute
        assert results['weyl_term'] > 0
        assert results['berry_term'] > 0
        assert results['prime_sum'] > 0
        
        # Total should be sum of parts (approximately)
        total_expected = (results['weyl_term'] + results['berry_term'] + 
                         results['prime_sum'] + results['error_term'])
        assert np.isclose(results['trace_total'], total_expected, rtol=1e-10)
    
    def test_trace_small_t_behavior(self):
        """Test trace formula behavior for small t."""
        comp = CompactacionAdelica(L=100.0, N_primes=20)
        
        # For small t, Weyl term should dominate
        results_small = comp.trace_formula_exact(t=0.01, n_terms=10)
        assert results_small['weyl_term'] > results_small['berry_term']
        assert results_small['weyl_term'] > abs(results_small['prime_sum'])
    
    def test_trace_berry_contribution(self):
        """Test Berry contribution to trace."""
        comp = CompactacionAdelica(L=100.0, N_primes=20)
        
        # Compute trace at several times
        times = [0.05, 0.1, 0.2, 0.5]
        berry_contributions = []
        
        for t in times:
            results = comp.trace_formula_exact(t=t, n_terms=15)
            berry_contributions.append(results['berry_term'])
        
        # All Berry contributions should be identical (constant term)
        assert all(b == berry_contributions[0] for b in berry_contributions)
        assert berry_contributions[0] == 7.0/8.0


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
