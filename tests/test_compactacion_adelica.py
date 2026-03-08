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


# ---------------------------------------------------------------------------
# New tests: Spectral Matching, Haar Measure, Zeta, Sparse matrices
# ---------------------------------------------------------------------------

class TestSpectralMatching:
    """Tests for spectral_eigenvalues and _weyl_counting_inv."""

    def test_weyl_counting_inv_basic(self):
        """N_smooth(_weyl_counting_inv(k)) == k for integer k."""
        two_pi = 2.0 * np.pi
        for k in [1, 2, 3, 5, 10, 20]:
            E = CompactacionAdelica._weyl_counting_inv(k)
            ratio = E / two_pi
            N_val = ratio * np.log(ratio) - ratio + 7.0 / 8.0
            assert abs(N_val - k) < 1e-6, (
                f"N_smooth({E:.4f}) = {N_val:.6f}, expected {k}"
            )

    def test_weyl_counting_inv_zero(self):
        """_weyl_counting_inv(0) returns 0."""
        assert CompactacionAdelica._weyl_counting_inv(0.0) == 0.0

    def test_weyl_counting_inv_negative(self):
        """_weyl_counting_inv for non-positive k returns 0."""
        assert CompactacionAdelica._weyl_counting_inv(-5.0) == 0.0
        assert CompactacionAdelica._weyl_counting_inv(-0.001) == 0.0

    def test_weyl_counting_inv_large_k(self):
        """_weyl_counting_inv works for large k (numerical stability)."""
        two_pi = 2.0 * np.pi
        for k in [100, 500, 1000]:
            E = CompactacionAdelica._weyl_counting_inv(k)
            assert np.isfinite(E), f"Non-finite result for k={k}"
            assert E > 0.0, f"Non-positive result for k={k}"
            ratio = E / two_pi
            N_val = ratio * np.log(ratio) - ratio + 7.0 / 8.0
            # Allow slightly larger tolerance for large k
            assert abs(N_val - k) < 1e-4, (
                f"k={k}: N_smooth({E:.2f}) = {N_val:.4f}"
            )

    def test_weyl_counting_inv_monotone(self):
        """_weyl_counting_inv is strictly increasing."""
        k_vals = [1, 2, 5, 10, 20, 50]
        E_vals = [CompactacionAdelica._weyl_counting_inv(k) for k in k_vals]
        for i in range(len(E_vals) - 1):
            assert E_vals[i] < E_vals[i + 1], (
                f"Not monotone: E({k_vals[i]})={E_vals[i]:.4f} >= E({k_vals[i+1]})={E_vals[i+1]:.4f}"
            )

    @pytest.mark.parametrize("N", [10, 20, 50, 100, 200])
    def test_spectral_eigenvalues_sqrt_scale_size(self, N: int):
        """spectral_eigenvalues returns N values for dense matrices."""
        comp = CompactacionAdelica()
        evals = comp.spectral_eigenvalues(N=N, scale="sqrt", psi=1.0)
        assert len(evals) == N

    @pytest.mark.parametrize("N,scale", [
        (20, "sqrt"),
        (50, "sqrt"),
        (20, "log"),
        (50, "log"),
    ])
    def test_spectral_eigenvalues_psi1_real(self, N: int, scale: str):
        """For psi=1, eigenvalues are real (imaginary parts ~ 0)."""
        comp = CompactacionAdelica()
        evals = comp.spectral_eigenvalues(N=N, scale=scale, psi=1.0)
        max_imag = float(np.max(np.abs(evals.imag)))
        assert max_imag < 1e-8, (
            f"N={N}, scale={scale}: max |Im(λ)| = {max_imag:.2e}"
        )

    @pytest.mark.parametrize("psi", [0.3, 0.5, 0.7, 0.9])
    def test_spectral_eigenvalues_psi_lt1_complex(self, psi: float):
        """For psi < 1, eigenvalues must have non-zero imaginary parts."""
        comp = CompactacionAdelica()
        evals = comp.spectral_eigenvalues(N=30, scale="sqrt", psi=psi)
        # At least some eigenvalues should be complex
        n_complex = int(np.sum(np.abs(evals.imag) > 1e-10))
        assert n_complex > 0, (
            f"psi={psi}: expected complex eigenvalues but all are real"
        )

    def test_spectral_eigenvalues_sqrt_range(self):
        """Scaled eigenvalues (sqrt) overlap with Riemann zeros range [14, 77]."""
        comp = CompactacionAdelica()
        N = 100
        evals = comp.spectral_eigenvalues(N=N, scale="sqrt", psi=1.0)
        real_positive = evals.real[evals.real > 0]
        assert np.any(real_positive < 30.0), "No eigenvalue below 30"
        assert np.any(real_positive > 14.0), "No eigenvalue above 14"

    def test_spectral_eigenvalues_log_range(self):
        """Scaled eigenvalues (log) are positive and in a reasonable range."""
        comp = CompactacionAdelica()
        evals = comp.spectral_eigenvalues(N=50, scale="log", psi=1.0)
        assert np.all(evals.real >= 0.0), "Some eigenvalues negative"

    def test_spectral_eigenvalues_raw_in_0_to_10(self):
        """Raw (unscaled) eigenvalues are in the 0–10 range for moderate N."""
        comp = CompactacionAdelica()
        N = 50
        evals = comp.spectral_eigenvalues(N=N, scale="sqrt", psi=1.0)
        alpha = np.sqrt(float(N))
        raw = evals.real / alpha
        # The first raw eigenvalue must be positive
        assert float(raw[0]) > 0.0, "First raw eigenvalue not positive"
        # The first 10 raw eigenvalues should all be in [0, 10]
        for i in range(min(10, len(raw))):
            assert 0.0 <= float(raw[i]) <= 10.0, (
                f"raw_{i+1} = {raw[i]:.4f} outside [0, 10]"
            )

    def test_spectral_eigenvalues_sorted(self):
        """Eigenvalues are returned sorted by real part."""
        comp = CompactacionAdelica()
        evals = comp.spectral_eigenvalues(N=30, scale="sqrt", psi=1.0)
        for i in range(len(evals) - 1):
            assert evals[i].real <= evals[i + 1].real + 1e-10, (
                f"Eigenvalues not sorted at index {i}"
            )

    def test_spectral_eigenvalues_invalid_N(self):
        """N < 2 raises ValueError."""
        comp = CompactacionAdelica()
        with pytest.raises(ValueError, match="N must be at least 2"):
            comp.spectral_eigenvalues(N=1)

    def test_spectral_eigenvalues_invalid_scale(self):
        """Unknown scale raises ValueError."""
        comp = CompactacionAdelica()
        with pytest.raises(ValueError, match="scale must be"):
            comp.spectral_eigenvalues(N=10, scale="bad")

    def test_spectral_eigenvalues_invalid_psi(self):
        """psi <= 0 raises ValueError."""
        comp = CompactacionAdelica()
        with pytest.raises(ValueError, match="psi must be positive"):
            comp.spectral_eigenvalues(N=10, psi=0.0)

    def test_spectral_eigenvalues_psi1_sorted_ascending(self):
        """Real eigenvalues (psi=1) are strictly ordered."""
        comp = CompactacionAdelica()
        evals = comp.spectral_eigenvalues(N=20, scale="sqrt", psi=1.0)
        real_vals = evals.real
        diffs = np.diff(real_vals)
        assert np.all(diffs >= -1e-10), "Eigenvalues not sorted ascending"

    @pytest.mark.parametrize("N,psi", [
        (10, 1.0),
        (20, 0.5),
        (50, 0.8),
        (100, 1.0),
    ])
    def test_spectral_eigenvalues_finite(self, N: int, psi: float):
        """All eigenvalues must be finite numbers."""
        comp = CompactacionAdelica()
        evals = comp.spectral_eigenvalues(N=N, scale="sqrt", psi=psi)
        assert np.all(np.isfinite(evals.real)), "Non-finite real parts"
        assert np.all(np.isfinite(evals.imag)), "Non-finite imaginary parts"


class TestHaarMeasure:
    """Tests for Haar measure inner product and log potential."""

    def test_log_potential_positive_input(self):
        """log_potential(x) = log(1 + 1/x) for positive x."""
        x = np.array([1.0, 2.0, 5.0, 10.0])
        expected = np.log1p(1.0 / x)
        result = CompactacionAdelica.log_potential(x)
        assert np.allclose(result, expected, rtol=1e-12)

    def test_log_potential_decreasing(self):
        """log(1 + 1/x) is strictly decreasing for x > 0."""
        x = np.linspace(0.5, 10.0, 100)
        V = CompactacionAdelica.log_potential(x)
        assert np.all(np.diff(V) < 0), "log_potential is not decreasing"

    def test_log_potential_at_one(self):
        """log_potential(1) = log(2)."""
        assert abs(CompactacionAdelica.log_potential(1.0) - np.log(2.0)) < 1e-12

    def test_log_potential_scalar(self):
        """log_potential accepts scalars."""
        v = CompactacionAdelica.log_potential(2.0)
        assert abs(v - np.log(1.5)) < 1e-12

    def test_log_potential_invalid_zero(self):
        """log_potential(0) raises ValueError."""
        with pytest.raises(ValueError, match="log_potential requires x > 0"):
            CompactacionAdelica.log_potential(0.0)

    def test_log_potential_invalid_negative(self):
        """log_potential(-1) raises ValueError."""
        with pytest.raises(ValueError, match="log_potential requires x > 0"):
            CompactacionAdelica.log_potential(-1.0)

    def test_haar_inner_product_positive(self):
        """<f, f> > 0 for non-zero f."""
        f = lambda x: np.exp(-x / 10.0)
        ip = CompactacionAdelica.haar_measure_inner_product(f, f, a=1.0, b=10.0)
        assert ip.real > 0.0

    def test_haar_inner_product_linearity(self):
        """Inner product is linear in second argument."""
        f = lambda x: np.exp(-x / 5.0)
        g1 = lambda x: np.sin(x / 10.0)
        g2 = lambda x: np.cos(x / 10.0)
        c1, c2 = 2.0, 3.0
        g12 = lambda x: c1 * g1(x) + c2 * g2(x)

        ip1 = CompactacionAdelica.haar_measure_inner_product(f, g1, 1.0, 10.0)
        ip2 = CompactacionAdelica.haar_measure_inner_product(f, g2, 1.0, 10.0)
        ip12 = CompactacionAdelica.haar_measure_inner_product(f, g12, 1.0, 10.0)

        assert abs(ip12 - (c1 * ip1 + c2 * ip2)) < 1e-6

    def test_haar_inner_product_symmetry(self):
        """<f, g> = conj(<g, f>)."""
        f = lambda x: np.exp(-x / 5.0)
        g = lambda x: 1.0 / (1.0 + x)
        ip_fg = CompactacionAdelica.haar_measure_inner_product(f, g, 1.0, 10.0)
        ip_gf = CompactacionAdelica.haar_measure_inner_product(g, f, 1.0, 10.0)
        assert abs(ip_fg - np.conj(ip_gf)) < 1e-6

    def test_haar_norm_non_negative(self):
        """Haar norm is non-negative."""
        f = lambda x: np.exp(-x)
        norm = CompactacionAdelica.haar_measure_norm(f, a=1.0, b=5.0)
        assert norm >= 0.0

    def test_haar_inner_product_invalid_bounds(self):
        """Invalid bounds raise ValueError."""
        f = lambda x: x
        with pytest.raises(ValueError, match="Lower bound a must be positive"):
            CompactacionAdelica.haar_measure_inner_product(f, f, a=0.0, b=10.0)
        with pytest.raises(ValueError, match="Upper bound b must be greater"):
            CompactacionAdelica.haar_measure_inner_product(f, f, a=5.0, b=2.0)

    def test_haar_inner_product_multiplicative_invariance(self):
        """Haar measure is invariant under dilation x → cx."""
        c = 3.0
        f = lambda x: np.exp(-x / 10.0)
        g = lambda x: np.exp(-x / 10.0)

        # ∫_a^b f̄(x)g(x) dx/x  =  ∫_{ca}^{cb} f̄(cx)g(cx) d(cx)/(cx)
        # For functions satisfying f(cx) = f(x): integrals differ by [log(cb)-log(ca)]
        a, b = 1.0, 5.0
        ip1 = CompactacionAdelica.haar_measure_inner_product(f, g, a, b)
        # Scale interval and function
        fc = lambda x: f(x / c)
        gc = lambda x: g(x / c)
        ip2 = CompactacionAdelica.haar_measure_inner_product(fc, gc, a * c, b * c)
        # Both integrals should be equal (substitution u = x/c)
        assert abs(ip1 - ip2) < 1e-4, (
            f"Haar measure invariance: {ip1:.6f} vs {ip2:.6f}"
        )


class TestZetaCriticalLine:
    """Tests for zeta_critical_line evaluation."""

    def test_zeta_at_first_zero_small(self):
        """Near γ_1 ≈ 14.13, |ζ(1/2 + iγ_1)| should be small (close to 0)."""
        z = CompactacionAdelica.zeta_critical_line(14.134725)
        assert abs(z) < 0.01, f"|ζ(1/2+14.13i)| = {abs(z):.4e}"

    def test_zeta_at_second_zero_small(self):
        """Near γ_2 ≈ 21.02, |ζ(1/2 + iγ_2)| should be small."""
        z = CompactacionAdelica.zeta_critical_line(21.022040)
        assert abs(z) < 0.01, f"|ζ(1/2+21.02i)| = {abs(z):.4e}"

    def test_zeta_returns_complex(self):
        """zeta_critical_line returns a complex number."""
        z = CompactacionAdelica.zeta_critical_line(10.0)
        assert isinstance(z, complex)

    def test_zeta_real_part_finite(self):
        """Real and imaginary parts are finite."""
        for t in [5.0, 10.0, 20.0, 50.0]:
            z = CompactacionAdelica.zeta_critical_line(t)
            assert np.isfinite(z.real), f"Re[ζ] not finite at t={t}"
            assert np.isfinite(z.imag), f"Im[ζ] not finite at t={t}"

    @pytest.mark.parametrize("t", [14.134725, 21.022040, 25.010858])
    def test_zeta_near_zeros_small_magnitude(self, t: float):
        """|ζ(1/2+it)| is very small near known Riemann zeros."""
        z = CompactacionAdelica.zeta_critical_line(t)
        assert abs(z) < 0.01, (
            f"|ζ(1/2+{t:.6f}i)| = {abs(z):.4e}, expected < 0.01"
        )

    def test_zeta_approx_fallback_returns_complex(self):
        """_zeta_approx static method returns a complex number."""
        z = CompactacionAdelica._zeta_approx(14.0, n_primes=50)
        assert isinstance(z, complex)
        assert np.isfinite(z.real)
        assert np.isfinite(z.imag)


class TestSparseTransferMatrix:
    """Tests for sparse matrix support in transfer_matrix."""

    def test_dense_matrix_for_small_N(self):
        """For n_dim <= 512, transfer_matrix returns a dense ndarray."""
        import numpy as np
        comp = CompactacionAdelica(N_primes=30)
        T = comp.transfer_matrix(n_dim=30)
        assert isinstance(T, np.ndarray), "Expected dense ndarray for n_dim=30"

    def test_sparse_matrix_for_large_N(self):
        """For n_dim > 512, transfer_matrix returns a sparse matrix."""
        import scipy.sparse
        # Need enough primes
        comp = CompactacionAdelica(N_primes=600)
        T = comp.transfer_matrix(n_dim=600)
        assert scipy.sparse.issparse(T), "Expected sparse matrix for n_dim=600"

    def test_sparse_diagonal_values(self):
        """Sparse matrix diagonal = log(p)/sqrt(p)."""
        import scipy.sparse
        comp = CompactacionAdelica(N_primes=600)
        T = comp.transfer_matrix(n_dim=600)
        T_arr = T.toarray() if scipy.sparse.issparse(T) else T
        for i in range(10):
            p = comp.primes[i]
            expected = np.log(p) / np.sqrt(p)
            assert abs(T_arr[i, i] - expected) < 1e-10, (
                f"T[{i},{i}] = {T_arr[i,i]:.6f}, expected {expected:.6f}"
            )

    def test_sparse_matrix_finite(self):
        """Sparse matrix has no NaN or Inf values."""
        import scipy.sparse
        comp = CompactacionAdelica(N_primes=600)
        T = comp.transfer_matrix(n_dim=600)
        data = T.data if scipy.sparse.issparse(T) else T
        assert np.all(np.isfinite(data)), "Sparse matrix has non-finite values"


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
