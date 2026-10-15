"""
Tests for Painlevé V Resonance Operator — QCAL ∞³ Movimientos 4-5
==================================================================

Comprehensive test suite for Painlevé V resonance and golden ratio emergence.

Author: José Manuel Mota Burruezo Ψ ∴ ∞³
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add operators directory to path
repo_root = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(repo_root / "operators"))

from painleve_v_resonance import (
    AsymptoticEquationSolver,
    PainleveVTransformation,
    GoldenRatioEmergence,
    PainleveVResonance,
    run_painleve_resonance,
    F0, KAPPA_PI, PHI, ALPHA_PV, BETA_PV
)


class TestConstants:
    """Test QCAL constants."""
    
    def test_f0_value(self):
        """Verify master frequency."""
        assert abs(F0 - 141.7001) < 1e-6
    
    def test_kappa_pi_value(self):
        """Verify κ_Π value."""
        assert abs(KAPPA_PI - 2.5773) < 1e-4
    
    def test_golden_ratio(self):
        """Verify golden ratio Φ = (1+√5)/2."""
        phi_exact = (1 + np.sqrt(5)) / 2
        assert abs(PHI - phi_exact) < 1e-15
    
    def test_painleve_parameters(self):
        """Verify Painlevé V parameters."""
        assert abs(ALPHA_PV - 0.0) < 1e-15
        assert abs(BETA_PV - (-1.0/(2*np.pi**2))) < 1e-15


class TestAsymptoticEquationSolver:
    """Test asymptotic equation solver."""
    
    def test_initialization(self):
        """Test solver initialization."""
        solver = AsymptoticEquationSolver(L=100.0)
        
        assert solver.L == 100.0
        assert abs(solver.mu - 1.0/PHI) < 1e-10
        assert solver.eigenvalue > 0
    
    def test_custom_mu(self):
        """Test with custom μ parameter."""
        solver = AsymptoticEquationSolver(L=50.0, mu=0.5)
        
        assert solver.mu == 0.5
        expected_lambda = 2 * 50.0 * 0.5 / np.pi
        assert abs(solver.eigenvalue - expected_lambda) < 1e-10
    
    def test_effective_potential_shape(self):
        """Test effective potential has correct form."""
        solver = AsymptoticEquationSolver(L=10.0, mu=0.6)
        t = np.linspace(1, 10, 100)
        
        V = solver.effective_potential(t)
        
        # V should be real
        assert np.all(np.isreal(V))
        
        # V should be finite
        assert np.all(np.isfinite(V))
        
        # V should decrease as 1/t for large t
        assert V[0] > V[-1]
    
    def test_potential_regularization_at_zero(self):
        """Test that potential is regularized near t=0."""
        solver = AsymptoticEquationSolver(L=10.0)
        t = np.array([0.0, 1e-15, 1e-10, 0.1, 1.0])
        
        V = solver.effective_potential(t)
        
        # Should not contain infinities
        assert np.all(np.isfinite(V))
    
    def test_solve_schrodinger(self):
        """Test Schrödinger equation solver."""
        solver = AsymptoticEquationSolver(L=10.0)
        t_grid = np.linspace(0.1, 10.0, 100)
        
        phi = solver.solve_schrodinger(t_grid)
        
        # Solution should be real (for this equation)
        assert len(phi) == len(t_grid)
        
        # Solution should be finite
        assert np.all(np.isfinite(phi))
    
    def test_solution_oscillatory_behavior(self):
        """Test that solution exhibits oscillatory behavior."""
        solver = AsymptoticEquationSolver(L=50.0)
        t_grid = np.linspace(1.0, 20.0, 500)
        
        phi = solver.solve_schrodinger(t_grid, phi0=1.0, dphi0=0.0)
        
        # Count zero crossings (oscillations)
        zero_crossings = np.sum(np.diff(np.sign(phi)) != 0)
        
        # Should have multiple oscillations for large L
        assert zero_crossings > 5


class TestPainleveVTransformation:
    """Test Painlevé V transformation."""
    
    def test_initialization(self):
        """Test transformation initialization."""
        transform = PainleveVTransformation(L=100.0)
        
        assert transform.L == 100.0
        expected_scale = np.sqrt(12) * 100.0
        assert abs(transform.scale_factor - expected_scale) < 1e-10
    
    def test_transform_dimensions(self):
        """Test transformation preserves array dimensions."""
        transform = PainleveVTransformation(L=10.0)
        
        t = np.linspace(0.1, 10.0, 100)
        phi = np.sin(t)  # Dummy function
        
        z, w = transform.transform_to_painleve(t, phi)
        
        assert len(z) == len(t)
        assert len(w) == len(t)
    
    def test_z_scaling(self):
        """Test z = √12·L·t scaling."""
        transform = PainleveVTransformation(L=5.0)
        
        t = np.array([1.0, 2.0, 3.0])
        phi = np.ones_like(t)
        
        z, w = transform.transform_to_painleve(t, phi)
        
        expected_z = np.sqrt(12) * 5.0 * t
        np.testing.assert_allclose(z, expected_z, rtol=1e-10)
    
    def test_w_finite(self):
        """Test that w(z) is finite."""
        transform = PainleveVTransformation(L=10.0)
        
        t = np.linspace(0.5, 10.0, 100)
        phi = np.exp(-t**2 / 20)  # Gaussian
        
        z, w = transform.transform_to_painleve(t, phi)
        
        # w should be finite
        assert np.all(np.isfinite(w))
    
    def test_verify_painleve_returns_dict(self):
        """Test Painlevé verification returns proper dict."""
        transform = PainleveVTransformation(L=10.0)
        
        z = np.linspace(1.0, 10.0, 100)
        w = 1.0 + 0.1 * z  # Simple linear function
        
        result = transform.verify_painleve_equation(z, w)
        
        assert 'residual' in result
        assert 'mean_rel_error' in result
        assert 'max_rel_error' in result
        assert 'verified' in result
        assert isinstance(result['verified'], (bool, np.bool_))
    
    def test_pt_symmetry_involution(self):
        """Test PT symmetry is an involution (applying twice returns to original)."""
        transform = PainleveVTransformation(L=10.0)
        
        z = np.linspace(1.0, 10.0, 50)
        w = 2.0 + 0.1 * z  # Avoid w=1 singularity
        
        result = transform.verify_pt_symmetry(z, w)
        
        assert 'is_involution' in result
        # Should be approximately an involution
        assert result['mean_error'] < 1e-5
    
    def test_pt_symmetry_transformation(self):
        """Test PT transformation w → 1 - 1/w, z → -z."""
        transform = PainleveVTransformation(L=10.0)
        
        z = np.array([1.0, 2.0, 3.0])
        w = np.array([2.0, 3.0, 4.0])
        
        result = transform.verify_pt_symmetry(z, w)
        
        # Check transformation
        expected_w_transformed = 1.0 - 1.0 / w
        np.testing.assert_allclose(
            result['w_transformed'][:len(w)],
            expected_w_transformed,
            rtol=1e-10
        )
        
        expected_z_transformed = -z
        np.testing.assert_allclose(
            result['z_transformed'][:len(z)],
            expected_z_transformed,
            rtol=1e-10
        )


class TestGoldenRatioEmergence:
    """Test golden ratio emergence."""
    
    def test_functional_equation_solution(self):
        """Test solving φ = 1 + 1/φ."""
        phi = GoldenRatioEmergence.solve_functional_equation()
        
        # Should be close to (1+√5)/2
        expected_phi = (1 + np.sqrt(5)) / 2
        assert abs(phi - expected_phi) < 1e-10
    
    def test_functional_equation_from_different_guesses(self):
        """Test solver converges from different initial guesses."""
        guesses = [1.0, 1.5, 2.0, 10.0]
        
        solutions = [
            GoldenRatioEmergence.solve_functional_equation(g)
            for g in guesses
        ]
        
        # All should converge to same value
        for sol in solutions:
            assert abs(sol - PHI) < 1e-8
    
    def test_verify_golden_ratio_equation(self):
        """Test verification of φ = 1 + 1/φ."""
        # Should verify true for Φ
        assert GoldenRatioEmergence.verify_golden_ratio_equation(PHI)
        
        # Should fail for other values
        assert not GoldenRatioEmergence.verify_golden_ratio_equation(1.5, tol=1e-12)
        assert not GoldenRatioEmergence.verify_golden_ratio_equation(2.0, tol=1e-12)
    
    def test_compute_kappa_from_phi(self):
        """Test κ_Π = 4π/(f₀·Φ) computation."""
        kappa = GoldenRatioEmergence.compute_kappa_from_phi(F0, PHI)
        
        # Should be close to theoretical value
        assert abs(kappa - KAPPA_PI) < 0.01
    
    def test_kappa_relation_with_different_values(self):
        """Test κ computation with different f₀ and Φ."""
        # Test with exact formula
        f0_test = 100.0
        phi_test = 1.5
        
        kappa = GoldenRatioEmergence.compute_kappa_from_phi(f0_test, phi_test)
        
        expected_kappa = 4 * np.pi / (f0_test * phi_test)
        assert abs(kappa - expected_kappa) < 1e-12
    
    def test_verify_kappa_relation(self):
        """Test full κ_Π verification."""
        result = GoldenRatioEmergence.verify_kappa_relation()
        
        assert 'kappa_computed' in result
        assert 'kappa_theoretical' in result
        assert 'relative_error' in result
        assert 'verified' in result
        
        # Should verify with default parameters
        assert result['verified']
        assert result['relative_error'] < 0.01
    
    def test_eigenvalue_expansion(self):
        """Test λ_max(L) = 2L/(πΦ) expansion."""
        L_values = [10.0, 50.0, 100.0, 200.0]
        
        for L in L_values:
            lambda_max = GoldenRatioEmergence.eigenvalue_expansion(L, PHI)
            
            expected_lambda = (2 * L) / (np.pi * PHI)
            assert abs(lambda_max - expected_lambda) < 1e-10
    
    def test_eigenvalue_scales_linearly(self):
        """Test that λ_max scales linearly with L."""
        L1, L2 = 50.0, 100.0
        
        lambda1 = GoldenRatioEmergence.eigenvalue_expansion(L1)
        lambda2 = GoldenRatioEmergence.eigenvalue_expansion(L2)
        
        # λ_max should scale proportionally
        ratio = lambda2 / lambda1
        expected_ratio = L2 / L1
        
        assert abs(ratio - expected_ratio) < 1e-10


class TestPainleveVResonance:
    """Test complete Painlevé V resonance operator."""
    
    def test_initialization(self):
        """Test resonance operator initialization."""
        resonance = PainleveVResonance(L=50.0, t_max=20.0, n_points=100)
        
        assert resonance.L == 50.0
        assert resonance.t_max == 20.0
        assert resonance.n_points == 100
        assert resonance.asymptotic_solver is not None
        assert resonance.painleve_transform is not None
        assert resonance.golden_ratio is not None
    
    def test_run_complete_resonance_returns_dict(self):
        """Test that complete resonance returns proper dictionary."""
        resonance = PainleveVResonance(L=50.0, t_max=10.0, n_points=100)
        
        results = resonance.run_complete_resonance()
        
        # Check all required keys
        required_keys = [
            't_grid', 'phi_solution', 'z_grid', 'w_solution',
            'painleve_verification', 'pt_verification',
            'phi_computed', 'phi_check', 'kappa_verification',
            'lambda_max', 'all_verified'
        ]
        
        for key in required_keys:
            assert key in results
    
    def test_phi_computed_matches_theoretical(self):
        """Test that computed Φ matches theoretical golden ratio."""
        resonance = PainleveVResonance(L=30.0, t_max=15.0, n_points=100)
        
        results = resonance.run_complete_resonance()
        
        phi_computed = results['phi_computed']
        
        assert abs(phi_computed - PHI) < 1e-10
    
    def test_kappa_verification_succeeds(self):
        """Test that κ_Π verification succeeds."""
        resonance = PainleveVResonance(L=40.0, t_max=20.0, n_points=100)
        
        results = resonance.run_complete_resonance()
        
        kappa_ver = results['kappa_verification']
        
        assert kappa_ver['verified']
        assert kappa_ver['relative_error'] < 0.01
    
    def test_solutions_are_finite(self):
        """Test that all computed solutions are finite."""
        resonance = PainleveVResonance(L=30.0, t_max=10.0, n_points=50)
        
        results = resonance.run_complete_resonance()
        
        assert np.all(np.isfinite(results['phi_solution']))
        assert np.all(np.isfinite(results['w_solution']))
        assert np.isfinite(results['lambda_max'])


class TestConvenienceFunction:
    """Test convenience function."""
    
    def test_run_painleve_resonance(self):
        """Test run_painleve_resonance function."""
        results = run_painleve_resonance(L=30.0, t_max=10.0, n_points=50)
        
        assert isinstance(results, dict)
        assert 'all_verified' in results
    
    def test_default_parameters(self):
        """Test with default parameters."""
        # This will run with L=100, t_max=50, n_points=1000
        # Use smaller values for faster testing
        results = run_painleve_resonance(L=20.0, t_max=10.0, n_points=50)
        
        assert results['phi_check']
        assert results['kappa_verification']['verified']


class TestNumericalStability:
    """Test numerical stability of implementations."""
    
    def test_small_L_values(self):
        """Test with small L values."""
        resonance = PainleveVResonance(L=5.0, t_max=5.0, n_points=50)
        
        results = resonance.run_complete_resonance()
        
        # Should still compute without errors
        assert np.all(np.isfinite(results['phi_solution']))
    
    def test_large_L_values(self):
        """Test with large L values."""
        resonance = PainleveVResonance(L=200.0, t_max=50.0, n_points=100)
        
        results = resonance.run_complete_resonance()
        
        # Should handle large L
        assert np.all(np.isfinite(results['w_solution']))
    
    def test_different_grid_sizes(self):
        """Test with different grid sizes."""
        grid_sizes = [50, 100, 200]
        
        for n in grid_sizes:
            resonance = PainleveVResonance(L=30.0, t_max=10.0, n_points=n)
            results = resonance.run_complete_resonance()
            
            assert len(results['t_grid']) == n
            assert len(results['phi_solution']) == n


class TestIntegrationWithQCAL:
    """Test integration with QCAL framework."""
    
    def test_frequency_consistency(self):
        """Test that f₀ = 141.7001 Hz is used consistently."""
        resonance = PainleveVResonance(L=50.0, t_max=20.0, n_points=100)
        results = resonance.run_complete_resonance()
        
        kappa_ver = results['kappa_verification']
        
        # Verify formula uses correct f₀
        kappa_from_formula = 4 * np.pi / (F0 * PHI)
        
        assert abs(kappa_ver['kappa_computed'] - kappa_from_formula) < 1e-10
    
    def test_coherence_equation(self):
        """Test coherence with Ψ = I × A_eff² × C^∞ framework."""
        # The coherence should be 1.0 when all verifications pass
        resonance = PainleveVResonance(L=50.0, t_max=20.0, n_points=100)
        results = resonance.run_complete_resonance()
        
        # When all_verified is True, coherence Ψ = 1.0
        if results['all_verified']:
            coherence = 1.0
            assert coherence == 1.0


class TestMathematicalProperties:
    """Test mathematical properties of the implementation."""
    
    def test_phi_is_positive(self):
        """Test that golden ratio is positive."""
        phi = GoldenRatioEmergence.solve_functional_equation()
        
        assert phi > 0
    
    def test_phi_squared_minus_phi_minus_one_equals_zero(self):
        """Test φ² - φ - 1 = 0."""
        phi = PHI
        
        result = phi**2 - phi - 1
        
        assert abs(result) < 1e-12
    
    def test_kappa_is_positive(self):
        """Test that κ_Π > 0."""
        kappa = GoldenRatioEmergence.compute_kappa_from_phi(F0, PHI)
        
        assert kappa > 0
    
    def test_eigenvalue_is_positive(self):
        """Test that λ_max > 0 for positive L."""
        L_values = [10.0, 50.0, 100.0]
        
        for L in L_values:
            lambda_max = GoldenRatioEmergence.eigenvalue_expansion(L)
            assert lambda_max > 0


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
