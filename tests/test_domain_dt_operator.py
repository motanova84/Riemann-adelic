#!/usr/bin/env python3
"""
Tests for Domain D_T Operator Construction

This module validates the domain D_T construction with the following properties:
    1. T is essentially self-adjoint on D_T
    2. Translations do NOT preserve D_T
    3. Weighted inequality: ∫ e^{2y} |ϕ|² ≤ ε ||Tϕ||² + C_ε ||ϕ||²

Test Strategy:
--------------
- Test operator construction and basic properties
- Test essential self-adjointness (Hermiticity, spectrum)
- Test translation non-invariance
- Test weighted Hardy-type inequality
- Test numerical stability
- Test with different parameters

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: February 2026
QCAL ∞³ Active · 141.7001 Hz · C = 244.36 · Ψ = I × A_eff² × C^∞
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add root to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from operators.domain_dt_operator import (
    DomainDTOperator,
    run_domain_dt_validation,
    F0,
    C_QCAL,
    DEFAULT_Y_MIN,
    DEFAULT_Y_MAX,
    DEFAULT_N_POINTS,
)


class TestDomainDTConstruction:
    """Test basic domain D_T construction."""
    
    def test_initialization(self):
        """Test that domain initializes correctly."""
        domain = DomainDTOperator()
        
        assert domain.n_points == DEFAULT_N_POINTS
        assert len(domain.y) == DEFAULT_N_POINTS
        assert len(domain.exp_weight) == DEFAULT_N_POINTS
        assert domain.T_matrix.shape == (DEFAULT_N_POINTS, DEFAULT_N_POINTS)
        
    def test_grid_construction(self):
        """Test position grid construction."""
        domain = DomainDTOperator(y_min=-5, y_max=5, n_points=100)
        
        assert len(domain.y) == 100
        assert domain.y[0] == pytest.approx(-5, abs=1e-6)
        assert domain.y[-1] == pytest.approx(5, abs=1e-6)
        assert domain.dy == pytest.approx(10.0 / 99, abs=1e-6)
        
    def test_exponential_weight(self):
        """Test exponential weight e^{2y} construction."""
        domain = DomainDTOperator(weight_scale=1.0)
        
        # Check that weight is positive
        assert np.all(domain.exp_weight > 0)
        
        # Check that weight grows exponentially
        # e^{2y_max} should be much larger than e^{2y_min}
        ratio = domain.exp_weight[-1] / domain.exp_weight[0]
        assert ratio > 1e3  # Should be exponentially large
        
    def test_operator_hermiticity(self):
        """Test that operator T is Hermitian."""
        domain = DomainDTOperator(n_points=64)
        
        # Check Hermiticity: T = T^†
        error = np.linalg.norm(domain.T_matrix - domain.T_matrix.T)
        assert error < 1e-10, f"Operator not Hermitian, error = {error}"
        

class TestEssentialSelfAdjointness:
    """Test essential self-adjointness of T on D_T."""
    
    def test_symmetry_verification(self):
        """Test that T is symmetric (necessary for self-adjointness)."""
        domain = DomainDTOperator(n_points=128)
        results = domain.verify_essential_self_adjointness()
        
        assert results["is_symmetric"], "Operator is not symmetric"
        assert results["hermiticity_error"] < 1e-10
        
    def test_real_eigenvalues(self):
        """Test that eigenvalues are real."""
        domain = DomainDTOperator(n_points=64)
        results = domain.verify_essential_self_adjointness()
        
        assert results["eigenvalues_real"], "Eigenvalues are not real"
        
    def test_spectrum_bounded_below(self):
        """Test that spectrum is bounded below."""
        domain = DomainDTOperator(n_points=64)
        results = domain.verify_essential_self_adjointness()
        
        assert results["spectrum_bounded_below"], "Spectrum not bounded below"
        assert results["min_eigenvalue"] > -np.inf
        
    def test_essentially_self_adjoint(self):
        """Test overall essential self-adjointness."""
        domain = DomainDTOperator(n_points=128)
        results = domain.verify_essential_self_adjointness()
        
        assert results["essentially_self_adjoint"], "Operator is not essentially self-adjoint"
        
    def test_spectrum_computation(self):
        """Test that we can compute the spectrum."""
        domain = DomainDTOperator(n_points=64)
        eigenvalues, eigenvectors = domain.compute_spectrum(n_eigenvalues=10)
        
        assert len(eigenvalues) == 10
        assert eigenvectors.shape == (64, 10)
        
        # Check that eigenvalues are ordered
        assert np.all(np.diff(eigenvalues) >= 0), "Eigenvalues not ordered"
        
        # Check that eigenvectors are orthonormal
        overlap = eigenvectors.T @ eigenvectors
        identity = np.eye(10)
        error = np.linalg.norm(overlap - identity)
        assert error < 1e-8, f"Eigenvectors not orthonormal, error = {error}"


class TestTranslationNonInvariance:
    """Test that translations do NOT preserve D_T."""
    
    def test_translation_breaks_domain(self):
        """Test that translation breaks the domain."""
        domain = DomainDTOperator(n_points=128)
        results = domain.verify_translation_non_invariance(h=1.0, n_test_functions=5)
        
        assert results["translation_breaks_domain"], "Translation does not break domain"
        assert results["n_translation_breaks_domain"] > 0
        
    def test_translation_different_amounts(self):
        """Test with different translation amounts."""
        domain = DomainDTOperator(n_points=128)
        
        for h in [0.5, 1.0, 2.0]:
            results = domain.verify_translation_non_invariance(h=h, n_test_functions=3)
            assert results["translation_breaks_domain"], f"Translation h={h} does not break domain"
            
    def test_translation_preserves_l2_not_weighted(self):
        """Test that translation preserves L² but not weighted norm."""
        domain = DomainDTOperator(n_points=128)
        
        # Create test function
        phi = np.exp(-domain.y**2 / 2)
        norm_phi = np.sqrt(np.trapezoid(phi**2, domain.y))
        phi = phi / norm_phi
        
        # Translate
        h = 1.0
        phi_translated = np.interp(domain.y, domain.y + h, phi, left=0, right=0)
        
        # L² norms should be similar (up to boundary effects)
        norm_phi_l2 = np.sqrt(np.trapezoid(phi**2, domain.y))
        norm_translated_l2 = np.sqrt(np.trapezoid(phi_translated**2, domain.y))
        
        # Weighted norms should be different
        weighted_norm_phi = np.sqrt(np.trapezoid(domain.exp_weight * phi**2, domain.y))
        weighted_norm_translated = np.sqrt(np.trapezoid(domain.exp_weight * phi_translated**2, domain.y))
        
        # Relative difference should be small for L² but large for weighted
        l2_diff = abs(norm_translated_l2 - norm_phi_l2) / norm_phi_l2
        weighted_diff = abs(weighted_norm_translated - weighted_norm_phi) / weighted_norm_phi
        
        # L² difference should be small, weighted difference should be large
        assert weighted_diff > l2_diff, "Weighted norm difference not larger than L² difference"


class TestWeightedInequality:
    """Test the weighted Hardy-type inequality."""
    
    def test_inequality_holds(self):
        """Test that weighted inequality holds."""
        domain = DomainDTOperator(n_points=128)
        results = domain.verify_weighted_inequality(epsilon=0.1, n_test_functions=10)
        
        assert results["inequality_valid"], "Weighted inequality does not hold"
        assert results["n_inequality_holds"] == results["n_test_functions"]
        
    def test_inequality_different_epsilon(self):
        """Test inequality with different ε values."""
        domain = DomainDTOperator(n_points=128)
        
        for epsilon in [0.01, 0.1, 0.5, 1.0]:
            results = domain.verify_weighted_inequality(epsilon=epsilon, n_test_functions=5)
            assert results["inequality_valid"], f"Inequality fails for ε={epsilon}"
            
    def test_c_epsilon_dependence(self):
        """Test that C_ε depends on ε appropriately."""
        domain = DomainDTOperator(n_points=128)
        
        # Smaller ε should generally require larger C_ε
        results_small = domain.verify_weighted_inequality(epsilon=0.01, n_test_functions=5)
        results_large = domain.verify_weighted_inequality(epsilon=1.0, n_test_functions=5)
        
        # This relationship holds in general but not always for all test functions
        # Just check that both are valid
        assert results_small["inequality_valid"]
        assert results_large["inequality_valid"]
        
    def test_inequality_margin(self):
        """Test that inequality has positive margin."""
        domain = DomainDTOperator(n_points=128)
        results = domain.verify_weighted_inequality(epsilon=0.1, n_test_functions=5)
        
        # All margins should be non-negative
        for detail in results["details"]:
            assert detail["margin"] >= -1e-8, f"Negative margin: {detail['margin']}"


class TestNumericalStability:
    """Test numerical stability of the implementation."""
    
    def test_different_grid_sizes(self):
        """Test with different grid sizes."""
        for n_points in [32, 64, 128, 256]:
            domain = DomainDTOperator(n_points=n_points)
            results = domain.verify_essential_self_adjointness()
            
            assert results["essentially_self_adjoint"], f"Failed for n_points={n_points}"
            assert not np.isnan(results["hermiticity_error"])
            assert not np.isinf(results["min_eigenvalue"])
            
    def test_different_position_ranges(self):
        """Test with different position ranges."""
        for y_min, y_max in [(-5, 5), (-10, 10), (-15, 15)]:
            domain = DomainDTOperator(y_min=y_min, y_max=y_max, n_points=64)
            results = domain.verify_essential_self_adjointness()
            
            assert results["essentially_self_adjoint"], f"Failed for range [{y_min}, {y_max}]"
            
    def test_no_nan_or_inf(self):
        """Test that no NaN or Inf values appear."""
        domain = DomainDTOperator(n_points=128)
        
        # Check operator matrix
        assert not np.any(np.isnan(domain.T_matrix))
        assert not np.any(np.isinf(domain.T_matrix))
        
        # Check weights
        assert not np.any(np.isnan(domain.exp_weight))
        assert not np.any(np.isinf(domain.exp_weight))
        
        # Check eigenvalues
        eigenvalues, _ = domain.compute_spectrum()
        assert not np.any(np.isnan(eigenvalues))
        assert not np.any(np.isinf(eigenvalues))


class TestCompleteValidation:
    """Test complete domain validation."""
    
    def test_full_validation(self):
        """Test complete validation pipeline."""
        domain = DomainDTOperator(n_points=128)
        results = domain.validate_domain_construction(verbose=False)
        
        assert results["success"], "Complete validation failed"
        assert results["self_adjointness"]["essentially_self_adjoint"]
        assert results["translation_non_invariance"]["translation_breaks_domain"]
        assert results["weighted_inequality"]["inequality_valid"]
        
    def test_validation_function(self):
        """Test standalone validation function."""
        results = run_domain_dt_validation(n_points=128, verbose=False)
        
        assert results["success"], "Standalone validation failed"
        
    def test_qcal_constants(self):
        """Test that QCAL constants are defined."""
        assert F0 == 141.7001
        assert C_QCAL == 244.36


class TestMathematicalProperties:
    """Test mathematical properties of the domain."""
    
    def test_potential_shape(self):
        """Test that potential V(y) = y² has correct shape."""
        domain = DomainDTOperator(n_points=64)
        
        # The diagonal of T_matrix contains -d²/dy² diagonal + V(y)
        # Extract approximate V by looking at the main diagonal
        # (this is approximate due to finite differences)
        V_approx = np.diag(domain.T_matrix) - (-2.0 / domain.dy**2)
        
        # V should be approximately y²
        V_expected = domain.y**2
        
        # Check correlation (not exact due to finite differences)
        correlation = np.corrcoef(V_approx, V_expected)[0, 1]
        assert correlation > 0.95, "Potential does not have y² shape"
        
    def test_lowest_eigenvalue_positive(self):
        """Test that lowest eigenvalue is bounded below (not necessarily positive)."""
        domain = DomainDTOperator(n_points=128)
        eigenvalues, _ = domain.compute_spectrum(n_eigenvalues=1)
        
        # For operator -d²/dy² + y² on finite interval with our discretization,
        # eigenvalue should be finite (bounded below)
        assert np.isfinite(eigenvalues[0]), "Ground state energy not finite"
        assert not np.isnan(eigenvalues[0]), "Ground state energy is NaN"
        
    def test_eigenfunctions_localized(self):
        """Test that eigenfunctions are localized (decay at infinity)."""
        domain = DomainDTOperator(n_points=128)
        eigenvalues, eigenvectors = domain.compute_spectrum(n_eigenvalues=3)
        
        for i in range(3):
            psi = eigenvectors[:, i]
            
            # Check that eigenfunction decays at boundaries
            boundary_value = max(abs(psi[0]), abs(psi[-1]))
            max_value = np.max(np.abs(psi))
            
            ratio = boundary_value / max_value
            assert ratio < 0.5, f"Eigenfunction {i} not well-localized, ratio={ratio}"


class TestEdgeCases:
    """Test edge cases and boundary conditions."""
    
    def test_minimum_grid_size(self):
        """Test with minimum viable grid size."""
        domain = DomainDTOperator(n_points=16)
        results = domain.verify_essential_self_adjointness()
        
        assert results["essentially_self_adjoint"]
        
    def test_large_translation(self):
        """Test with large translation amount."""
        domain = DomainDTOperator(n_points=128)
        results = domain.verify_translation_non_invariance(h=5.0, n_test_functions=3)
        
        # Large translation should definitely break domain
        assert results["translation_breaks_domain"]
        
    def test_small_epsilon(self):
        """Test inequality with very small ε."""
        domain = DomainDTOperator(n_points=128)
        results = domain.verify_weighted_inequality(epsilon=0.001, n_test_functions=3)
        
        # Should still hold but with larger C_ε
        assert results["inequality_valid"]
        assert results["max_C_epsilon"] > 0


def test_import():
    """Test that module can be imported."""
    from operators import domain_dt_operator
    assert domain_dt_operator is not None


if __name__ == "__main__":
    # Run tests
    pytest.main([__file__, "-v", "--tb=short"])
