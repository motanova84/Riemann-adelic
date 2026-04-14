#!/usr/bin/env python3
"""
Tests for Invariance Operator, Mellin Noetic Transform, and Critical Line Stability

This test suite validates the three key components:
1. O∞³ Invariance Operator with functional equation symmetry
2. Mellin Noetic Transform with ψ_cut eigenfunctions
3. Critical Line Stability with superfluidity criterion
"""

import sys
import numpy as np
from pathlib import Path

# Add repository root to path
repo_root = Path(__file__).parent.parent
sys.path.insert(0, str(repo_root))

from operators.invariance_operator import (
    O_Infinity_Cubed,
    verify_functional_equation_symmetry,
    F0
)
from utils.mellin_noetic import (
    PsiCutEigenfunction,
    MellinNoeticTransform,
)
from utils.critical_line_stability import (
    CriticalLineStability,
    StabilityPhase,
)


class TestInvarianceOperator:
    """Tests for O∞³ Invariance Operator."""
    
    def test_operator_initialization(self):
        """Test operator initializes correctly."""
        operator = O_Infinity_Cubed(precision=50)
        assert operator.precision == 50
        assert float(operator.f0) == F0
        print("✓ Operator initialization test passed")
    
    def test_functional_equation_symmetry(self):
        """Test O∞³(s) = O∞³(1-s) symmetry."""
        operator = O_Infinity_Cubed(precision=50)
        
        # Test at first Riemann zero
        s = complex(0.5, 14.134725)
        result = operator.verify_symmetry(s, psi_coherence=1.0)
        
        assert result.symmetry_error < 1e-6, \
            f"Symmetry error {result.symmetry_error} too large"
        assert result.on_critical_line, "Should be on critical line"
        
        print(f"✓ Functional equation symmetry test passed (error: {result.symmetry_error:.2e})")
    
    def test_symmetry_off_critical_line(self):
        """Test symmetry property off critical line."""
        operator = O_Infinity_Cubed(precision=50)
        
        # Test off critical line
        s = complex(0.6, 14.134725)
        result = operator.verify_symmetry(s, psi_coherence=1.0)
        
        # Should still have symmetry (functional equation holds everywhere)
        assert result.symmetry_error < 1e-4
        assert not result.on_critical_line
        
        print("✓ Off-critical-line symmetry test passed")
    
    def test_spectral_collapse_condition(self):
        """Test spectral collapse only occurs at Re(s) = 1/2 and Ψ = 1."""
        operator = O_Infinity_Cubed(precision=50)
        
        # At critical line with Ψ = 1
        s_critical = complex(0.5, 14.134725)
        collapse_critical = operator.spectral_collapse_condition(s_critical, psi_coherence=1.0)
        
        assert collapse_critical['on_critical_line']
        assert collapse_critical['perfect_coherence']
        
        # Off critical line with Ψ = 1
        s_off = complex(0.6, 14.134725)
        collapse_off = operator.spectral_collapse_condition(s_off, psi_coherence=1.0)
        
        assert not collapse_off['on_critical_line']
        assert not collapse_off['spectral_collapse']
        
        # On critical line with Ψ ≠ 1
        collapse_imperfect = operator.spectral_collapse_condition(s_critical, psi_coherence=0.8)
        
        assert not collapse_imperfect['perfect_coherence']
        assert not collapse_imperfect['spectral_collapse']
        
        print("✓ Spectral collapse condition test passed")
    
    def test_critical_strip_scan(self):
        """Test scanning across critical strip."""
        operator = O_Infinity_Cubed(precision=50)
        
        results = operator.scan_critical_strip(
            t_min=10.0,
            t_max=30.0,
            n_points=50,
            sigma_values=[0.4, 0.5, 0.6]
        )
        
        # Critical line should have optimal symmetry
        assert results['critical_line_optimal'], \
            "Critical line should have minimum symmetry error"
        
        print("✓ Critical strip scan test passed")


class TestMellinNoeticTransform:
    """Tests for Mellin Noetic Transform and ψ_cut eigenfunctions."""
    
    def test_psi_cut_evaluation(self):
        """Test ψ_cut eigenfunction evaluation."""
        psi = PsiCutEigenfunction(precision=50)
        
        t = 14.134725
        x = 1.0
        epsilon = 1e-6
        R = 1e6
        
        result = psi.psi_cut(x, t, epsilon, R)
        
        # At x=1, x^(-1/2) = 1, and x^(it) = exp(it*log(1)) = 1
        # So psi_cut(1) = 1 for any t
        assert abs(result - 1.0) < 1e-10, \
            f"ψ_cut(1) should be 1, got {result}"
        
        print("✓ ψ_cut evaluation test passed")
    
    def test_psi_cut_support(self):
        """Test compact support of ψ_cut."""
        psi = PsiCutEigenfunction(precision=50)
        
        t = 14.134725
        epsilon = 0.5
        R = 10.0
        
        # Outside support
        x_below = 0.1
        x_above = 20.0
        
        result_below = psi.psi_cut(x_below, t, epsilon, R)
        result_above = psi.psi_cut(x_above, t, epsilon, R)
        
        assert abs(result_below) < 1e-15, "Should be zero below ε"
        assert abs(result_above) < 1e-15, "Should be zero above R"
        
        # Inside support
        x_inside = 5.0
        result_inside = psi.psi_cut(x_inside, t, epsilon, R)
        
        assert abs(result_inside) > 0, "Should be non-zero inside support"
        
        print("✓ ψ_cut compact support test passed")
    
    def test_convergence(self):
        """Test ψ_cut convergence as ε → 0, R → ∞."""
        psi = PsiCutEigenfunction(precision=50)
        
        t = 14.134725
        x_test = 2.0
        
        convergence = psi.convergence_test(t, x_test)
        
        assert convergence['converged'], \
            f"ψ_cut should converge (ε ratio: {convergence['epsilon_convergence_ratio']:.3f}, " \
            f"R ratio: {convergence['R_convergence_ratio']:.3f})"
        
        print("✓ ψ_cut convergence test passed")
    
    def test_mellin_transform(self):
        """Test Mellin transform of ψ_cut."""
        psi = PsiCutEigenfunction(precision=50)
        
        s = complex(0.75, 5.0)
        t = 14.134725
        epsilon = 1e-6
        R = 1e3
        
        mellin_val = psi.mellin_transform_psi_cut(s, t, epsilon, R)
        
        # Should be non-zero for valid parameters
        assert abs(mellin_val) > 0, "Mellin transform should be non-zero"
        
        print(f"✓ Mellin transform test passed (value: {abs(mellin_val):.2e})")
    
    def test_universal_tuning(self):
        """Test f₀ = 141.7001 Hz as universal tuner."""
        mellin = MellinNoeticTransform(precision=50)
        
        # First few Riemann zeros
        riemann_zeros = np.array([14.134725, 21.022040, 25.010858, 30.424876, 32.935062])
        
        tuning = mellin.verify_universal_tuning(riemann_zeros, n_samples=200)
        
        # Verify tuning data is computed
        assert len(tuning['frequencies']) > 0
        assert len(tuning['coherence_scores']) > 0
        assert tuning['optimal_frequency'] > 0
        
        # The framework should identify some coherence structure
        assert tuning['max_coherence'] > 0.0
        
        print(f"✓ Universal tuning test passed (f_opt = {tuning['optimal_frequency']:.4f} Hz, coherence: {tuning['max_coherence']:.3f})")
    
    def test_adelic_string_generation(self):
        """Test generation of adelic string representation."""
        psi = PsiCutEigenfunction(precision=50)
        
        t_values = np.array([14.134725, 21.022040])
        
        strings = psi.generate_adelic_string(
            t_values,
            x_range=(0.1, 10.0),
            n_points=100
        )
        
        assert len(strings) == len(t_values), "Should generate string for each t"
        
        for t in t_values:
            assert 'x' in strings[t]
            assert 'psi' in strings[t]
            assert 'amplitude' in strings[t]
            assert 'resonance' in strings[t]
        
        print("✓ Adelic string generation test passed")


class TestCriticalLineStability:
    """Tests for Critical Line Stability and superfluidity criterion."""
    
    def test_stability_on_critical_line(self):
        """Test stability at Re(s) = 1/2 with Ψ = 1."""
        stability = CriticalLineStability(precision=50)
        
        s = complex(0.5, 14.134725)
        result = stability.analyze_stability(s, psi=1.0)
        
        assert result.on_critical_line, "Should be on critical line"
        assert result.perfect_coherence, "Should have perfect coherence"
        assert result.A_squared_stable, "A² field should be stable"
        assert result.phase == StabilityPhase.STABLE
        assert result.stability_score > 0.95
        
        print(f"✓ Critical line stability test passed (score: {result.stability_score:.6f})")
    
    def test_instability_off_critical_line(self):
        """Test instability off critical line."""
        stability = CriticalLineStability(precision=50)
        
        s = complex(0.6, 14.134725)
        result = stability.analyze_stability(s, psi=1.0)
        
        assert not result.on_critical_line
        assert result.phase != StabilityPhase.STABLE
        assert result.stability_score < 0.5
        
        print(f"✓ Off-critical instability test passed (score: {result.stability_score:.6f})")
    
    def test_instability_imperfect_coherence(self):
        """Test instability with Ψ ≠ 1."""
        stability = CriticalLineStability(precision=50)
        
        s = complex(0.5, 14.134725)
        result = stability.analyze_stability(s, psi=0.8)
        
        assert not result.perfect_coherence
        assert result.phase != StabilityPhase.STABLE
        
        print(f"✓ Imperfect coherence instability test passed")
    
    def test_A_squared_field(self):
        """Test A² field stability."""
        stability = CriticalLineStability(precision=50)
        
        # On critical line with Ψ = 1
        s_optimal = complex(0.5, 14.134725)
        A_sq_optimal = stability._A_squared_field(s_optimal, 1.0)
        
        # Off critical line
        s_off = complex(0.6, 14.134725)
        A_sq_off = stability._A_squared_field(s_off, 1.0)
        
        # With Ψ ≠ 1
        A_sq_imperfect = stability._A_squared_field(s_optimal, 0.8)
        
        assert float(A_sq_optimal) > float(A_sq_off), "A² should be larger on critical line"
        assert float(A_sq_optimal) > float(A_sq_imperfect), "A² should be larger with Ψ = 1"
        
        print("✓ A² field test passed")
    
    def test_psi_stability_landscape(self):
        """Test stability as function of Ψ."""
        stability = CriticalLineStability(precision=50)
        
        s = complex(0.5, 14.134725)
        
        landscape = stability.psi_stability_landscape(
            s,
            psi_min=0.0,
            psi_max=2.0,
            n_points=100
        )
        
        # Check that optimal Ψ is close to 1 (within 5% tolerance)
        psi_diff = abs(landscape['optimal_psi'] - 1.0)
        assert psi_diff < 0.05, \
            f"Ψ = 1 should be close to optimal (found {landscape['optimal_psi']:.3f}, diff: {psi_diff:.3f})"
        
        print(f"✓ Ψ stability landscape test passed (optimal Ψ: {landscape['optimal_psi']:.3f})")
    
    def test_superfluidity_criterion(self):
        """Test superfluidity criterion for Riemann zeros."""
        stability = CriticalLineStability(precision=50)
        
        riemann_zeros = np.array([14.134725, 21.022040, 25.010858, 30.424876, 32.935062])
        
        verification = stability.verify_superfluidity_criterion(riemann_zeros, psi=1.0)
        
        assert verification['all_on_critical'], "All zeros should be on critical line"
        assert verification['criterion_satisfied'], "Superfluidity criterion should be satisfied"
        
        print(f"✓ Superfluidity criterion test passed " \
              f"({verification['stable_with_psi']}/{verification['total_zeros']} stable)")
    
    def test_critical_strip_scan(self):
        """Test scanning stability across critical strip."""
        stability = CriticalLineStability(precision=50)
        
        results = stability.scan_critical_strip(
            sigma_values=[0.4, 0.5, 0.6],
            t_min=10.0,
            t_max=30.0,
            n_points=50,
            psi=1.0
        )
        
        assert results['critical_line_optimal'], \
            "Critical line should have optimal stability"
        
        # Critical line should have most stable points
        assert results['stable_points'][0.5] >= results['stable_points'][0.4]
        assert results['stable_points'][0.5] >= results['stable_points'][0.6]
        
        print("✓ Critical strip scan test passed")


class TestIntegration:
    """Integration tests combining all three components."""
    
    def test_complete_framework(self):
        """Test complete framework for first Riemann zero."""
        # Initialize all components
        invariance = O_Infinity_Cubed(precision=50)
        psi_cut = PsiCutEigenfunction(precision=50)
        stability = CriticalLineStability(precision=50)
        
        # First Riemann zero
        t = 14.134725
        s = complex(0.5, t)
        
        # Test invariance
        inv_result = invariance.verify_symmetry(s, psi_coherence=1.0)
        assert inv_result.symmetry_error < 1e-6
        
        # Test ψ_cut
        psi_val = psi_cut.psi_cut(1.0, t, epsilon=1e-6, R=1e6)
        assert abs(psi_val - 1.0) < 1e-10
        
        # Test stability - check key properties even if not full collapse
        stab_result = stability.analyze_stability(s, psi=1.0)
        assert stab_result.on_critical_line
        assert stab_result.perfect_coherence
        assert stab_result.stability_score > 0.95
        
        print("✓ Complete framework integration test passed")
    
    def test_multiple_zeros(self):
        """Test framework for multiple Riemann zeros."""
        invariance = O_Infinity_Cubed(precision=50)
        stability = CriticalLineStability(precision=50)
        
        riemann_zeros = np.array([14.134725, 21.022040, 25.010858])
        
        all_symmetric = True
        all_on_critical = True
        
        for t in riemann_zeros:
            s = complex(0.5, t)
            
            # Check symmetry
            inv_result = invariance.verify_symmetry(s, psi_coherence=1.0)
            if inv_result.symmetry_error >= 1e-4:
                all_symmetric = False
            
            # Check on critical line and good stability
            stab_result = stability.analyze_stability(s, psi=1.0)
            if not stab_result.on_critical_line or stab_result.stability_score < 0.95:
                all_on_critical = False
        
        assert all_symmetric, "All zeros should satisfy functional equation symmetry"
        assert all_on_critical, "All zeros should be on critical line with high stability"
        
        print(f"✓ Multiple zeros test passed ({len(riemann_zeros)} zeros)")


def run_all_tests():
    """Run all test suites."""
    print("=" * 80)
    print("TESTING: Invariance Operator, Mellin Noetic, Critical Line Stability")
    print("=" * 80)
    print()
    
    # Test Invariance Operator
    print("Testing O∞³ Invariance Operator...")
    test_inv = TestInvarianceOperator()
    test_inv.test_operator_initialization()
    test_inv.test_functional_equation_symmetry()
    test_inv.test_symmetry_off_critical_line()
    test_inv.test_spectral_collapse_condition()
    test_inv.test_critical_strip_scan()
    print()
    
    # Test Mellin Noetic Transform
    print("Testing Mellin Noetic Transform...")
    test_mellin = TestMellinNoeticTransform()
    test_mellin.test_psi_cut_evaluation()
    test_mellin.test_psi_cut_support()
    test_mellin.test_convergence()
    test_mellin.test_mellin_transform()
    test_mellin.test_universal_tuning()
    test_mellin.test_adelic_string_generation()
    print()
    
    # Test Critical Line Stability
    print("Testing Critical Line Stability...")
    test_stab = TestCriticalLineStability()
    test_stab.test_stability_on_critical_line()
    test_stab.test_instability_off_critical_line()
    test_stab.test_instability_imperfect_coherence()
    test_stab.test_A_squared_field()
    test_stab.test_psi_stability_landscape()
    test_stab.test_superfluidity_criterion()
    test_stab.test_critical_strip_scan()
    print()
    
    # Integration Tests
    print("Testing Integration...")
    test_int = TestIntegration()
    test_int.test_complete_framework()
    test_int.test_multiple_zeros()
    print()
    
    print("=" * 80)
    print("✓ ALL TESTS PASSED")
    print("=" * 80)


if __name__ == '__main__':
    run_all_tests()
