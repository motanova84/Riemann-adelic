"""
Tests for the Canonical System Impossibility Theorem

This module tests the theoretical impossibility of using Gamma function
as a spectral determinant for self-adjoint operators with positive real eigenvalues.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID: 0009-0002-1923-0773
"""

import pytest
import numpy as np
from operators.canonical_system_impossibility import (
    CanonicalSystemImpossibility,
    demonstrate_canonical_system_transformation,
    validate_impossibility_with_numerical_check
)


class TestCanonicalSystemImpossibility:
    """Test suite for the Γ-Impossibility theorem."""
    
    def test_initialization(self):
        """Test that the analyzer initializes correctly."""
        analyzer = CanonicalSystemImpossibility(n_poles=10)
        assert analyzer.n_poles == 10
        assert len(analyzer.gamma_poles) == 10
        assert np.all(analyzer.gamma_poles <= 0)
        assert analyzer.gamma_poles[0] == 0
        assert analyzer.gamma_poles[-1] == -9
    
    def test_real_argument_analysis(self):
        """Test analysis of Γ(a + λ) for real λ."""
        analyzer = CanonicalSystemImpossibility(n_poles=10)
        result = analyzer.analyze_real_argument(a=0.25)
        
        # Check structure
        assert 'argument_form' in result
        assert 'poles' in result
        assert 'are_real' in result
        assert 'conclusion' in result
        
        # Verify poles are real
        assert result['are_real'] is True
        
        # Verify poles are constants (independent of spectral parameter)
        # For a=0.25, poles should be at λ = -0.25, -1.25, -2.25, ...
        expected_poles = -0.25 - np.arange(10)
        np.testing.assert_array_almost_equal(result['poles'], expected_poles)
        
        # Verify conclusion indicates impossibility
        assert 'IMPOSSIBLE' in result['conclusion']
    
    def test_imaginary_argument_analysis(self):
        """Test analysis of Γ(a + iλ) for real λ."""
        analyzer = CanonicalSystemImpossibility(n_poles=10)
        result = analyzer.analyze_imaginary_argument(a=0.25)
        
        # Check structure
        assert 'argument_form' in result
        assert 'poles' in result
        assert 'are_real' in result
        
        # Verify poles are NOT real
        assert result['are_real'] is False
        
        # Verify poles are purely imaginary
        poles = result['poles']
        assert np.all(np.real(poles) == 0)
        assert np.all(np.imag(poles) != 0)
        
        # First pole should be at λ = i(-0.25) = -0.25i
        assert np.isclose(np.imag(poles[0]), -0.25)
        
        # Verify conclusion indicates impossibility
        assert 'IMPOSSIBLE' in result['conclusion']
    
    def test_sqrt_argument_analysis(self):
        """Test analysis of Γ(a + i·b·√λ) for real λ."""
        analyzer = CanonicalSystemImpossibility(n_poles=10)
        result = analyzer.analyze_sqrt_argument(a=0.25, b=0.5)
        
        # Check structure
        assert 'argument_form' in result
        assert 'poles' in result
        assert 'are_real' in result
        assert 'are_positive' in result
        
        # Verify poles are real
        assert result['are_real'] is True
        
        # Verify poles are NOT positive
        assert result['are_positive'] is False
        
        # Poles should be negative: λ = -(0.25 + n)²/0.5² = -4(0.25 + n)²
        poles = result['poles']
        assert np.all(poles < 0)
        
        # Verify conclusion indicates impossibility
        assert 'IMPOSSIBLE' in result['conclusion']
    
    def test_prove_impossibility_theorem(self):
        """Test the complete impossibility theorem proof."""
        analyzer = CanonicalSystemImpossibility(n_poles=10)
        theorem = analyzer.prove_impossibility_theorem()
        
        # Check theorem structure
        assert 'title' in theorem
        assert 'statement' in theorem
        assert 'scenarios' in theorem
        assert 'conclusion' in theorem
        
        # Verify all three scenarios are analyzed
        assert 'real_argument' in theorem['scenarios']
        assert 'imaginary_argument' in theorem['scenarios']
        assert 'sqrt_argument' in theorem['scenarios']
        
        # Verify theorem holds (impossibility is proven)
        assert theorem['conclusion']['theorem_holds'] is True
        
        # Verify summary explains all three failure modes
        summary = theorem['conclusion']['summary']
        assert 'Real argument' in summary
        assert 'Imaginary argument' in summary
        assert 'Square root argument' in summary
        
        # Verify implications are listed
        assert 'implications' in theorem['conclusion']
        assert len(theorem['conclusion']['implications']) >= 3
    
    def test_scenario_exhaustiveness(self):
        """Test that all three scenarios fail for different parameter values."""
        analyzer = CanonicalSystemImpossibility(n_poles=20)
        
        # Test multiple values of parameter a
        for a in [0.25, 0.5, 1.0, 2.0]:
            # Real argument always gives constants
            result_real = analyzer.analyze_real_argument(a=a)
            assert 'constant' in result_real['spectrum_type']
            
            # Imaginary argument always gives imaginary poles
            result_imag = analyzer.analyze_imaginary_argument(a=a)
            assert result_imag['are_real'] is False
            
            # Sqrt argument always gives negative poles
            for b in [0.5, 1.0, 2.0]:
                result_sqrt = analyzer.analyze_sqrt_argument(a=a, b=b)
                assert result_sqrt['are_positive'] is False
    
    def test_riemann_zeros_mismatch(self):
        """Test that Γ poles don't match Riemann zeros."""
        analyzer = CanonicalSystemImpossibility(n_poles=10)
        
        # First few Riemann zeros (imaginary parts)
        riemann_zeros_im = np.array([
            14.134725, 21.022040, 25.010858, 30.424876, 32.935062
        ])
        
        # Check that no Γ pole configuration matches these
        for a in [0.25, 0.5, 1.0]:
            # Imaginary argument gives poles at i(-a - n)
            gamma_poles_im = -a - np.arange(10)
            
            # These should not match Riemann zeros
            for rz in riemann_zeros_im:
                # No Γ pole should be close to any Riemann zero
                distances = np.abs(gamma_poles_im - rz)
                assert np.all(distances > 1.0)  # At least 1.0 apart
    
    def test_positive_spectrum_impossibility(self):
        """Test that no configuration gives positive real spectrum."""
        analyzer = CanonicalSystemImpossibility(n_poles=30)
        
        # Test various parameter combinations
        test_cases = [
            ('real', lambda: analyzer.analyze_real_argument(a=0.25)),
            ('real', lambda: analyzer.analyze_real_argument(a=0.5)),
            ('imaginary', lambda: analyzer.analyze_imaginary_argument(a=0.25)),
            ('imaginary', lambda: analyzer.analyze_imaginary_argument(a=0.5)),
            ('sqrt', lambda: analyzer.analyze_sqrt_argument(a=0.25, b=0.5)),
            ('sqrt', lambda: analyzer.analyze_sqrt_argument(a=0.5, b=1.0)),
        ]
        
        for case_type, analyzer_func in test_cases:
            result = analyzer_func()
            
            if case_type == 'real':
                # Real argument: poles are constants, not a spectrum
                assert 'constant' in result['spectrum_type'].lower()
            elif case_type == 'imaginary':
                # Imaginary argument: poles are not real
                assert not result['are_real']
            elif case_type == 'sqrt':
                # Sqrt argument: poles are not positive
                assert not result['are_positive']
                assert np.all(result['poles'] < 0)
    
    def test_demonstration_runs(self):
        """Test that the demonstration function runs without error."""
        # This should print the full transformation and theorem
        # Just check it doesn't crash
        import io
        import sys
        
        # Capture output
        old_stdout = sys.stdout
        sys.stdout = io.StringIO()
        
        try:
            demonstrate_canonical_system_transformation()
            output = sys.stdout.getvalue()
            
            # Check that key sections are present
            assert 'SCHRÖDINGER' in output
            assert 'CANONICAL SYSTEM' in output
            assert 'Γ-Impossibility' in output
            assert 'STEP 1' in output
            assert 'STEP 8' in output
            
        finally:
            sys.stdout = old_stdout
    
    def test_numerical_validation_runs(self):
        """Test that numerical validation runs without error."""
        import io
        import sys
        
        # Capture output
        old_stdout = sys.stdout
        sys.stdout = io.StringIO()
        
        try:
            validate_impossibility_with_numerical_check()
            output = sys.stdout.getvalue()
            
            # Check that validation content is present
            assert 'Riemann zeros' in output
            assert 'Γ vs Riemann' in output
            
        finally:
            sys.stdout = old_stdout
    
    def test_print_theorem_formatting(self):
        """Test that print_theorem produces well-formatted output."""
        import io
        import sys
        
        analyzer = CanonicalSystemImpossibility(n_poles=10)
        
        # Capture output
        old_stdout = sys.stdout
        sys.stdout = io.StringIO()
        
        try:
            analyzer.print_theorem()
            output = sys.stdout.getvalue()
            
            # Check formatting elements
            assert '='*80 in output  # Horizontal rules
            assert 'STATEMENT:' in output
            assert 'PROOF BY EXHAUSTION:' in output
            assert 'Scenario 1:' in output
            assert 'Scenario 2:' in output
            assert 'Scenario 3:' in output
            assert 'CONCLUSION:' in output
            assert 'IMPLICATIONS:' in output
            
        finally:
            sys.stdout = old_stdout
    
    @pytest.mark.parametrize("n_poles", [5, 10, 20, 50])
    def test_different_pole_counts(self, n_poles):
        """Test analyzer works with different numbers of poles."""
        analyzer = CanonicalSystemImpossibility(n_poles=n_poles)
        
        assert len(analyzer.gamma_poles) == n_poles
        
        # Theorem should hold regardless of number of poles
        theorem = analyzer.prove_impossibility_theorem()
        assert theorem['conclusion']['theorem_holds'] is True
    
    def test_gamma_pole_structure(self):
        """Test that Gamma poles are correctly at negative integers."""
        analyzer = CanonicalSystemImpossibility(n_poles=20)
        
        expected_poles = np.arange(0, -20, -1)
        np.testing.assert_array_equal(analyzer.gamma_poles, expected_poles)
        
        # All should be non-positive integers
        assert np.all(analyzer.gamma_poles <= 0)
        assert np.all(analyzer.gamma_poles == np.floor(analyzer.gamma_poles))
    
    def test_conclusion_consistency(self):
        """Test that all three scenarios consistently fail."""
        analyzer = CanonicalSystemImpossibility(n_poles=10)
        
        results = [
            analyzer.analyze_real_argument(),
            analyzer.analyze_imaginary_argument(),
            analyzer.analyze_sqrt_argument()
        ]
        
        # All should have 'IMPOSSIBLE' in conclusion
        for result in results:
            assert 'IMPOSSIBLE' in result['conclusion']
            assert 'conclusion' in result
            
    def test_implications_completeness(self):
        """Test that theorem implications cover key points."""
        analyzer = CanonicalSystemImpossibility(n_poles=10)
        theorem = analyzer.prove_impossibility_theorem()
        
        implications = theorem['conclusion']['implications']
        
        # Should mention key concepts
        implications_text = ' '.join(implications)
        
        # Key concepts that should be mentioned
        key_concepts = ['Γ', 'de Branges', 'Fredholm', 'Weyl']
        
        for concept in key_concepts:
            # At least some implications should mention these
            assert any(concept in imp for imp in implications)


class TestTheoremIntegration:
    """Integration tests for the complete theorem."""
    
    def test_full_theorem_proof_cycle(self):
        """Test the complete theorem proof from initialization to conclusion."""
        # Initialize
        analyzer = CanonicalSystemImpossibility(n_poles=15)
        
        # Analyze all scenarios
        real_result = analyzer.analyze_real_argument(a=0.25)
        imag_result = analyzer.analyze_imaginary_argument(a=0.25)
        sqrt_result = analyzer.analyze_sqrt_argument(a=0.25, b=0.5)
        
        # All should fail
        assert 'IMPOSSIBLE' in real_result['conclusion']
        assert 'IMPOSSIBLE' in imag_result['conclusion']
        assert 'IMPOSSIBLE' in sqrt_result['conclusion']
        
        # Prove complete theorem
        theorem = analyzer.prove_impossibility_theorem()
        
        # Theorem should hold
        assert theorem['conclusion']['theorem_holds'] is True
        
        # Should have comprehensive summary
        assert len(theorem['conclusion']['summary']) > 100
        
    def test_mathematical_correctness(self):
        """Test mathematical correctness of pole calculations."""
        analyzer = CanonicalSystemImpossibility(n_poles=10)
        
        # Test real argument: Γ(0.25 + λ)
        # Poles when 0.25 + λ = -n → λ = -0.25 - n
        result = analyzer.analyze_real_argument(a=0.25)
        expected = -0.25 - np.arange(10)
        np.testing.assert_array_almost_equal(result['poles'], expected)
        
        # Test imaginary argument: Γ(0.25 + iλ)
        # Poles when 0.25 + iλ = -n → λ = i(-0.25 - n)
        result = analyzer.analyze_imaginary_argument(a=0.25)
        expected = 1j * (-0.25 - np.arange(10))
        np.testing.assert_array_almost_equal(result['poles'], expected)
        
        # Test sqrt argument: Γ(0.25 + i·0.5·√λ)
        # Poles when 0.25 + i·0.5·√λ = -n
        # → i·0.5·√λ = -0.25 - n
        # → √λ = -i(0.25 + n)/0.5 = -i·2(0.25 + n)
        # → λ = -4(0.25 + n)²
        result = analyzer.analyze_sqrt_argument(a=0.25, b=0.5)
        expected = -((0.25 + np.arange(10)) / 0.5)**2
        np.testing.assert_array_almost_equal(result['poles'], expected)


if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])
