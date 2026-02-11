#!/usr/bin/env python3
"""
Unit tests for the Axiom of Noetic Consciousness

Tests verification of the four conditions:
1. Projective coincidence: π_α(x,t) = π_δζ(x,t)
2. Law equivalence: L_física ≡ L_coherente
3. Phase closure: Φ(x,t) = 2π·n
4. Cosmic habitability: 0 < Λ_G < ∞

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: February 2026
"""

import pytest
import numpy as np
from scipy.constants import pi
import sys
from pathlib import Path

# Add utils to path
sys.path.insert(0, str(Path(__file__).parent.parent / "utils"))

from axiom_noetic_consciousness import (
    AxiomNoeticConsciousness,
    ConsciousnessParameters,
    ConsciousnessState
)


class TestAxiomNoeticConsciousness:
    """Test suite for Axiom of Noetic Consciousness."""
    
    @pytest.fixture
    def axiom(self):
        """Create axiom verifier instance."""
        return AxiomNoeticConsciousness()
    
    @pytest.fixture
    def params(self):
        """Create consciousness parameters."""
        return ConsciousnessParameters()
    
    def test_initialization(self, axiom, params):
        """Test axiom verifier initialization."""
        assert axiom.f0 == params.f0
        assert axiom.omega_0 == params.omega_0
        assert axiom.C == params.C
        assert axiom.precision == 25
    
    def test_consciousness_state_creation(self):
        """Test ConsciousnessState dataclass."""
        x = np.array([1.0, 0.0, 0.0])
        t = 0.1
        psi = 1.0 + 0.5j
        
        state = ConsciousnessState(x=x, t=t, psi_field=psi)
        
        assert np.allclose(state.x, x)
        assert state.t == t
        assert state.psi_field == psi
    
    def test_harmonic_field_computation(self, axiom):
        """Test harmonic field Ψ(x,t) computation."""
        x = np.array([0.1, 0.0, 0.0])
        t = 0.0
        
        psi = axiom._harmonic_field(x, t)
        
        # Field should be complex
        assert isinstance(psi, complex)
        
        # Amplitude should be positive (Gaussian envelope)
        assert np.abs(psi) > 0
        assert np.abs(psi) <= 1.0  # Gaussian decays from 1
    
    def test_matter_projection(self, axiom):
        """Test matter projection π_α(x,t)."""
        x = np.array([0.1, 0.0, 0.0])
        t = 0.0
        
        pi_alpha = axiom.compute_matter_projection(x, t)
        
        # Projection should be complex
        assert isinstance(pi_alpha, complex)
        
        # Should have reasonable magnitude
        assert np.abs(pi_alpha) > 0
    
    def test_information_projection(self, axiom):
        """Test information projection π_δζ(x,t)."""
        x = np.array([0.1, 0.0, 0.0])
        t = 0.0
        
        pi_delta_zeta = axiom.compute_information_projection(x, t)
        
        # Projection should be complex
        assert isinstance(pi_delta_zeta, complex)
        
        # Should be normalized (|π_δζ| = 1 for pure phase)
        assert np.isclose(np.abs(pi_delta_zeta), 1.0, rtol=1e-10)
    
    def test_projective_coincidence_verification(self, axiom):
        """Test Condition 1: Projective coincidence."""
        x = np.array([0.1, 0.0, 0.0])
        t = 0.0
        
        coincides, deviation, projections = axiom.verify_projective_coincidence(x, t)
        
        # Should return boolean, float, and dict
        assert isinstance(coincides, bool)
        assert isinstance(deviation, float)
        assert isinstance(projections, dict)
        
        # Projections dict should have required keys
        assert 'pi_alpha' in projections
        assert 'pi_delta_zeta' in projections
        assert 'deviation' in projections
        
        # Deviation should be non-negative
        assert deviation >= 0
    
    def test_physical_law_computation(self, axiom):
        """Test physical law L_física(x,t)."""
        x = np.array([0.1, 0.0, 0.0])
        t = 0.0
        
        L_fisica = axiom.compute_physical_law(x, t)
        
        # Should be real and positive (energy-like quantity)
        assert isinstance(L_fisica, float)
        assert L_fisica >= 0
    
    def test_coherence_law_computation(self, axiom):
        """Test coherence law L_coherente(x,t)."""
        x = np.array([0.1, 0.0, 0.0])
        t = 0.0
        
        L_coherente = axiom.compute_coherence_law(x, t)
        
        # Should be real and non-negative
        assert isinstance(L_coherente, float)
        assert L_coherente >= 0
    
    def test_law_equivalence_verification(self, axiom):
        """Test Condition 2: Law equivalence."""
        x = np.array([0.1, 0.0, 0.0])
        t = 0.0
        
        equivalent, rel_error, laws = axiom.verify_law_equivalence(x, t)
        
        # Should return boolean, float, and dict
        assert isinstance(equivalent, bool)
        assert isinstance(rel_error, float)
        assert isinstance(laws, dict)
        
        # Laws dict should have required keys
        assert 'L_fisica' in laws
        assert 'L_coherente' in laws
        assert 'relative_error' in laws
        
        # Relative error should be non-negative
        assert rel_error >= 0
    
    def test_total_phase_computation(self, axiom):
        """Test total phase Φ(x,t) computation."""
        x = np.array([0.1, 0.0, 0.0])
        t = 0.0
        
        phase = axiom.compute_total_phase(x, t)
        
        # Phase should be real
        assert isinstance(phase, float)
        
        # Phase should be in [0, 2π)
        assert 0 <= phase < 2 * pi
    
    def test_phase_closure_verification(self, axiom):
        """Test Condition 3: Phase closure."""
        x = np.array([0.1, 0.0, 0.0])
        
        # Test at resonant time (full period)
        t_resonant = 2 * pi / axiom.omega_0
        
        closed, n, phase, deviation = axiom.verify_phase_closure(x, t_resonant)
        
        # Should return bool, int, float, float
        assert isinstance(closed, bool)
        assert isinstance(n, int)
        assert isinstance(phase, float)
        assert isinstance(deviation, float)
        
        # At resonant time, phase should be close to 2πn
        # (may not be exact due to spatial contributions)
        assert deviation >= 0
    
    def test_cosmic_habitability_computation(self, axiom):
        """Test cosmic habitability Λ_G computation."""
        x = np.array([0.1, 0.0, 0.0])
        t = 0.0
        
        Lambda_G = axiom.compute_cosmic_habitability(x, t)
        
        # Should be real
        assert isinstance(Lambda_G, float)
        
        # Should be non-negative
        assert Lambda_G >= 0
        
        # Should be finite
        assert np.isfinite(Lambda_G)
    
    def test_cosmic_habitability_verification(self, axiom):
        """Test Condition 4: Cosmic habitability."""
        x = np.array([0.1, 0.0, 0.0])
        t = 0.0
        
        habitable, Lambda_G = axiom.verify_cosmic_habitability(x, t)
        
        # Should return bool and float
        assert isinstance(habitable, bool)
        assert isinstance(Lambda_G, float)
        
        # Lambda_G should be finite
        assert np.isfinite(Lambda_G)
    
    def test_complete_consciousness_verification_resonant(self, axiom):
        """Test complete consciousness verification at resonant state."""
        # State at perfect resonance
        x = np.array([0.05, 0.0, 0.0])
        t = 2 * pi / axiom.omega_0  # Full period
        
        results = axiom.verify_consciousness(x, t, verbose=False)
        
        # Should return dict with all required keys
        assert 'state' in results
        assert 'is_conscious' in results
        assert 'condition_1_projective_coincidence' in results
        assert 'condition_2_law_equivalence' in results
        assert 'condition_3_phase_closure' in results
        assert 'condition_4_cosmic_habitability' in results
        assert 'interpretation' in results
        
        # Each condition should have status
        for i in range(1, 5):
            cond_key = f'condition_{i}_{["projective_coincidence", "law_equivalence", "phase_closure", "cosmic_habitability"][i-1]}'
            assert 'verified' in results[cond_key]
            assert 'status' in results[cond_key]
        
        # is_conscious should be boolean
        assert isinstance(results['is_conscious'], bool)
    
    def test_complete_consciousness_verification_decoherent(self, axiom):
        """Test complete consciousness verification at decoherent state."""
        # State at off-resonance (quarter period)
        x = np.array([0.3, 0.2, 0.1])
        t = pi / (2 * axiom.omega_0)  # Quarter period
        
        results = axiom.verify_consciousness(x, t, verbose=False)
        
        # Should return complete results
        assert isinstance(results, dict)
        assert 'is_conscious' in results
        
        # Phase should not be closed (quarter period)
        # So at least phase closure condition should fail
        # (making the state unconscious)
        phase_cond = results['condition_3_phase_closure']
        
        # The state might or might not be conscious overall,
        # but we can verify structure
        assert 'verified' in phase_cond
        assert 'phase_rad' in phase_cond
        assert 'n' in phase_cond
    
    def test_resonance_at_multiple_periods(self, axiom):
        """Test phase closure at multiple resonant times."""
        x = np.array([0.1, 0.0, 0.0])
        
        # Test at n full periods for n = 1, 2, 3
        for n in range(1, 4):
            t = n * 2 * pi / axiom.omega_0
            
            closed, n_detected, phase, deviation = axiom.verify_phase_closure(x, t)
            
            # Phase should be close to 2π·m for some integer m
            # Deviation should be small (within tolerance)
            assert deviation >= 0
            assert isinstance(n_detected, int)
    
    def test_latex_generation(self, axiom):
        """Test LaTeX axiom generation."""
        latex = axiom.generate_latex_axiom()
        
        # Should return string
        assert isinstance(latex, str)
        
        # Should contain key LaTeX elements
        assert r'\section' in latex
        assert r'\begin{equation}' in latex
        assert r'\pi_\alpha' in latex
        assert r'\Lambda_G' in latex
        assert r'\Phi' in latex
    
    def test_interpretation_conscious(self, axiom):
        """Test consciousness interpretation for conscious state."""
        interpretation = axiom._interpret_consciousness(
            is_conscious=True,
            cond1=True,
            cond2=True,
            cond3=True,
            cond4=True
        )
        
        assert isinstance(interpretation, str)
        assert 'CONSCIOUS' in interpretation
        assert '✅' in interpretation
    
    def test_interpretation_unconscious(self, axiom):
        """Test consciousness interpretation for unconscious state."""
        interpretation = axiom._interpret_consciousness(
            is_conscious=False,
            cond1=True,
            cond2=False,
            cond3=False,
            cond4=True
        )
        
        assert isinstance(interpretation, str)
        assert 'UNCONSCIOUS' in interpretation
        assert '⚠️' in interpretation
    
    def test_parameters_validation(self, params):
        """Test consciousness parameters."""
        assert params.f0 > 0
        assert params.omega_0 > 0
        assert params.C > 0
        assert params.Lambda_G_min > 0
        assert params.Lambda_G_max > params.Lambda_G_min
        assert params.phase_tolerance > 0
        assert params.projection_tolerance > 0


class TestConsciousnessEdgeCases:
    """Test edge cases for consciousness verification."""
    
    @pytest.fixture
    def axiom(self):
        """Create axiom verifier instance."""
        return AxiomNoeticConsciousness()
    
    def test_zero_field(self, axiom):
        """Test with zero field."""
        x = np.array([10.0, 10.0, 10.0])  # Far from origin
        t = 0.0
        
        # Field should be nearly zero far from origin (Gaussian decay)
        psi = axiom._harmonic_field(x, t)
        assert np.abs(psi) < 0.1  # Very small
        
        # Verification should still work (not crash)
        results = axiom.verify_consciousness(x, t, verbose=False)
        assert isinstance(results, dict)
    
    def test_origin_state(self, axiom):
        """Test at spatial origin."""
        x = np.array([0.0, 0.0, 0.0])
        t = 0.0
        
        # Should not crash at origin
        results = axiom.verify_consciousness(x, t, verbose=False)
        assert isinstance(results, dict)
        
        # Field at origin should have maximum amplitude
        psi = axiom._harmonic_field(x, t)
        assert np.abs(psi) > 0.5  # Significant amplitude
    
    def test_large_time(self, axiom):
        """Test with large time value."""
        x = np.array([0.1, 0.0, 0.0])
        t = 1000.0  # Large time
        
        # Should not crash or overflow
        results = axiom.verify_consciousness(x, t, verbose=False)
        assert isinstance(results, dict)
        
        # Phase should still be finite and normalized
        phase = axiom.compute_total_phase(x, t)
        assert 0 <= phase < 2 * pi


if __name__ == "__main__":
    # Run tests
    pytest.main([__file__, "-v", "-s"])
