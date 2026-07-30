#!/usr/bin/env python3
"""
Comprehensive Test Suite for ABC-Atlas³ Coupling Tensor
========================================================

Tests all components of the ABC-Atlas³ coupling tensor that unifies
the Riemann Hypothesis framework with the ABC Conjecture.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
License: CC BY-NC-SA 4.0
"""

import sys
import os
import math

# Add parent directory to path for imports
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from operators.abc_atlas3_coupling_tensor import (
    ABCAtlas3CouplingTensor,
    radical,
    quantum_info_abc,
    F0,
    KAPPA_PI,
    EPSILON_CRITICAL,
    C_QCAL
)

try:
    import pytest
    PYTEST_AVAILABLE = True
except ImportError:
    PYTEST_AVAILABLE = False


class TestRadicalFunction:
    """Test suite for radical computation."""
    
    def test_radical_basic(self):
        """Test basic radical computations."""
        assert radical(12) == 6  # 2² × 3 → 2 × 3
        assert radical(100) == 10  # 2² × 5² → 2 × 5
        assert radical(30) == 30  # 2 × 3 × 5 (square-free)
        assert radical(1) == 1
        assert radical(7) == 7  # Prime
    
    def test_radical_powers(self):
        """Test radical of perfect powers."""
        assert radical(8) == 2  # 2³
        assert radical(27) == 3  # 3³
        assert radical(128) == 2  # 2⁷
        assert radical(243) == 3  # 3⁵
    
    def test_radical_large(self):
        """Test radical for larger numbers."""
        assert radical(1001) == 1001  # 7 × 11 × 13
        assert radical(1000) == 10  # 2³ × 5³


class TestQuantumInfoFunction:
    """Test suite for quantum information function."""
    
    def test_quantum_info_basic(self):
        """Test basic quantum information calculation."""
        # For (1, 8, 9): rad(72) = rad(2³ × 3²) = 6
        i_abc = quantum_info_abc(1, 8, 9)
        expected = math.log2(9) - math.log2(6)
        assert abs(i_abc - expected) < 1e-10
    
    def test_quantum_info_exceptional(self):
        """Test quantum info for known exceptional triple."""
        # (3, 125, 128) is a famous exceptional triple
        i_abc = quantum_info_abc(3, 125, 128)
        # Should be positive (c > rad(abc))
        assert i_abc > 0
    
    def test_quantum_info_bounds(self):
        """Test that quantum info is finite."""
        test_triples = [(1, 8, 9), (3, 125, 128), (1, 80, 81)]
        for a, b, c in test_triples:
            i_abc = quantum_info_abc(a, b, c)
            assert math.isfinite(i_abc)


class TestCouplingTensorInit:
    """Test suite for coupling tensor initialization."""
    
    def test_init_default(self):
        """Test default initialization."""
        coupling = ABCAtlas3CouplingTensor()
        assert coupling.f0 == F0
        assert coupling.T_cosmic == 2.725
        assert coupling.kappa_pi == KAPPA_PI
        assert coupling.C_coherence == C_QCAL
    
    def test_init_custom(self):
        """Test custom initialization."""
        coupling = ABCAtlas3CouplingTensor(
            f0=100.0,
            T_cosmic=3.0,
            kappa_pi=2.5,
            C_coherence=200.0
        )
        assert coupling.f0 == 100.0
        assert coupling.T_cosmic == 3.0
        assert coupling.kappa_pi == 2.5
        assert coupling.C_coherence == 200.0
    
    def test_epsilon_critical_computed(self):
        """Test that epsilon critical is computed correctly."""
        coupling = ABCAtlas3CouplingTensor()
        assert coupling.epsilon_critical > 0
        assert coupling.epsilon_critical < 1e-8
    
    def test_viscosity_computed(self):
        """Test that viscosity ν = 1/κ is computed."""
        coupling = ABCAtlas3CouplingTensor()
        expected_nu = 1.0 / KAPPA_PI
        assert abs(coupling.nu - expected_nu) < 1e-10


class TestAdelicLaplacian:
    """Test suite for Adelic Laplacian computation."""
    
    def test_laplacian_basic(self):
        """Test basic Adelic Laplacian computation."""
        coupling = ABCAtlas3CouplingTensor()
        result = coupling.compute_adelic_laplacian(1, 8, 9)
        
        # Should have required fields
        assert 'laplacian_value' in result
        assert 'coherence_psi' in result
        assert 'dissipation_capacity' in result
        assert 'transport_potential' in result
        assert 'quantum_info' in result
        assert 'epsilon_bound' in result
    
    def test_laplacian_transport_dissipation(self):
        """Test transport vs dissipation split."""
        coupling = ABCAtlas3CouplingTensor()
        result = coupling.compute_adelic_laplacian(3, 125, 128)
        
        # Transport should be log₂(c)
        assert abs(result['transport_potential'] - math.log2(128)) < 1e-10
        
        # Dissipation should be log₂(rad(abc))
        rad_abc = radical(3 * 125 * 128)
        assert abs(result['dissipation_capacity'] - math.log2(rad_abc)) < 1e-10
    
    def test_laplacian_net_flow(self):
        """Test that laplacian is net flow."""
        coupling = ABCAtlas3CouplingTensor()
        result = coupling.compute_adelic_laplacian(1, 80, 81)
        
        # Net flow = transport - dissipation
        net = result['transport_potential'] - result['dissipation_capacity']
        assert abs(result['laplacian_value'] - net) < 1e-10
    
    def test_coherence_psi_bounds(self):
        """Test that Ψ coherence is bounded."""
        coupling = ABCAtlas3CouplingTensor()
        
        test_triples = [(1, 8, 9), (3, 125, 128), (5, 27, 32)]
        for a, b, c in test_triples:
            result = coupling.compute_adelic_laplacian(a, b, c)
            # Ψ should be positive
            assert result['coherence_psi'] > 0


class TestAdelicFlow:
    """Test suite for adelic flow analysis."""
    
    def test_flow_analysis_structure(self):
        """Test flow analysis returns correct structure."""
        coupling = ABCAtlas3CouplingTensor()
        flow = coupling.analyze_adelic_flow(1, 8, 9)
        
        assert 'quantum_info' in flow
        assert 'reynolds_analog' in flow
        assert 'flow_regime' in flow
        assert 'quality_abc' in flow
        assert 'viscosity_nu' in flow
        assert 'is_exceptional' in flow
        assert 'laminar_stable' in flow
    
    def test_flow_regime_classification(self):
        """Test flow regime classification."""
        coupling = ABCAtlas3CouplingTensor()
        
        # Simple triple should be laminar
        flow1 = coupling.analyze_adelic_flow(1, 8, 9)
        assert flow1['flow_regime'] in ['laminar', 'transitional', 'turbulent']
        
        # Exceptional triple may be transitional/turbulent
        flow2 = coupling.analyze_adelic_flow(3, 125, 128)
        assert flow2['flow_regime'] in ['laminar', 'transitional', 'turbulent']
    
    def test_reynolds_analog_positive(self):
        """Test Reynolds analog is positive."""
        coupling = ABCAtlas3CouplingTensor()
        
        test_triples = [(1, 8, 9), (3, 125, 128), (1, 80, 81)]
        for a, b, c in test_triples:
            flow = coupling.analyze_adelic_flow(a, b, c)
            assert flow['reynolds_analog'] > 0
    
    def test_exceptional_detection(self):
        """Test exceptional triple detection."""
        coupling = ABCAtlas3CouplingTensor()
        
        # (3, 125, 128) is exceptional
        flow = coupling.analyze_adelic_flow(3, 125, 128)
        assert flow['is_exceptional'] == True


class TestCouplingStrength:
    """Test suite for coupling strength computation."""
    
    def test_coupling_metrics_structure(self):
        """Test coupling metrics dataclass structure."""
        coupling = ABCAtlas3CouplingTensor()
        metrics = coupling.compute_coupling_strength(1, 8, 9)
        
        assert hasattr(metrics, 'epsilon_critical')
        assert hasattr(metrics, 'abc_quantum_info')
        assert hasattr(metrics, 'atlas3_spectral_gap')
        assert hasattr(metrics, 'coupling_strength')
        assert hasattr(metrics, 'coherence_ratio')
        assert hasattr(metrics, 'viscosity_nu')
        assert hasattr(metrics, 'condensation_parameter')
        assert hasattr(metrics, 'flow_regime')
    
    def test_coupling_with_default_gap(self):
        """Test coupling with default spectral gap."""
        coupling = ABCAtlas3CouplingTensor()
        metrics = coupling.compute_coupling_strength(1, 8, 9)
        
        # Default gap should be epsilon_critical
        assert metrics.atlas3_spectral_gap == coupling.epsilon_critical
    
    def test_coupling_with_custom_gap(self):
        """Test coupling with custom spectral gap."""
        coupling = ABCAtlas3CouplingTensor()
        custom_gap = 1e-8
        metrics = coupling.compute_coupling_strength(1, 8, 9, atlas3_gap=custom_gap)
        
        assert metrics.atlas3_spectral_gap == custom_gap
    
    def test_coherence_ratio_bounds(self):
        """Test coherence ratio is bounded [0, 1]."""
        coupling = ABCAtlas3CouplingTensor()
        
        test_triples = [(1, 8, 9), (3, 125, 128), (5, 27, 32)]
        for a, b, c in test_triples:
            metrics = coupling.compute_coupling_strength(a, b, c)
            assert 0 <= metrics.coherence_ratio <= 1
    
    def test_viscosity_matches_init(self):
        """Test viscosity in metrics matches initialization."""
        coupling = ABCAtlas3CouplingTensor()
        metrics = coupling.compute_coupling_strength(1, 8, 9)
        
        assert metrics.viscosity_nu == coupling.nu


class TestInformationConservation:
    """Test suite for information conservation law."""
    
    def test_conservation_structure(self):
        """Test conservation analysis structure."""
        coupling = ABCAtlas3CouplingTensor()
        cons = coupling.verify_information_conservation(1, 8, 9)
        
        assert 'info_a' in cons
        assert 'info_b' in cons
        assert 'info_c' in cons
        assert 'info_input' in cons
        assert 'info_output' in cons
        assert 'info_entanglement' in cons
        assert 'info_radical' in cons
        assert 'conservation_satisfied' in cons
    
    def test_conservation_law(self):
        """Test information conservation law holds."""
        coupling = ABCAtlas3CouplingTensor()
        
        test_triples = [(1, 8, 9), (3, 125, 128), (1, 80, 81)]
        for a, b, c in test_triples:
            cons = coupling.verify_information_conservation(a, b, c)
            
            # Info(a) + Info(b) should equal Info(c) + Info_entanglement
            total_in = cons['info_input']
            total_out = cons['info_output'] + cons['info_entanglement']
            
            # Allow for floating point error
            assert abs(total_in - total_out) < 1e-6
    
    def test_all_info_finite(self):
        """Test all information values are finite."""
        coupling = ABCAtlas3CouplingTensor()
        cons = coupling.verify_information_conservation(1, 8, 9)
        
        assert math.isfinite(cons['info_a'])
        assert math.isfinite(cons['info_b'])
        assert math.isfinite(cons['info_c'])
        assert math.isfinite(cons['info_entanglement'])


class TestFusionTable:
    """Test suite for fusion table generation."""
    
    def test_fusion_table_structure(self):
        """Test fusion table has correct structure."""
        coupling = ABCAtlas3CouplingTensor()
        fusion = coupling.generate_fusion_table(1, 8, 9)
        
        assert 'Frequency' in fusion
        assert 'Scale' in fusion
        assert 'Operator' in fusion
        assert 'Objective' in fusion
        assert 'Metrics' in fusion
    
    def test_fusion_frequency_alignment(self):
        """Test frequency alignment in fusion table."""
        coupling = ABCAtlas3CouplingTensor()
        fusion = coupling.generate_fusion_table(1, 8, 9)
        
        freq = fusion['Frequency']
        assert freq['Atlas3_Riemann'] == F0
        assert freq['ABC_Document'] == F0
        assert freq['Unified_Fusion'] == 'Resonance Base'
    
    def test_fusion_metrics_complete(self):
        """Test metrics section is complete."""
        coupling = ABCAtlas3CouplingTensor()
        fusion = coupling.generate_fusion_table(3, 125, 128)
        
        metrics = fusion['Metrics']
        assert 'coupling_strength' in metrics
        assert 'coherence_ratio' in metrics
        assert 'flow_regime' in metrics
        assert 'quantum_info' in metrics
        assert 'conservation_error' in metrics
    
    def test_fusion_conservation_error_small(self):
        """Test conservation error is small."""
        coupling = ABCAtlas3CouplingTensor()
        fusion = coupling.generate_fusion_table(1, 8, 9)
        
        error = fusion['Metrics']['conservation_error']
        assert error < 1e-6


class TestIntegration:
    """Integration tests for complete workflow."""
    
    def test_complete_analysis_workflow(self):
        """Test complete ABC-Atlas³ analysis workflow."""
        coupling = ABCAtlas3CouplingTensor()
        
        # Test with exceptional triple
        a, b, c = 3, 125, 128
        
        # Compute all components
        laplacian = coupling.compute_adelic_laplacian(a, b, c)
        flow = coupling.analyze_adelic_flow(a, b, c)
        metrics = coupling.compute_coupling_strength(a, b, c)
        conservation = coupling.verify_information_conservation(a, b, c)
        fusion = coupling.generate_fusion_table(a, b, c)
        
        # All should complete without error
        assert laplacian is not None
        assert flow is not None
        assert metrics is not None
        assert conservation is not None
        assert fusion is not None
    
    def test_multiple_triples_consistency(self):
        """Test consistency across multiple triples."""
        coupling = ABCAtlas3CouplingTensor()
        
        triples = [(1, 8, 9), (3, 125, 128), (1, 80, 81), (5, 27, 32)]
        
        for a, b, c in triples:
            # All should have valid quantum info
            I_abc = quantum_info_abc(a, b, c)
            assert math.isfinite(I_abc)
            
            # All should have valid flow regime
            flow = coupling.analyze_adelic_flow(a, b, c)
            assert flow['flow_regime'] in ['laminar', 'transitional', 'turbulent']
    
    def test_qcal_constants_preserved(self):
        """Test QCAL constants are preserved throughout."""
        coupling = ABCAtlas3CouplingTensor()
        
        # Constants should match
        assert coupling.f0 == F0
        assert coupling.kappa_pi == KAPPA_PI
        assert coupling.C_coherence == C_QCAL
        
        # Fusion table should preserve them
        fusion = coupling.generate_fusion_table(1, 8, 9)
        assert fusion['Frequency']['Atlas3_Riemann'] == F0


def test_module_constants():
    """Test module-level constants are defined correctly."""
    assert F0 == 141.7001
    assert KAPPA_PI > 2.5 and KAPPA_PI < 2.6
    assert C_QCAL == 244.36
    assert EPSILON_CRITICAL > 0
    assert EPSILON_CRITICAL < 1e-8


if __name__ == '__main__':
    if PYTEST_AVAILABLE:
        pytest.main([__file__, '-v'])
    else:
        print("pytest not available, running basic tests...")
        
        # Run basic tests
        test = TestRadicalFunction()
        test.test_radical_basic()
        test.test_radical_powers()
        print("✓ Radical tests passed")
        
        test2 = TestQuantumInfoFunction()
        test2.test_quantum_info_basic()
        test2.test_quantum_info_exceptional()
        print("✓ Quantum info tests passed")
        
        test3 = TestCouplingTensorInit()
        test3.test_init_default()
        test3.test_epsilon_critical_computed()
        print("✓ Coupling tensor init tests passed")
        
        test4 = TestAdelicLaplacian()
        test4.test_laplacian_basic()
        print("✓ Adelic Laplacian tests passed")
        
        test5 = TestIntegration()
        test5.test_complete_analysis_workflow()
        print("✓ Integration tests passed")
        
        test_module_constants()
        print("✓ Module constants tests passed")
        
        print("\n✅ All basic tests passed!")
        print("For full test suite, install pytest: pip install pytest")
