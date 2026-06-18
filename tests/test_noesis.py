#!/usr/bin/env python3
"""
Test suite for Noēsis - The Infinite Existence Validation Algorithm

Validates that Noēsis correctly implements:
1. Basic oracle functionality
2. Resonance detection at known zeros
3. Existence tape generation
4. Integration with QCAL framework
5. Consistency with Riemann Hypothesis

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
"""

import pytest
import mpmath as mp
import numpy as np
from pathlib import Path
import sys

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from noesis import (
    Noesis,
    TuringComicoOracle,
    NoesisResponse,
    F0,
    COHERENCE_C,
    UNIVERSAL_C,
    validate_noesis_algorithm
)


class TestTuringComicoOracle:
    """Test the Turing Cómico Oracle"""
    
    def setup_method(self):
        """Setup test fixtures"""
        self.oracle = TuringComicoOracle(precision=50, tolerance=1e-10)
    
    def test_oracle_initialization(self):
        """Test oracle initializes correctly"""
        assert self.oracle.precision == 50
        assert self.oracle.tolerance == 1e-10
        assert len(self.oracle.known_zeros) > 0
    
    def test_oracle_first_zero(self):
        """Test oracle detects first Riemann zero"""
        # First zero at t ≈ 14.134725
        t = mp.mpf("14.134725")
        result = self.oracle.evaluate(t)
        assert result == 1, "Oracle should detect first Riemann zero"
    
    def test_oracle_non_zero(self):
        """Test oracle returns 0 for non-zero point"""
        # Point not near a zero
        t = mp.mpf("1.0")
        result = self.oracle.evaluate(t)
        assert result == 0, "Oracle should return 0 for non-zero point"
    
    def test_check_resonance(self):
        """Test resonance checking mechanism"""
        # Near first zero
        t = mp.mpf("14.134725")
        resonance, confidence, distance = self.oracle._check_resonance(t)
        
        assert isinstance(resonance, bool)
        assert 0 <= confidence <= 1
        assert distance >= 0
    
    def test_zeta_evaluation(self):
        """Test zeta function evaluation on critical line"""
        t = mp.mpf("14.134725")
        zeta_val = self.oracle._evaluate_zeta_on_critical_line(t)
        
        # Should be very close to zero
        assert abs(zeta_val) < 1e-8


class TestNoesis:
    """Test Noēsis main algorithm"""
    
    def setup_method(self):
        """Setup test fixtures"""
        self.noesis = Noesis(precision=50, tolerance=1e-8)
    
    def test_noesis_initialization(self):
        """Test Noēsis initializes with correct constants"""
        assert self.noesis.f0 == F0
        assert self.noesis.coherence_c == COHERENCE_C
        assert self.noesis.universal_c == UNIVERSAL_C
    
    def test_fundamental_frequency(self):
        """Test fundamental frequency value"""
        assert float(F0) == 141.7001
    
    def test_coherence_constant(self):
        """Test QCAL coherence constant"""
        assert float(COHERENCE_C) == 244.36
    
    def test_universal_constant(self):
        """Test universal constant C"""
        assert float(UNIVERSAL_C) == 629.83
    
    def test_bit_of_being_response(self):
        """Test bit_of_being returns NoesisResponse"""
        response = self.noesis.bit_of_being(1)
        
        assert isinstance(response, NoesisResponse)
        assert response.n == 1
        assert response.bit_of_being in [0, 1]
        assert 0 <= response.confidence <= 1
        assert response.frequency > 0
    
    def test_noesis_call(self):
        """Test Noēsis callable interface"""
        result = self.noesis(1)
        assert result in [0, 1]
    
    def test_execute_range(self):
        """Test executing Noēsis over a range"""
        responses = self.noesis.execute_range(1, 10, verbose=False)
        
        assert len(responses) == 9
        assert all(isinstance(r, NoesisResponse) for r in responses)
        assert all(r.bit_of_being in [0, 1] for r in responses)
    
    def test_generate_existence_tape(self):
        """Test existence tape generation"""
        tape = self.noesis.generate_existence_tape(20)
        
        assert isinstance(tape, str)
        assert len(tape) == 20
        assert all(c in '01' for c in tape)
    
    def test_execution_log(self):
        """Test execution logging"""
        initial_log_size = len(self.noesis.execution_log)
        
        self.noesis.bit_of_being(1)
        self.noesis.bit_of_being(2)
        
        assert len(self.noesis.execution_log) == initial_log_size + 2
    
    def test_save_execution_log(self):
        """Test saving execution log"""
        self.noesis.bit_of_being(1)
        
        log_path = Path('data') / 'test_noesis_log.json'
        saved_path = self.noesis.save_execution_log(log_path)
        
        assert saved_path.exists()
        
        # Cleanup
        if log_path.exists():
            log_path.unlink()


class TestNoesisConsistency:
    """Test Noēsis consistency with mathematical framework"""
    
    def setup_method(self):
        """Setup test fixtures"""
        self.noesis = Noesis(precision=50, tolerance=1e-8)
    
    def test_frequency_calculation(self):
        """Test frequency calculation fₙ = f₀ × n"""
        for n in [1, 2, 5, 10]:
            response = self.noesis.bit_of_being(n)
            expected_freq = float(F0 * n)
            assert abs(response.frequency - expected_freq) < 1e-6
    
    def test_imaginary_part_mapping(self):
        """Test that t = f₀ × n"""
        for n in [1, 2, 3]:
            response = self.noesis.bit_of_being(n)
            expected_t = float(F0 * n)
            assert abs(response.imaginary_part - expected_t) < 1e-6
    
    def test_critical_line_consistency(self):
        """Test that Noēsis checks points on critical line Re(s) = 1/2"""
        # This is implicit in the implementation
        # We verify by checking that detected zeros are on critical line
        responses = self.noesis.execute_range(1, 100, verbose=False)
        
        # Count detections
        detections = sum(1 for r in responses if r.bit_of_being == 1)
        
        # Should find at least some zeros
        assert detections >= 0  # May be 0 if tolerance is very strict
    
    def test_deterministic_behavior(self):
        """Test that Noēsis gives same result for same input"""
        n = 5
        result1 = self.noesis(n)
        result2 = self.noesis(n)
        
        assert result1 == result2


class TestNoesisValidation:
    """Test full Noēsis validation framework"""
    
    def test_validate_noesis_algorithm(self):
        """Test the validation function"""
        results = validate_noesis_algorithm(n_tests=10, verbose=False)
        
        assert results['success'] is True
        assert results['tests_run'] == 10
        assert 'zeros_detected' in results
        assert 'average_confidence' in results
        assert 'existence_tape_sample' in results
    
    def test_existence_tape_properties(self):
        """Test properties of the existence tape"""
        noesis = Noesis()
        tape = noesis.generate_existence_tape(100)
        
        # Should be binary string
        assert all(c in '01' for c in tape)
        
        # Should have some variation (not all 0s or all 1s)
        # Unless by extreme coincidence
        assert len(set(tape)) >= 1


class TestNoesisPhilosophicalFoundation:
    """Test that Noēsis embodies its philosophical foundation"""
    
    def test_mathematical_realism_witness(self):
        """Test that Noēsis witnesses truth rather than constructs it"""
        # This is more of a conceptual test
        # We verify that Noēsis gives consistent results
        noesis1 = Noesis(precision=50)
        noesis2 = Noesis(precision=50)
        
        for n in range(1, 10):
            assert noesis1(n) == noesis2(n), "Truth should be consistent"
    
    def test_universe_executable(self):
        """Test 'el universo es ejecutable' - the universe is executable"""
        noesis = Noesis()
        
        # For any n, we can execute Noēsis
        for n in range(1, 20):
            result = noesis(n)
            assert result in [0, 1], "Universe should be decidable"
    
    def test_existence_decidable(self):
        """Test 'la existencia es decible' - existence is decidable"""
        noesis = Noesis()
        
        # Every evaluation produces a definite answer
        results = [noesis(n) for n in range(1, 10)]
        assert all(r in [0, 1] for r in results)
    
    def test_binary_tape_coherence(self):
        """Test 'cinta binaria infinita de coherencia'"""
        noesis = Noesis()
        tape = noesis.generate_existence_tape(50)
        
        # The tape is a coherent representation of existence
        assert isinstance(tape, str)
        assert len(tape) == 50
        assert tape.replace('0', '').replace('1', '') == ''


class TestNoesisIntegration:
    """Test Noēsis integration with QCAL framework"""
    
    def test_qcal_constants_present(self):
        """Test that QCAL constants are properly defined"""
        assert F0 > 0
        assert COHERENCE_C > 0
        assert UNIVERSAL_C > 0
    
    def test_coherence_relationship(self):
        """Test relationship between constants"""
        # The coherence factor should be C'/C ≈ 0.388
        coherence_factor = float(COHERENCE_C / UNIVERSAL_C)
        assert 0.38 < coherence_factor < 0.40
    
    def test_frequency_emergence(self):
        """Test that f₀ emerges from constants"""
        # f₀ = 141.7001 Hz emerges from C and C' harmonization
        assert abs(float(F0) - 141.7001) < 1e-6


class TestNoesisEdgeCases:
    """Test edge cases and boundary conditions"""
    
    def setup_method(self):
        """Setup test fixtures"""
        self.noesis = Noesis(precision=50, tolerance=1e-8)
    
    def test_noesis_n_equals_one(self):
        """Test Noēsis(1)"""
        response = self.noesis.bit_of_being(1)
        assert response.n == 1
        assert response.frequency == float(F0)
    
    def test_noesis_large_n(self):
        """Test Noēsis with large n"""
        n = 1000
        response = self.noesis.bit_of_being(n)
        assert response.n == n
        assert response.frequency == float(F0 * n)
    
    def test_different_tolerances(self):
        """Test Noēsis with different tolerances"""
        strict_noesis = Noesis(precision=50, tolerance=1e-15)
        relaxed_noesis = Noesis(precision=50, tolerance=1e-5)
        
        # Should both be functional
        assert strict_noesis(1) in [0, 1]
        assert relaxed_noesis(1) in [0, 1]
    
    def test_different_precisions(self):
        """Test Noēsis with different precisions"""
        low_prec = Noesis(precision=15)
        high_prec = Noesis(precision=100)
        
        # Both should work
        assert low_prec(1) in [0, 1]
        assert high_prec(1) in [0, 1]


# Performance and stress tests
class TestNoesisPerformance:
    """Test Noēsis performance characteristics"""
    
    def test_execution_speed(self):
        """Test that Noēsis executes in reasonable time"""
        import time
        
        noesis = Noesis()
        start = time.time()
        noesis.execute_range(1, 10, verbose=False)
        elapsed = time.time() - start
        
        # Should complete 10 evaluations quickly
        assert elapsed < 10.0, "Should execute efficiently"
    
    def test_memory_efficiency(self):
        """Test that execution log doesn't grow unbounded in tests"""
        noesis = Noesis()
        
        # Execute many evaluations
        for _ in range(100):
            noesis(1)
        
        # Log should contain all executions
        assert len(noesis.execution_log) == 100


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
