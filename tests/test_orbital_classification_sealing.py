#!/usr/bin/env python3
"""
Test suite for Orbital Classification Sealing validation
"""

import sys
from pathlib import Path

# Add parent directory to path
repo_root = Path(__file__).parent.parent
sys.path.insert(0, str(repo_root))

# Import the validation script
try:
    from validate_orbital_classification_sealing import (
        OrbitalSumReduction,
        VonMangoldtEmergence,
        TraceClassFubini
    )
    VALIDATION_AVAILABLE = True
except ImportError:
    VALIDATION_AVAILABLE = False
    print("Warning: Validation module not available")

# Try to import pytest, but provide fallback
try:
    import pytest
    PYTEST_AVAILABLE = True
except ImportError:
    PYTEST_AVAILABLE = False
    print("Warning: pytest not available, running tests directly")


class TestOrbitalClassificationSealing:
    """Test suite for BLOQUE #888888 - Orbital Classification Sealing"""
    
    def test_component1_orbital_sum_reduction(self):
        """Test Component 1: Orbital Sum Reduction to Prime Powers"""
        comp1 = OrbitalSumReduction(verbose=False)
        result = comp1.validate()
        
        assert result['status'] == 'PASSED', "Component 1 should pass all tests"
        assert result['component'] == 1
        assert len(result['tests']) == 2
        
        # Check individual tests
        for test in result['tests']:
            assert test['passed'], f"Test {test['test']} should pass"
    
    def test_component1_gaussian_concentration(self):
        """Test Gaussian kernel diagonal concentration"""
        comp1 = OrbitalSumReduction(verbose=False)
        result = comp1.validate_gaussian_concentration()
        
        assert result['passed'], "Gaussian concentration test should pass"
        assert result['on_diagonal'] > 0
        
        # Check decay ratios
        ratios = result['off_diagonal_ratios']
        assert ratios['distance_1'] < 1.0
        assert ratios['distance_2'] < ratios['distance_1']
        assert ratios['distance_5'] < ratios['distance_2']
    
    def test_component1_prime_power_sum(self):
        """Test prime power sum convergence"""
        comp1 = OrbitalSumReduction(verbose=False)
        result = comp1.validate_prime_power_sum()
        
        assert result['passed'], "Prime power sum should converge"
        assert result['total_sum'] > 0.1
        assert result['total_sum'] < 10.0
        assert result['num_terms'] > 0
    
    def test_component2_von_mangoldt_emergence(self):
        """Test Component 2: von Mangoldt Emergence via Haar Measure"""
        comp2 = VonMangoldtEmergence(verbose=False)
        result = comp2.validate()
        
        assert result['status'] == 'PASSED', "Component 2 should pass all tests"
        assert result['component'] == 2
        assert len(result['tests']) == 2
        
        for test in result['tests']:
            assert test['passed'], f"Test {test['test']} should pass"
    
    def test_component2_haar_volume_identity(self):
        """Test Haar volume identity: log p = Vol(ℤ_p×) = Λ(p)"""
        comp2 = VonMangoldtEmergence(verbose=False)
        result = comp2.validate_haar_volume_identity()
        
        assert result['passed'], "Haar volume identity should hold"
        assert result['max_error'] < 1e-10
        assert len(result['primes_tested']) > 0
        
        # Check that log p = Haar volume = von Mangoldt
        for prime_data in result['primes_tested']:
            assert abs(prime_data['log_p'] - prime_data['haar_volume']) < 1e-10
            assert abs(prime_data['log_p'] - prime_data['von_mangoldt']) < 1e-10
    
    def test_component2_transfer_coefficient(self):
        """Test transfer coefficient structure"""
        comp2 = VonMangoldtEmergence(verbose=False)
        result = comp2.validate_transfer_coefficient_structure()
        
        assert result['passed'], "Transfer coefficient structure should be correct"
        assert result['max_error'] < 1e-10
        
        # Check structure for each test case
        for case in result['test_cases']:
            assert abs(case['transfer_coeff'] - case['expected']) < 1e-10
    
    def test_component3_trace_class_fubini(self):
        """Test Component 3: Trace Class & Fubini Justification"""
        comp3 = TraceClassFubini(verbose=False)
        result = comp3.validate()
        
        assert result['status'] == 'PASSED', "Component 3 should pass all tests"
        assert result['component'] == 3
        assert len(result['tests']) == 3
        
        for test in result['tests']:
            assert test['passed'], f"Test {test['test']} should pass"
    
    def test_component3_agmon_decay(self):
        """Test Agmon exponential decay"""
        comp3 = TraceClassFubini(verbose=False)
        result = comp3.validate_agmon_decay()
        
        assert result['passed'], "Agmon decay should be exponential"
        assert result['fastest_decay'] < 1e-10
        
        # Check that decay accelerates with distance
        decay_rates = result['decay_rates']
        for i in range(len(decay_rates) - 1):
            assert decay_rates[i]['decay_rate'] > decay_rates[i+1]['decay_rate']
    
    def test_component3_nuclearity(self):
        """Test nuclearity (trace class property)"""
        comp3 = TraceClassFubini(verbose=False)
        result = comp3.validate_nuclearity()
        
        assert result['passed'], "Operator should be trace class"
        assert result['finite_sum'] < 10
        assert result['tail_estimate'] < 1e-6
        assert result['total_trace_norm'] < float('inf')
    
    def test_component3_fubini_convergence(self):
        """Test Fubini absolute convergence"""
        comp3 = TraceClassFubini(verbose=False)
        result = comp3.validate_fubini_convergence()
        
        assert result['passed'], "Double sum should converge absolutely"
        assert result['double_sum'] < 100
        assert result['num_primes'] > 0
        assert result['num_powers'] > 0
    
    def test_von_mangoldt_function_accuracy(self):
        """Test von Mangoldt function for prime powers"""
        comp2 = VonMangoldtEmergence(verbose=False)
        
        import numpy as np
        
        # Test for primes
        assert abs(comp2.von_mangoldt(2) - np.log(2)) < 1e-10
        assert abs(comp2.von_mangoldt(3) - np.log(3)) < 1e-10
        assert abs(comp2.von_mangoldt(5) - np.log(5)) < 1e-10
        
        # Test for prime powers
        assert abs(comp2.von_mangoldt(4) - np.log(2)) < 1e-10  # 4 = 2^2
        assert abs(comp2.von_mangoldt(8) - np.log(2)) < 1e-10  # 8 = 2^3
        assert abs(comp2.von_mangoldt(9) - np.log(3)) < 1e-10  # 9 = 3^2
        
        # Test for non-prime-powers
        assert comp2.von_mangoldt(6) == 0.0  # 6 = 2*3
        assert comp2.von_mangoldt(10) == 0.0  # 10 = 2*5
    
    def test_v_eff_coercivity(self):
        """Test effective potential coercivity"""
        comp3 = TraceClassFubini(verbose=False)
        
        # V_eff should grow linearly
        u_values = [5, 10, 15, 20]
        v_values = [comp3.V_eff(u) for u in u_values]
        
        # Check monotonic growth
        for i in range(len(v_values) - 1):
            assert v_values[i] < v_values[i+1], "V_eff should be monotonically increasing"
        
        # Check approximately linear growth for large u
        for u in u_values:
            v = comp3.V_eff(u)
            # V_eff(u) ~ u for large u (since log(1+exp(u)) ~ u)
            # Allow generous margin since V_eff has epsilon subtraction
            assert abs(v - u) < 2.0, f"V_eff({u}) should be close to {u}"
    
    def test_eigenvalue_estimate_growth(self):
        """Test WKB eigenvalue estimate growth"""
        comp3 = TraceClassFubini(verbose=False)
        
        # λₙ ~ n log(n+1)
        eigenvalues = [comp3.eigenvalue_estimate(n) for n in range(1, 11)]
        
        # Check monotonic growth
        for i in range(len(eigenvalues) - 1):
            assert eigenvalues[i] < eigenvalues[i+1], "Eigenvalues should grow monotonically"
        
        # Check growth rate is roughly n log n
        import numpy as np
        for n in [10, 20, 50, 100]:
            est = comp3.eigenvalue_estimate(n)
            expected = n * np.log(n + 1)
            # Should be close to n log(n+1)
            assert abs(est - expected) < 0.1, f"Eigenvalue estimate at n={n} should match WKB"


def test_full_validation():
    """Test full BLOQUE #888888 validation"""
    if not VALIDATION_AVAILABLE:
        print("SKIP: Validation module not available")
        return True
    
    # Component 1
    comp1 = OrbitalSumReduction(verbose=False)
    result1 = comp1.validate()
    assert result1['status'] == 'PASSED'
    
    # Component 2
    comp2 = VonMangoldtEmergence(verbose=False)
    result2 = comp2.validate()
    assert result2['status'] == 'PASSED'
    
    # Component 3
    comp3 = TraceClassFubini(verbose=False)
    result3 = comp3.validate()
    assert result3['status'] == 'PASSED'
    
    # All components should pass
    all_passed = all([
        result1['status'] == 'PASSED',
        result2['status'] == 'PASSED',
        result3['status'] == 'PASSED'
    ])
    assert all_passed, "All three components of BLOQUE #888888 should pass"
    return True


def run_all_tests():
    """Run all tests manually if pytest not available"""
    if not VALIDATION_AVAILABLE:
        print("ERROR: Validation module not available")
        return False
    
    test_obj = TestOrbitalClassificationSealing()
    tests = [
        ('Component 1: Orbital Sum Reduction', test_obj.test_component1_orbital_sum_reduction),
        ('Component 1: Gaussian Concentration', test_obj.test_component1_gaussian_concentration),
        ('Component 1: Prime Power Sum', test_obj.test_component1_prime_power_sum),
        ('Component 2: von Mangoldt Emergence', test_obj.test_component2_von_mangoldt_emergence),
        ('Component 2: Haar Volume Identity', test_obj.test_component2_haar_volume_identity),
        ('Component 2: Transfer Coefficient', test_obj.test_component2_transfer_coefficient),
        ('Component 3: Trace Class Fubini', test_obj.test_component3_trace_class_fubini),
        ('Component 3: Agmon Decay', test_obj.test_component3_agmon_decay),
        ('Component 3: Nuclearity', test_obj.test_component3_nuclearity),
        ('Component 3: Fubini Convergence', test_obj.test_component3_fubini_convergence),
        ('von Mangoldt Function Accuracy', test_obj.test_von_mangoldt_function_accuracy),
        ('V_eff Coercivity', test_obj.test_v_eff_coercivity),
        ('Eigenvalue Estimate Growth', test_obj.test_eigenvalue_estimate_growth),
        ('Full Validation', test_full_validation),
    ]
    
    passed = 0
    failed = 0
    
    print("\n" + "="*70)
    print("Running Orbital Classification Sealing Tests")
    print("="*70 + "\n")
    
    for test_name, test_func in tests:
        try:
            test_func()
            print(f"✓ {test_name}")
            passed += 1
        except Exception as e:
            print(f"✗ {test_name}: {e}")
            failed += 1
    
    print("\n" + "="*70)
    print(f"Test Results: {passed} passed, {failed} failed")
    print("="*70 + "\n")
    
    return failed == 0


if __name__ == "__main__":
    if PYTEST_AVAILABLE:
        pytest.main([__file__, "-v"])
    else:
        success = run_all_tests()
        sys.exit(0 if success else 1)
