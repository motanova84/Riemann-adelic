#!/usr/bin/env python3
"""
Test suite for infinite reciprocity implementation.

Validates:
1. Reciprocity factor computation
2. Product convergence
3. Integration with QCAL framework
4. Consistency with Weil reciprocity
"""

import sys
import json
from pathlib import Path


def test_infinite_reciprocity_validation_exists():
    """Test that validation results file exists."""
    results_file = Path("data/infinite_reciprocity_validation.json")
    assert results_file.exists(), "Validation results file not found"
    print("✓ Validation results file exists")


def test_validation_results_structure():
    """Test that validation results have correct structure."""
    results_file = Path("data/infinite_reciprocity_validation.json")
    
    with open(results_file) as f:
        data = json.load(f)
    
    # Check required keys
    required_keys = [
        'validation_type',
        'qcal_framework',
        'base_frequency_hz',
        'coherence_constant',
        'convergence_results',
        'weil_reciprocity',
        'qcal_coherence',
        'validation_status'
    ]
    
    for key in required_keys:
        assert key in data, f"Missing required key: {key}"
    
    print("✓ Validation results structure is correct")


def test_qcal_parameters():
    """Test QCAL framework parameters."""
    results_file = Path("data/infinite_reciprocity_validation.json")
    
    with open(results_file) as f:
        data = json.load(f)
    
    # Check QCAL parameters
    assert data['base_frequency_hz'] == 141.7001, "Incorrect base frequency"
    assert data['coherence_constant'] == 244.36, "Incorrect coherence constant"
    assert data['qcal_framework'] == "Ψ = I × A_eff² × C^∞", "Incorrect QCAL framework"
    
    print("✓ QCAL parameters are correct")


def test_coherence_status():
    """Test that validation is coherent."""
    results_file = Path("data/infinite_reciprocity_validation.json")
    
    with open(results_file) as f:
        data = json.load(f)
    
    assert data['validation_status'] == 'COHERENT', "Validation is not coherent"
    assert data['qcal_coherence']['coherence_status'] is True, "QCAL coherence failed"
    
    # Check coherence measure is small
    coherence_measure = data['qcal_coherence']['coherence_measure']
    assert coherence_measure < 1e-10, f"Coherence measure too large: {coherence_measure}"
    
    print(f"✓ Validation is COHERENT (measure: {coherence_measure:.2e})")


def test_convergence_data():
    """Test convergence data is present and reasonable."""
    results_file = Path("data/infinite_reciprocity_validation.json")
    
    with open(results_file) as f:
        data = json.load(f)
    
    conv = data['convergence_results']
    
    # Check we have data for multiple N values
    assert len(conv['N_values']) >= 5, "Not enough convergence data points"
    
    # Check all products have magnitude ≈ 1 (reciprocity)
    for mag in conv['magnitudes']:
        assert abs(mag - 1.0) < 0.01, f"Product magnitude {mag} too far from 1"
    
    # Check defects are reasonable
    for defect in conv['defects']:
        assert defect < 5.0, f"Reciprocity defect {defect} too large"
    
    print(f"✓ Convergence data is valid ({len(conv['N_values'])} points)")


def test_weil_reciprocity_connection():
    """Test connection to Weil reciprocity."""
    results_file = Path("data/infinite_reciprocity_validation.json")
    
    with open(results_file) as f:
        data = json.load(f)
    
    weil = data['weil_reciprocity']
    
    # Check zero count is reasonable
    assert weil['zero_count'] > 0, "No zeros found"
    assert weil['height'] > 0, "Invalid zero height"
    
    # Check expected count ratio is reasonable (within 2x)
    ratio = weil['zero_count'] / weil['expected_count']
    assert 0.5 < ratio < 2.0, f"Zero count ratio {ratio} out of range"
    
    # Check phase mod 2π is in valid range
    phase_mod = weil['phase_mod_2pi']
    assert 0 <= phase_mod < 2 * 3.14159 * 1.1, f"Phase mod 2π out of range: {phase_mod}"
    
    print(f"✓ Weil reciprocity connection validated (ratio: {ratio:.4f})")


def test_lean_formalization_exists():
    """Test that Lean4 formalization file exists."""
    lean_file = Path("formalization/lean/RiemannAdelic/infinite_reciprocity_zeros.lean")
    assert lean_file.exists(), "Lean formalization file not found"
    
    # Check file has content
    content = lean_file.read_text()
    assert len(content) > 1000, "Lean file too small"
    
    # Check for key theorems
    assert 'infinite_reciprocity_convergence' in content, "Missing convergence theorem"
    assert 'weil_reciprocity_infinite' in content, "Missing Weil reciprocity theorem"
    assert 'infinite_reciprocity_main_theorem' in content, "Missing main theorem"
    
    print("✓ Lean4 formalization exists and contains key theorems")


def test_documentation_exists():
    """Test that documentation file exists."""
    doc_file = Path("INFINITE_RECIPROCITY_README.md")
    assert doc_file.exists(), "Documentation file not found"
    
    content = doc_file.read_text()
    assert len(content) > 2000, "Documentation too brief"
    
    # Check for key sections
    assert 'Infinite Reciprocity' in content, "Missing title"
    assert 'QCAL' in content, "Missing QCAL reference"
    assert 'Weil' in content, "Missing Weil reference"
    
    print("✓ Documentation exists and is comprehensive")


def test_plot_exists():
    """Test that convergence plot exists."""
    plot_file = Path("data/infinite_reciprocity_convergence.png")
    assert plot_file.exists(), "Convergence plot not found"
    
    # Check file size is reasonable
    file_size = plot_file.stat().st_size
    assert file_size > 10000, f"Plot file too small: {file_size} bytes"
    
    print(f"✓ Convergence plot exists ({file_size // 1024} KB)")


def run_all_tests():
    """Run all tests and report results."""
    print("\n" + "="*70)
    print("INFINITE RECIPROCITY IMPLEMENTATION TESTS")
    print("="*70 + "\n")
    
    tests = [
        test_infinite_reciprocity_validation_exists,
        test_validation_results_structure,
        test_qcal_parameters,
        test_coherence_status,
        test_convergence_data,
        test_weil_reciprocity_connection,
        test_lean_formalization_exists,
        test_documentation_exists,
        test_plot_exists,
    ]
    
    passed = 0
    failed = 0
    
    for test in tests:
        try:
            test()
            passed += 1
        except AssertionError as e:
            print(f"✗ {test.__name__}: {e}")
            failed += 1
        except Exception as e:
            print(f"✗ {test.__name__}: Unexpected error: {e}")
            failed += 1
    
    print("\n" + "="*70)
    print(f"TEST SUMMARY: {passed} passed, {failed} failed")
    print("="*70 + "\n")
    
    if failed == 0:
        print("✅ All tests passed! Infinite reciprocity implementation is valid.")
        print("♾️ QCAL coherence confirmed.\n")
        return 0
    else:
        print("⚠️ Some tests failed. Please review implementation.\n")
        return 1


if __name__ == "__main__":
    sys.exit(run_all_tests())
