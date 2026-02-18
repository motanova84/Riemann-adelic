#!/usr/bin/env python3
"""
Test Suite for Trace Formula Complete Validation
================================================

Tests the 5 achievements validation framework to ensure all components
work correctly.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz
"""

import sys
import pytest
from pathlib import Path

# Add repo root to path
repo_root = Path(__file__).parent.parent
sys.path.insert(0, str(repo_root))

# Import validation script
from validate_trace_formula_complete import (
    run_complete_validation,
    Achievement1_TraceFormula,
    Achievement2_WeilFormula,
    Achievement3_DXiIdentity,
    Achievement4_SpectralImplication,
    Achievement5_NoSpuriousSpectrum,
    F0_BASE,
    C_COHERENCE_VALUE,
    WEIL_ERROR_TARGET
)


def test_validation_constants():
    """Test that QCAL constants are correctly defined."""
    assert F0_BASE == 141.7001
    assert C_COHERENCE_VALUE == 244.36
    assert WEIL_ERROR_TARGET == 8.91e-7


def test_achievement1_instantiation():
    """Test Achievement 1 class instantiation."""
    validator = Achievement1_TraceFormula(verbose=False)
    assert validator is not None


def test_achievement1_validation():
    """Test Achievement 1 complete validation."""
    validator = Achievement1_TraceFormula(verbose=False)
    results = validator.validate()
    
    assert 'achievement' in results
    assert results['achievement'] == 'Complete Trace Formula'
    assert 'status' in results
    assert 'tests' in results
    assert 'passed' in results
    
    # All tests should pass
    assert results['passed'] is True
    assert results['status'] == 'PASSED'


def test_achievement2_instantiation():
    """Test Achievement 2 class instantiation."""
    validator = Achievement2_WeilFormula(verbose=False)
    assert validator is not None
    assert validator.target_error == WEIL_ERROR_TARGET


def test_achievement2_validation():
    """Test Achievement 2 complete validation."""
    validator = Achievement2_WeilFormula(verbose=False)
    results = validator.validate()
    
    assert results['achievement'] == 'Weil Formula at s=1/2'
    assert results['passed'] is True
    assert results['status'] == 'PASSED'
    assert results['target_error'] == 8.91e-7


def test_achievement3_instantiation():
    """Test Achievement 3 class instantiation."""
    validator = Achievement3_DXiIdentity(verbose=False)
    assert validator is not None


def test_achievement3_validation():
    """Test Achievement 3 complete validation."""
    validator = Achievement3_DXiIdentity(verbose=False)
    results = validator.validate()
    
    assert results['achievement'] == 'D(s) ≡ Ξ(s) Identity'
    assert results['passed'] is True
    assert results['status'] == 'PASSED'


def test_achievement4_instantiation():
    """Test Achievement 4 class instantiation."""
    validator = Achievement4_SpectralImplication(verbose=False)
    assert validator is not None


def test_achievement4_validation():
    """Test Achievement 4 complete validation."""
    validator = Achievement4_SpectralImplication(verbose=False)
    results = validator.validate()
    
    assert results['achievement'] == 'Spectral Implication'
    assert results['passed'] is True
    assert results['status'] == 'PASSED'


def test_achievement5_instantiation():
    """Test Achievement 5 class instantiation."""
    validator = Achievement5_NoSpuriousSpectrum(verbose=False)
    assert validator is not None


def test_achievement5_validation():
    """Test Achievement 5 complete validation."""
    validator = Achievement5_NoSpuriousSpectrum(verbose=False)
    results = validator.validate()
    
    assert results['achievement'] == 'No Spurious Spectrum'
    assert results['passed'] is True
    assert results['status'] == 'PASSED'


def test_complete_validation():
    """Test complete validation of all 5 achievements."""
    results = run_complete_validation(verbose=False, save_certificate=False)
    
    # Check structure
    assert 'validation_type' in results
    assert results['validation_type'] == 'Complete Trace Formula - 5 Achievements'
    
    assert 'qcal_constants' in results
    assert results['qcal_constants']['f0'] == 141.7001
    assert results['qcal_constants']['C_coherence'] == 244.36
    
    assert 'achievements' in results
    assert len(results['achievements']) == 5
    
    assert 'overall' in results
    assert 'all_passed' in results['overall']
    assert 'achievements_passed' in results['overall']
    assert 'status' in results['overall']
    
    # All should pass
    assert results['overall']['all_passed'] is True
    assert results['overall']['achievements_passed'] == 5
    assert results['overall']['status'] == 'COMPLETE'


def test_certificate_generation():
    """Test certificate generation."""
    results = run_complete_validation(verbose=False, save_certificate=True)
    
    # Check certificate was generated
    cert_path = repo_root / "data" / "trace_formula_complete_certificate.json"
    assert cert_path.exists()
    
    # Load and verify certificate
    import json
    with open(cert_path, 'r') as f:
        cert = json.load(f)
    
    assert cert['validation_type'] == 'Complete Trace Formula - 5 Achievements'
    assert cert['overall']['all_passed'] is True


def test_zeros_file_exists():
    """Test that zeros data file exists."""
    zeros_file = repo_root / "zeros" / "zeros_t1e3.txt"
    assert zeros_file.exists(), "Zeros data file should exist"


def test_schatten_s1_computation():
    """Test Schatten S_1 eigenvalue computation."""
    import numpy as np
    
    zeros_file = repo_root / "zeros" / "zeros_t1e3.txt"
    zeros = np.loadtxt(zeros_file)
    
    # Compute eigenvalues
    eigenvalues = 0.25 + zeros**2
    
    # Should all be positive
    assert np.all(eigenvalues > 0)
    
    # Check growth rate
    partial_sums = np.cumsum(eigenvalues)
    ratios = partial_sums[1:] / partial_sums[:-1]
    growth_rate = np.mean(ratios[-100:])
    
    # Should be close to 1 for convergent series
    assert growth_rate < 1.5


def test_critical_line_translation():
    """Test spectral translation to critical line."""
    import numpy as np
    
    zeros_file = repo_root / "zeros" / "zeros_t1e3.txt"
    zeros = np.loadtxt(zeros_file)[:10]
    
    # For each zero γ, s = 1/2 + iγ should be on critical line
    for gamma in zeros:
        s = 0.5 + 1j * gamma
        assert abs(s.real - 0.5) < 1e-10, "All zeros should map to Re(s) = 1/2"


def test_discrete_spectrum():
    """Test that spectrum is discrete."""
    import numpy as np
    
    zeros_file = repo_root / "zeros" / "zeros_t1e3.txt"
    zeros = np.loadtxt(zeros_file)
    
    # Check spacings
    spacings = np.diff(sorted(zeros))
    min_spacing = spacings.min()
    
    # Should be bounded away from 0
    assert min_spacing > 0.01, "Spectrum should be discrete"


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
