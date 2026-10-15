#!/usr/bin/env python3
"""
Tests for V13 Hilbert-Pólya Elevation Validator

Tests validation of:
- Camino A: Adelic kernel closure
- Camino B: Spectral universality
- Camino C: Mandatory scaling law
- Kernel-Duro protocol

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
"""

import pytest
import sys
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from validate_v13_hilbert_polya_elevation import (
    V13HilbertPolyaElevationValidator,
    KAPPA_PI,
    F0,
    C_QCAL,
    ERROR_THRESHOLD
)


class TestV13HilbertPolyaElevationValidator:
    """Test suite for V13 Hilbert-Pólya elevation validator."""
    
    def setup_method(self):
        """Set up test fixtures."""
        self.validator = V13HilbertPolyaElevationValidator(verbose=False)
    
    def test_initialization(self):
        """Test validator initialization."""
        assert self.validator is not None
        assert isinstance(self.validator.results, dict)
        assert 'timestamp' in self.validator.results
        assert self.validator.verbose == False
    
    def test_constants(self):
        """Test QCAL constants."""
        assert KAPPA_PI == 2.577310
        assert F0 == 141.7001
        assert C_QCAL == 244.36
        assert 0 < ERROR_THRESHOLD < 1
    
    def test_camino_a_validation(self):
        """Test Camino A: Adelic kernel closure validation."""
        success, details = self.validator.validate_camino_a_kernel_weil()
        
        # Should return tuple
        assert isinstance(success, bool)
        assert isinstance(details, dict)
        
        # Check required keys
        assert 'kernel_defined' in details
        assert 'poisson_sum' in details
        assert 'weyl_term' in details
        assert 'orbit_term' in details
        assert 'remainder_bounded' in details
        
        # All checks should pass
        assert success is True
        assert all(details.values())
    
    def test_camino_b_validation(self):
        """Test Camino B: Spectral universality validation."""
        success, details = self.validator.validate_camino_b_universality()
        
        # Should return tuple
        assert isinstance(success, bool)
        assert isinstance(details, dict)
        
        # Check required keys
        assert 'basis_invariance' in details
        assert 'spectral_collapse' in details
        assert 'rigidity_law' in details
        assert 'discretization_immunity' in details
        assert 'topological_invariance' in details
        
        # All checks should pass
        assert success is True
        assert all(details.values())
    
    @pytest.mark.slow
    def test_camino_c_validation(self):
        """Test Camino C: Scaling law validation."""
        success, details = self.validator.validate_camino_c_scaling_law()
        
        # Should return tuple
        assert isinstance(success, bool)
        assert isinstance(details, dict)
        
        # Check required keys
        assert 'v13_executed' in details
        assert 'kappa_inf' in details
        assert 'error_percent' in details
        assert 'alpha' in details
        
        # If V13 executed, validate results
        if details['v13_executed']:
            assert details['kappa_inf'] is not None
            assert details['error_percent'] is not None
            assert details['alpha'] is not None
            
            # Kappa should be close to target
            assert 2.5 < details['kappa_inf'] < 2.6
            
            # Error should be small
            assert details['error_percent'] < 5.0  # 5% tolerance for tests
            
            # Alpha should be in reasonable range
            assert 0.3 < details['alpha'] < 1.2
    
    def test_kernel_duro_validation(self):
        """Test Kernel-Duro protocol validation."""
        success, details = self.validator.validate_kernel_duro_protocol()
        
        # Should return tuple
        assert isinstance(success, bool)
        assert isinstance(details, dict)
        
        # Check required categories
        assert 'espacio_fase' in details
        assert 'cuantizacion' in details
        assert 'traza' in details
        assert 'constante_kappa' in details
        
        # Each category should have sub-checks
        assert isinstance(details['espacio_fase'], dict)
        assert isinstance(details['cuantizacion'], dict)
        assert isinstance(details['traza'], dict)
        assert isinstance(details['constante_kappa'], dict)
        
        # All checks should pass
        assert success is True
    
    def test_espacio_fase_checks(self):
        """Test phase space checks in Kernel-Duro."""
        success, details = self.validator.validate_kernel_duro_protocol()
        
        espacio_fase = details['espacio_fase']
        assert espacio_fase['adelic_torus'] is True
        assert espacio_fase['closed_orbits'] is True
        assert espacio_fase['prime_ideals'] is True
    
    def test_cuantizacion_checks(self):
        """Test quantization checks in Kernel-Duro."""
        success, details = self.validator.validate_kernel_duro_protocol()
        
        cuantizacion = details['cuantizacion']
        assert cuantizacion['operator_defined'] is True
        assert cuantizacion['self_adjoint'] is True
        assert cuantizacion['real_spectrum'] is True
    
    def test_traza_checks(self):
        """Test trace checks in Kernel-Duro."""
        success, details = self.validator.validate_kernel_duro_protocol()
        
        traza = details['traza']
        assert traza['gutzwiller_trace'] is True
        assert traza['factor_1_over_k'] is True
        assert traza['weil_connection'] is True
    
    def test_constante_kappa_checks(self):
        """Test kappa constant checks in Kernel-Duro."""
        success, details = self.validator.validate_kernel_duro_protocol()
        
        constante = details['constante_kappa']
        assert constante['compactness_forced'] is True
        assert constante['kappa_anchored'] is True
    
    @pytest.mark.slow
    def test_full_validation(self):
        """Test complete validation pipeline."""
        success = self.validator.run_full_validation()
        
        # Should return boolean
        assert isinstance(success, bool)
        
        # Results should be populated
        assert self.validator.results['camino_a'] is not None
        assert self.validator.results['camino_b'] is not None
        assert self.validator.results['camino_c'] is not None
        assert self.validator.results['kernel_duro'] is not None
        assert self.validator.results['overall_status'] is not None
        
        # Each result should have success and details
        for key in ['camino_a', 'camino_b', 'kernel_duro']:
            assert 'success' in self.validator.results[key]
            assert 'details' in self.validator.results[key]
    
    def test_results_structure(self):
        """Test results dictionary structure."""
        # Run minimal validation
        self.validator.validate_camino_a_kernel_weil()
        
        # Check structure
        assert 'timestamp' in self.validator.results
        assert 'camino_a' in self.validator.results
        assert 'camino_b' in self.validator.results
        assert 'camino_c' in self.validator.results
        assert 'kernel_duro' in self.validator.results
        assert 'overall_status' in self.validator.results
    
    def test_save_results(self):
        """Test results saving to JSON."""
        # Run validation
        self.validator.validate_camino_a_kernel_weil()
        
        # Save to temp file
        import tempfile
        with tempfile.NamedTemporaryFile(mode='w', suffix='.json', delete=False) as f:
            temp_path = f.name
        
        try:
            # Override save path
            from pathlib import Path
            temp_file = Path(temp_path).name
            self.validator.save_results(temp_file)
            
            # Check file exists
            expected_path = Path(__file__).parent.parent / 'data' / temp_file
            if expected_path.exists():
                # Verify JSON is valid
                import json
                with open(expected_path, 'r') as f:
                    data = json.load(f)
                
                assert 'timestamp' in data
                assert 'camino_a' in data
                
                # Clean up
                expected_path.unlink()
        finally:
            # Clean up temp file
            Path(temp_path).unlink(missing_ok=True)
    
    def test_verbose_mode(self):
        """Test verbose and non-verbose modes."""
        # Verbose mode
        validator_verbose = V13HilbertPolyaElevationValidator(verbose=True)
        assert validator_verbose.verbose is True
        
        # Non-verbose mode
        validator_quiet = V13HilbertPolyaElevationValidator(verbose=False)
        assert validator_quiet.verbose is False
    
    def test_print_method(self):
        """Test internal print method."""
        # Should not raise in verbose mode
        validator_verbose = V13HilbertPolyaElevationValidator(verbose=True)
        validator_verbose._print("Test message", 'info')
        validator_verbose._print("Success", 'success')
        validator_verbose._print("Warning", 'warning')
        validator_verbose._print("Error", 'error')
        validator_verbose._print("Section", 'section')
        
        # Should not raise in quiet mode
        validator_quiet = V13HilbertPolyaElevationValidator(verbose=False)
        validator_quiet._print("Test message", 'info')


class TestIntegration:
    """Integration tests with existing V13 framework."""
    
    def test_kappa_pi_consistency(self):
        """Test KAPPA_PI value consistency."""
        from validate_v13_hilbert_polya_elevation import KAPPA_PI as hp_kappa
        
        try:
            from v13_limit_validator import KAPPA_PI as v13_kappa
            assert hp_kappa == v13_kappa
        except ImportError:
            # V13 module not available, just check value
            assert hp_kappa == 2.577310
    
    def test_f0_consistency(self):
        """Test F0 frequency consistency."""
        from validate_v13_hilbert_polya_elevation import F0 as hp_f0
        
        try:
            from v13_limit_validator import F0 as v13_f0
            assert hp_f0 == v13_f0
        except ImportError:
            # V13 module not available, just check value
            assert hp_f0 == 141.7001
    
    def test_c_qcal_consistency(self):
        """Test C_QCAL coherence constant consistency."""
        from validate_v13_hilbert_polya_elevation import C_QCAL as hp_c
        
        try:
            from v13_limit_validator import C_QCAL as v13_c
            assert hp_c == v13_c
        except ImportError:
            # V13 module not available, just check value
            assert hp_c == 244.36


class TestMathematicalProperties:
    """Tests for mathematical properties and constraints."""
    
    def test_error_threshold(self):
        """Test error threshold is reasonable."""
        assert ERROR_THRESHOLD == 0.01  # 1%
        assert ERROR_THRESHOLD > 0
        assert ERROR_THRESHOLD < 0.1  # Less than 10%
    
    def test_kappa_pi_range(self):
        """Test κ_Π is in expected range."""
        # Based on literature (Berry-Keating, etc.)
        assert 2.5 < KAPPA_PI < 2.6
        assert KAPPA_PI == 2.577310
    
    def test_frequency_range(self):
        """Test fundamental frequency is in expected range."""
        assert 140 < F0 < 145
        assert F0 == 141.7001
    
    def test_coherence_constant_range(self):
        """Test QCAL coherence constant is reasonable."""
        assert 200 < C_QCAL < 300
        assert C_QCAL == 244.36


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
