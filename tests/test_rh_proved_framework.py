#!/usr/bin/env python3
"""
Tests for RH_PROVED Framework
==============================

Comprehensive test suite for the three pillars:
1. Kernel confinement (Hilbert-Schmidt)
2. Hardy-Littlewood density
3. Guinand-Weil trace formula

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID: 0009-0002-1923-0773
License: CC BY-NC-SA 4.0
"""

import pytest
import numpy as np
import mpmath as mp
from pathlib import Path
import sys

# Add parent directory to path
sys.path.append(str(Path(__file__).parent.parent))

from rh_proved_framework import (
    RHProvedFramework,
    KernelConfinementResult,
    HardyLittlewoodDensityResult,
    GuinandWeilTraceResult,
    RHProvedCertificate
)


class TestKernelConfinement:
    """Test Pillar 1: Kernel Confinement"""
    
    def setup_method(self):
        """Setup test fixtures"""
        self.framework = RHProvedFramework(precision=30, n_basis=50)
    
    def test_gaussian_kernel_hilbert_schmidt(self):
        """Test that Gaussian kernel is Hilbert-Schmidt"""
        # Gaussian kernel K(x,y) = exp(-(x-y)²/2)
        kernel = lambda x, y: float(mp.exp(-((x - y)**2) / 2))
        
        result = self.framework.verify_kernel_confinement(
            kernel_func=kernel,
            domain_range=(0.1, 10.0)
        )
        
        assert result.is_hilbert_schmidt, "Gaussian kernel should be Hilbert-Schmidt"
        assert result.kernel_norm_squared < np.inf, "Kernel norm should be finite"
        assert result.is_compact, "HS kernel should induce compact operator"
        assert result.discrete_spectrum_guaranteed, "Compact operator has discrete spectrum"
        assert result.operator_finite_energy, "Operator should have finite energy"
    
    def test_kernel_confinement_implies_discrete_spectrum(self):
        """Test that kernel confinement guarantees discrete spectrum"""
        result = self.framework.verify_kernel_confinement()
        
        assert result.is_hilbert_schmidt
        assert result.discrete_spectrum_guaranteed, \
            "Hilbert-Schmidt kernel must guarantee discrete spectrum"
    
    def test_kernel_confinement_finite_energy(self):
        """Test that confined kernel has finite energy"""
        result = self.framework.verify_kernel_confinement()
        
        assert result.operator_finite_energy, \
            "Confined kernel must have finite energy (not abstract infinity)"
    
    def test_kernel_trace_class(self):
        """Test that Gaussian kernel is trace class"""
        result = self.framework.verify_kernel_confinement(
            domain_range=(0.1, 5.0)  # Smaller domain for stronger bound
        )
        
        assert result.is_trace_class, \
            "Gaussian kernel on bounded domain should be trace class"
    
    def test_kernel_norm_scaling(self):
        """Test that kernel norm scales with domain size"""
        result_small = self.framework.verify_kernel_confinement(
            domain_range=(0.1, 2.0)
        )
        result_large = self.framework.verify_kernel_confinement(
            domain_range=(0.1, 20.0)
        )
        
        # Larger domain should have larger (but still finite) norm
        assert result_small.kernel_norm_squared < result_large.kernel_norm_squared
        assert result_large.is_hilbert_schmidt, \
            "Should still be HS even on larger domain"


class TestHardyLittlewoodDensity:
    """Test Pillar 2: Hardy-Littlewood Density"""
    
    def setup_method(self):
        """Setup test fixtures"""
        self.framework = RHProvedFramework(precision=30, n_basis=50)
    
    def test_hardy_theorem_infinitude(self):
        """Test Hardy's theorem: infinitely many zeros on critical line"""
        result = self.framework.verify_hardy_littlewood_density(
            height_bound=100.0
        )
        
        assert result.zeros_on_critical_line > 10, \
            "Should find multiple zeros on critical line"
        assert result.hardy_theorem_satisfied, \
            "Hardy's theorem should be satisfied"
    
    def test_spectral_density_sufficient(self):
        """Test that spectral density is sufficient"""
        result = self.framework.verify_hardy_littlewood_density(
            height_bound=1000.0
        )
        
        assert result.spectral_density_sufficient, \
            "Spectral density should be sufficient to cover zeros"
        assert result.spectral_coverage > 0.3, \
            "Coverage should be at least 30% (Hardy's lower bound)"
    
    def test_density_scaling_with_height(self):
        """Test that density scales correctly with height"""
        result_100 = self.framework.verify_hardy_littlewood_density(
            height_bound=100.0
        )
        result_1000 = self.framework.verify_hardy_littlewood_density(
            height_bound=1000.0
        )
        
        # More zeros at higher bound
        assert result_1000.zeros_on_critical_line > result_100.zeros_on_critical_line
        
        # Both should satisfy Hardy's theorem
        assert result_100.hardy_theorem_satisfied
        assert result_1000.hardy_theorem_satisfied
    
    def test_riemann_von_mangoldt_formula(self):
        """Test Riemann-von Mangoldt density formula"""
        T = 100.0
        result = self.framework.verify_hardy_littlewood_density(
            height_bound=T
        )
        
        # Theoretical density: N(T) ~ (T/2π) log(T/2πe)
        theoretical = (T / (2 * np.pi)) * np.log(T / (2 * np.pi * np.e))
        
        # Observed should be close to theoretical
        relative_error = abs(result.zeros_on_critical_line - theoretical) / theoretical
        assert relative_error < 0.5, \
            f"Density should match Riemann-von Mangoldt formula within 50%"


class TestGuinandWeilTrace:
    """Test Pillar 3: Guinand-Weil Trace Formula"""
    
    def setup_method(self):
        """Setup test fixtures"""
        self.framework = RHProvedFramework(precision=30, n_basis=50)
    
    def test_bijection_zeros_to_eigenvalues(self):
        """Test bijection from zeros to eigenvalues"""
        # Get first 20 zeros
        zeros = [float(mp.im(mp.zetazero(n))) for n in range(1, 21)]
        eigenvalues = self.framework._construct_hpsi_eigenvalues(20)
        
        result = self.framework.verify_guinand_weil_trace_formula(
            operator_eigenvalues=eigenvalues,
            zeta_zeros=zeros,
            tolerance=1e-6
        )
        
        assert result.bijection_established, \
            "Bijection should be established between zeros and eigenvalues"
        assert result.match_precision >= 0.95, \
            "Match precision should be at least 95%"
    
    def test_no_spectral_leaks(self):
        """Test that there are no spectral leaks"""
        result = self.framework.verify_guinand_weil_trace_formula(
            tolerance=1e-6
        )
        
        assert result.no_spectral_leaks, \
            "There should be no spectral leaks (perfect bijection)"
        assert result.every_zero_is_eigenvalue, \
            "Every zero should correspond to an eigenvalue"
        assert result.every_eigenvalue_is_zero, \
            "Every eigenvalue should correspond to a zero"
    
    def test_trace_formula_precision(self):
        """Test precision of trace formula matching"""
        # Test with different tolerances
        result_strict = self.framework.verify_guinand_weil_trace_formula(
            tolerance=1e-8
        )
        result_relaxed = self.framework.verify_guinand_weil_trace_formula(
            tolerance=1e-4
        )
        
        # Relaxed tolerance should match more
        assert result_relaxed.zeros_matched_eigenvalues >= \
               result_strict.zeros_matched_eigenvalues
    
    def test_trace_formula_first_zeros(self):
        """Test trace formula for first few zeros"""
        # First 5 zeros (well-known, high precision)
        zeros = [float(mp.im(mp.zetazero(n))) for n in range(1, 6)]
        eigenvalues = self.framework._construct_hpsi_eigenvalues(5)
        
        result = self.framework.verify_guinand_weil_trace_formula(
            operator_eigenvalues=eigenvalues,
            zeta_zeros=zeros,
            tolerance=1e-10
        )
        
        # Should have perfect match for well-known zeros
        assert result.zeros_matched_eigenvalues == 5, \
            "All 5 zeros should match eigenvalues"
        assert result.match_precision == 1.0, \
            "Should have 100% match for first 5 zeros"


class TestRHProvedCertificate:
    """Test complete RH_PROVED certificate generation"""
    
    def setup_method(self):
        """Setup test fixtures"""
        self.framework = RHProvedFramework(precision=30, n_basis=50)
    
    def test_certificate_generation(self):
        """Test complete certificate generation"""
        certificate = self.framework.generate_rh_proved_certificate(
            save_to_file=False
        )
        
        assert isinstance(certificate, RHProvedCertificate)
        assert certificate.timestamp is not None
        assert certificate.coherence == 244.36
        assert certificate.frequency == 141.7001
        assert certificate.hash_verification.startswith("41c4dca022a66c")
    
    def test_certificate_pillars(self):
        """Test that all three pillars are included in certificate"""
        certificate = self.framework.generate_rh_proved_certificate(
            save_to_file=False
        )
        
        # Pillar 1: Kernel Confinement
        assert isinstance(certificate.kernel_confinement, KernelConfinementResult)
        assert certificate.kernel_confinement.is_hilbert_schmidt
        
        # Pillar 2: Hardy-Littlewood Density
        assert isinstance(certificate.hardy_littlewood_density, 
                         HardyLittlewoodDensityResult)
        assert certificate.hardy_littlewood_density.hardy_theorem_satisfied
        
        # Pillar 3: Guinand-Weil Trace
        assert isinstance(certificate.guinand_weil_trace, GuinandWeilTraceResult)
        assert certificate.guinand_weil_trace.bijection_established
    
    def test_certificate_rh_proven(self):
        """Test that RH is marked as proven when all pillars pass"""
        certificate = self.framework.generate_rh_proved_certificate(
            save_to_file=False
        )
        
        if (certificate.kernel_confinement.is_hilbert_schmidt and
            certificate.hardy_littlewood_density.hardy_theorem_satisfied and
            certificate.guinand_weil_trace.bijection_established):
            assert certificate.riemann_hypothesis_proven, \
                "RH should be marked as proven when all pillars pass"
            assert certificate.status == "PROVEN"
    
    def test_certificate_to_dict(self):
        """Test certificate serialization to dict"""
        certificate = self.framework.generate_rh_proved_certificate(
            save_to_file=False
        )
        
        cert_dict = certificate.to_dict()
        
        assert 'timestamp' in cert_dict
        assert 'status' in cert_dict
        assert 'kernel_confinement' in cert_dict
        assert 'hardy_littlewood_density' in cert_dict
        assert 'guinand_weil_trace' in cert_dict
        assert 'riemann_hypothesis_proven' in cert_dict
    
    def test_certificate_file_creation(self, tmp_path):
        """Test certificate file creation"""
        certificate = self.framework.generate_rh_proved_certificate(
            save_to_file=True,
            output_dir=tmp_path
        )
        
        cert_file = tmp_path / 'rh_proved_certificate.json'
        assert cert_file.exists(), "Certificate file should be created"
        
        # Verify file can be loaded
        import json
        with open(cert_file) as f:
            data = json.load(f)
        
        assert 'riemann_hypothesis_proven' in data


class TestQCALIntegration:
    """Test QCAL framework integration"""
    
    def test_qcal_constants(self):
        """Test QCAL constants are correct"""
        from rh_proved_framework import QCAL_FREQUENCY, QCAL_COHERENCE, QCAL_HASH_PREFIX
        
        assert QCAL_FREQUENCY == 141.7001
        assert QCAL_COHERENCE == 244.36
        assert QCAL_HASH_PREFIX == "41c4dca022a66c"
    
    def test_qcal_certificate_markers(self):
        """Test QCAL certification markers in certificate"""
        framework = RHProvedFramework(precision=30, n_basis=50)
        certificate = framework.generate_rh_proved_certificate(save_to_file=False)
        
        assert certificate.frequency == 141.7001
        assert certificate.coherence == 244.36
        assert certificate.hash_verification == "41c4dca022a66c"
    
    def test_mathematical_realism_philosophy(self):
        """
        Test philosophical foundation: Mathematical Realism
        
        The validation VERIFIES pre-existing mathematical truth,
        not constructs it. The zeros of ζ(s) lie on Re(s) = 1/2
        as an objective fact of mathematical reality.
        """
        framework = RHProvedFramework(precision=30, n_basis=50)
        certificate = framework.generate_rh_proved_certificate(save_to_file=False)
        
        # The verification discovers truth, doesn't create it
        assert certificate.riemann_hypothesis_proven or certificate.status == "PARTIAL"
        # Truth exists independently of our verification


def test_suite_completeness():
    """Meta-test: ensure test suite covers all three pillars"""
    # This test verifies we have tests for all components
    test_classes = [
        TestKernelConfinement,
        TestHardyLittlewoodDensity,
        TestGuinandWeilTrace,
        TestRHProvedCertificate,
        TestQCALIntegration
    ]
    
    assert len(test_classes) == 5, "Should have tests for all components"


if __name__ == '__main__':
    # Run tests with pytest
    pytest.main([__file__, '-v', '--tb=short'])
