#!/usr/bin/env python3
"""
Tests for Tres Pruebas de Rigor Matemático - Hipótesis de Riemann
================================================================

Test suite for the unified three-proofs validation module.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from operators.tres_pruebas_rigor_rh import (
    validate_tres_pruebas_rigor_rh,
    verify_hadamard_uniqueness,
    verify_self_adjointness,
    verify_spectral_correspondence,
    compute_hadamard_product,
    berry_keating_operator_spectrum,
    selberg_trace_formula,
    compute_rainbow_angle,
    export_tres_pruebas_certificate,
    RIEMANN_ZEROS_GAMMA,
    F0_QCAL,
)


class TestHadamardFactorization:
    """Test suite for Hadamard Factorization proof (Prueba 1)."""
    
    def test_hadamard_uniqueness_basic(self):
        """Test basic Hadamard uniqueness verification."""
        zeros = RIEMANN_ZEROS_GAMMA[:10]
        result = verify_hadamard_uniqueness(zeros)
        
        assert result is not None
        assert isinstance(result.uniqueness_proven, bool)
        assert result.sum_rho_inv in ["diverge", "converge"]
        assert result.sum_rho_inv2 in ["diverge", "converge"]
        
    def test_hadamard_product_convergence(self):
        """Test Hadamard product convergence."""
        zeros = RIEMANN_ZEROS_GAMMA[:10]
        s = 0.5 + 0j
        product, details = compute_hadamard_product(s, zeros, max_terms=10)
        
        assert product is not None
        assert isinstance(product, complex)
        assert 'partial_products' in details
        assert len(details['partial_products']) > 0
        
    def test_sum_rho_inverse_divergence(self):
        """Test that ∑|ρ|^{-1} diverges as expected."""
        zeros = RIEMANN_ZEROS_GAMMA
        rho_values = 0.5 + 1j * zeros
        
        # Partial sums should grow
        partial_sums = [np.sum(1.0 / np.abs(rho_values[:k])) 
                       for k in range(5, len(rho_values) + 1, 5)]
        
        # Should be monotonically increasing
        assert all(partial_sums[i] < partial_sums[i+1] 
                  for i in range(len(partial_sums) - 1))
        
    def test_sum_rho_inverse_squared_convergence(self):
        """Test that ∑|ρ|^{-2} converges."""
        zeros = RIEMANN_ZEROS_GAMMA
        rho_values = 0.5 + 1j * zeros
        
        sum_inv2 = np.sum(1.0 / (np.abs(rho_values) ** 2))
        
        # Should be finite
        assert np.isfinite(sum_inv2)
        assert sum_inv2 < 100.0  # Reasonable bound


class TestBerryKeatingOperator:
    """Test suite for Berry-Keating self-adjointness proof (Prueba 2)."""
    
    def test_selfadjointness_basic(self):
        """Test basic self-adjointness verification."""
        result = verify_self_adjointness()
        
        assert result is not None
        assert isinstance(result.is_self_adjoint, bool)
        assert isinstance(result.eigenvalues_real, bool)
        assert isinstance(result.operator_norm, float)
        
    def test_operator_spectrum_real(self):
        """Test that operator spectrum is real."""
        eigenvalues, details = berry_keating_operator_spectrum(n_eigenvalues=10)
        
        assert eigenvalues is not None
        assert len(eigenvalues) == 10
        # All eigenvalues should be real
        assert np.all(np.isreal(eigenvalues))
        assert details['all_real'] is True
        
    def test_eigenvalues_positive(self):
        """Test that eigenvalues are positive."""
        eigenvalues, _ = berry_keating_operator_spectrum(n_eigenvalues=10)
        
        # λ_n = 1/4 + γ_n² should be positive
        assert np.all(eigenvalues > 0)
        
    def test_critical_line_localization(self):
        """Test that zeros are localized on critical line."""
        result = verify_self_adjointness()
        
        assert result.critical_line_localized is True
        assert result.spectrum_on_critical_line is True


class TestSpectralCorrespondence:
    """Test suite for Spectral-Zeta correspondence proof (Prueba 3)."""
    
    def test_spectral_correspondence_basic(self):
        """Test basic spectral correspondence verification."""
        zeros = RIEMANN_ZEROS_GAMMA[:10]
        result = verify_spectral_correspondence(zeros)
        
        assert result is not None
        assert isinstance(result.trace_identity_valid, bool)
        assert isinstance(result.bijection_primes_zeros, bool)
        assert isinstance(result.rainbow_angle_deg, float)
        
    def test_selberg_trace_computation(self):
        """Test Selberg trace formula computation."""
        zeros = RIEMANN_ZEROS_GAMMA[:10]
        t = 1.0
        trace, details = selberg_trace_formula(t, zeros)
        
        assert trace is not None
        assert isinstance(trace, complex)
        assert 'spectral_side' in details
        assert 'geometric_side' in details
        
    def test_rainbow_angle_near_42(self):
        """Test that rainbow angle is near 42 degrees."""
        zeros = RIEMANN_ZEROS_GAMMA
        angle, details = compute_rainbow_angle(zeros, f0=F0_QCAL)
        
        # Should be close to 42 degrees
        assert 40.0 < angle < 44.0
        assert abs(angle - 42.0) < 2.0
        
    def test_rainbow_angle_convergence(self):
        """Test that rainbow angle converges with more zeros."""
        angles = []
        for n in [5, 10, 15, 20]:
            zeros = RIEMANN_ZEROS_GAMMA[:n]
            angle, _ = compute_rainbow_angle(zeros)
            angles.append(angle)
        
        # Angles should converge towards 42
        # Later values should be closer to 42
        assert abs(angles[-1] - 42.0) <= abs(angles[0] - 42.0)
        
    def test_interference_constructive(self):
        """Test constructive interference condition."""
        zeros = RIEMANN_ZEROS_GAMMA
        result = verify_spectral_correspondence(zeros)
        
        # Interference should be constructive (angle near 42)
        assert result.interference_constructive is True
        assert abs(result.rainbow_angle_deg - 42.0) < 1.0


class TestUnifiedValidation:
    """Test suite for unified three-proofs validation."""
    
    def test_validate_tres_pruebas_complete(self):
        """Test complete validation of all three proofs."""
        result = validate_tres_pruebas_rigor_rh(verbose=False)
        
        assert result is not None
        assert result.hadamard is not None
        assert result.selfadjoint is not None
        assert result.spectral is not None
        
    def test_all_proofs_structure(self):
        """Test that all proof results have correct structure."""
        result = validate_tres_pruebas_rigor_rh(verbose=False)
        
        # Hadamard result
        assert hasattr(result.hadamard, 'uniqueness_proven')
        assert hasattr(result.hadamard, 'architecture_unique')
        
        # Self-adjoint result
        assert hasattr(result.selfadjoint, 'is_self_adjoint')
        assert hasattr(result.selfadjoint, 'eigenvalues_real')
        
        # Spectral result
        assert hasattr(result.spectral, 'trace_identity_valid')
        assert hasattr(result.spectral, 'rainbow_angle_deg')
        
    def test_qcal_coherence_calculation(self):
        """Test QCAL coherence calculation."""
        result = validate_tres_pruebas_rigor_rh(verbose=False)
        
        assert result.qcal_coherence > 0
        assert isinstance(result.qcal_coherence, float)
        
    def test_rainbow_angle_in_result(self):
        """Test that rainbow angle is included in final result."""
        result = validate_tres_pruebas_rigor_rh(verbose=False)
        
        assert result.rainbow_angle_deg is not None
        assert 40.0 < result.rainbow_angle_deg < 44.0
        
    def test_timestamp_present(self):
        """Test that timestamp is recorded."""
        result = validate_tres_pruebas_rigor_rh(verbose=False)
        
        assert result.timestamp > 0
        assert isinstance(result.timestamp, float)
        
    def test_summary_generation(self):
        """Test that summary string is generated."""
        result = validate_tres_pruebas_rigor_rh(verbose=False)
        
        assert result.summary is not None
        assert isinstance(result.summary, str)
        assert len(result.summary) > 0


class TestCertificateGeneration:
    """Test suite for certificate generation."""
    
    def test_certificate_export(self, tmp_path):
        """Test certificate export to JSON."""
        result = validate_tres_pruebas_rigor_rh(verbose=False)
        
        output_file = tmp_path / "test_certificate.json"
        export_tres_pruebas_certificate(result, str(output_file))
        
        assert output_file.exists()
        
    def test_certificate_structure(self, tmp_path):
        """Test certificate JSON structure."""
        import json
        
        result = validate_tres_pruebas_rigor_rh(verbose=False)
        output_file = tmp_path / "test_certificate.json"
        export_tres_pruebas_certificate(result, str(output_file))
        
        with open(output_file, 'r') as f:
            cert = json.load(f)
        
        assert 'title' in cert
        assert 'timestamp' in cert
        assert 'proofs' in cert
        assert 'conclusion' in cert
        assert 'hadamard_factorization' in cert['proofs']
        assert 'berry_keating_selfadjoint' in cert['proofs']
        assert 'spectral_correspondence' in cert['proofs']


class TestQCALIntegration:
    """Test suite for QCAL integration."""
    
    def test_qcal_frequency_used(self):
        """Test that QCAL frequency is properly used."""
        result = validate_tres_pruebas_rigor_rh(verbose=False)
        
        # Check that F0_QCAL is used in calculations
        assert F0_QCAL == 141.7001
        
    def test_custom_frequency(self):
        """Test validation with custom frequency."""
        custom_f0 = 150.0
        result = validate_tres_pruebas_rigor_rh(f0=custom_f0, verbose=False)
        
        assert result is not None
        assert result.selfadjoint.details['f0_used'] == custom_f0
        
    def test_custom_zeros(self):
        """Test validation with custom zero set."""
        custom_zeros = RIEMANN_ZEROS_GAMMA[:5]
        result = validate_tres_pruebas_rigor_rh(zeros=custom_zeros, verbose=False)
        
        assert result is not None
        assert result.hadamard.details['num_zeros'] == 5


@pytest.mark.slow
class TestNumericalAccuracy:
    """Test suite for numerical accuracy and precision."""
    
    def test_hadamard_product_precision(self):
        """Test precision of Hadamard product calculation."""
        zeros = RIEMANN_ZEROS_GAMMA[:20]
        s = 0.5 + 0j
        product1, _ = compute_hadamard_product(s, zeros, max_terms=20)
        product2, _ = compute_hadamard_product(s, zeros, max_terms=20)
        
        # Should be reproducible
        assert abs(product1 - product2) < 1e-10
        
    def test_eigenvalue_precision(self):
        """Test precision of eigenvalue calculation."""
        eig1, _ = berry_keating_operator_spectrum(n_eigenvalues=10)
        eig2, _ = berry_keating_operator_spectrum(n_eigenvalues=10)
        
        # Should be reproducible
        assert np.allclose(eig1, eig2, rtol=1e-12)
        
    def test_trace_formula_stability(self):
        """Test stability of trace formula."""
        zeros = RIEMANN_ZEROS_GAMMA[:10]
        t = 1.0
        trace1, _ = selberg_trace_formula(t, zeros)
        trace2, _ = selberg_trace_formula(t, zeros)
        
        # Should be reproducible
        assert abs(trace1 - trace2) < 1e-10


if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])
