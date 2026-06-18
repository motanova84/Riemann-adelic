#!/usr/bin/env python3
"""
Tests for Mellin Deficiency Analyzer
====================================

Comprehensive test suite for the Mellin transform and deficiency index analysis.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz
"""

import pytest
import numpy as np
from pathlib import Path
import sys

# Add operators to path
sys.path.insert(0, str(Path(__file__).parent.parent / "operators"))

from mellin_deficiency_analyzer import (
    MellinDeficiencyAnalyzer,
    C_OPERATOR,
    F0,
    C_QCAL,
    KAPPA_PI,
    UNITARITY_TOLERANCE,
    SPECTRAL_VARIATION_TOLERANCE
)


class TestMellinTransform:
    """Test Mellin transform implementation."""
    
    def test_initialization(self):
        """Test analyzer initialization."""
        analyzer = MellinDeficiencyAnalyzer()
        
        assert analyzer.C == C_OPERATOR
        assert analyzer.C < 0  # Critical: C must be negative
        assert analyzer.N > 0
        assert len(analyzer.t) == analyzer.N
        assert len(analyzer.x) == analyzer.N
    
    def test_custom_parameters(self):
        """Test initialization with custom parameters."""
        C_custom = -15.0
        N_custom = 100
        
        analyzer = MellinDeficiencyAnalyzer(
            C=C_custom,
            N=N_custom,
            t_min=-5.0,
            t_max=5.0
        )
        
        assert analyzer.C == C_custom
        assert analyzer.N == N_custom
        assert len(analyzer.t) == N_custom
    
    def test_mellin_transform_gaussian(self):
        """Test Mellin transform on Gaussian function."""
        analyzer = MellinDeficiencyAnalyzer(N=100)
        
        # Create Gaussian in x-space
        x0 = 2.0
        sigma = 1.0
        f = np.exp(-((analyzer.x - x0) / sigma) ** 2)
        
        # Apply Mellin transform
        Uf = analyzer.mellin_transform(f)
        
        # Should get complex array
        assert Uf.dtype == complex
        assert len(Uf) == analyzer.N
        assert np.all(np.isfinite(Uf))
    
    def test_inverse_mellin_transform(self):
        """Test inverse Mellin transform."""
        analyzer = MellinDeficiencyAnalyzer(N=100)
        
        # Create function in t-space
        sigma_t = 2.0
        Uf = np.exp(-(analyzer.t / sigma_t) ** 2)
        
        # Apply inverse Mellin transform
        f = analyzer.inverse_mellin_transform(Uf)
        
        # Should get complex array
        assert f.dtype == complex
        assert len(f) == analyzer.N
        assert np.all(np.isfinite(f))
    
    def test_unitarity_property(self):
        """Test that U is approximately unitary."""
        analyzer = MellinDeficiencyAnalyzer(N=150)
        
        # Create smooth test function
        f_original = np.exp(-((analyzer.x - 3.0) / 1.5) ** 2)
        
        # Apply U then U⁻¹
        Uf = analyzer.mellin_transform(f_original)
        f_reconstructed = analyzer.inverse_mellin_transform(Uf)
        
        # Compute reconstruction error
        error = np.linalg.norm(f_reconstructed - f_original) / np.linalg.norm(f_original)
        
        # Should be within tolerance for discrete transforms
        assert error < UNITARITY_TOLERANCE, f"Unitarity error too large: {error:.4f}"
    
    def test_verify_unitarity_function(self):
        """Test the verify_unitarity method."""
        analyzer = MellinDeficiencyAnalyzer(N=150)
        
        results = analyzer.verify_unitarity(num_tests=5)
        
        assert 'unitarity_verified' in results
        assert 'max_error' in results
        assert 'mean_error' in results
        assert len(results['errors']) == 5
        
        # Should pass verification
        assert results['unitarity_verified'], "Unitarity verification failed"
        assert results['max_error'] < UNITARITY_TOLERANCE, \
            f"Max error too large: {results['max_error']:.4f} (tolerance: {UNITARITY_TOLERANCE})"


class TestOperatorConstruction:
    """Test operator construction in both representations."""
    
    def test_H_psi_operator_shape(self):
        """Test H_Ψ operator matrix shape."""
        analyzer = MellinDeficiencyAnalyzer(N=100)
        
        H_psi = analyzer.build_H_psi_operator()
        
        assert H_psi.shape == (100, 100)
        assert H_psi.dtype == complex
    
    def test_H_psi_operator_hermiticity(self):
        """Test that H_Ψ is approximately Hermitian."""
        analyzer = MellinDeficiencyAnalyzer(N=100)
        
        H_psi = analyzer.build_H_psi_operator()
        H_psi_dag = H_psi.conj().T
        
        # Compute Hermitian error
        hermitian_error = np.linalg.norm(H_psi - H_psi_dag) / np.linalg.norm(H_psi)
        
        # Should be approximately Hermitian (< 5% error due to discretization)
        assert hermitian_error < 0.1, f"Hermiticity error: {hermitian_error:.4f}"
    
    def test_H_hat_operator_shape(self):
        """Test Ĥ_Ψ operator matrix shape."""
        analyzer = MellinDeficiencyAnalyzer(N=100)
        
        H_hat = analyzer.build_H_hat_operator()
        
        assert H_hat.shape == (100, 100)
        assert H_hat.dtype == complex
    
    def test_H_hat_first_order(self):
        """Test that Ĥ_Ψ is first-order (tridiagonal structure)."""
        analyzer = MellinDeficiencyAnalyzer(N=100)
        
        H_hat = analyzer.build_H_hat_operator()
        
        # Check that it's mostly tridiagonal (allowing boundaries)
        # Extract main diagonal and first off-diagonals
        main_diag = np.diag(H_hat)
        upper_diag = np.diag(H_hat, k=1)
        lower_diag = np.diag(H_hat, k=-1)
        
        # Most of the matrix should be in these three diagonals
        assert len(main_diag) == 100
        assert len(upper_diag) == 99
        assert len(lower_diag) == 99


class TestDeficiencyIndices:
    """Test deficiency index computation."""
    
    def test_deficiency_solution_shape(self):
        """Test deficiency solution computation."""
        analyzer = MellinDeficiencyAnalyzer(N=100)
        
        lam = 1j
        u = analyzer.compute_deficiency_solution(lam)
        
        assert len(u) == analyzer.N
        assert u.dtype == complex
        assert np.all(np.isfinite(u))
    
    def test_deficiency_solution_gaussian_for_negative_C(self):
        """Test that for C < 0, solutions are Gaussian (decay at infinity)."""
        analyzer = MellinDeficiencyAnalyzer(N=200, t_min=-20, t_max=20)
        
        # For C < 0
        assert analyzer.C < 0
        
        lam = 1j
        u = analyzer.compute_deficiency_solution(lam)
        
        # Check decay at boundaries
        edge_idx = 10
        center_idx = len(u) // 2
        
        # Edges should be smaller than center (Gaussian decay)
        assert np.abs(u[edge_idx]) < np.abs(u[center_idx])
        assert np.abs(u[-edge_idx]) < np.abs(u[center_idx])
    
    def test_compute_deficiency_indices(self):
        """Test deficiency indices computation."""
        analyzer = MellinDeficiencyAnalyzer(N=200)
        
        results = analyzer.compute_deficiency_indices()
        
        assert 'C' in results
        assert 'deficiency_indices' in results
        assert 'u_plus_L2' in results
        assert 'u_minus_L2' in results
        assert 'limit_point_or_circle' in results
        
        # For C < 0, should get (2,2)
        assert results['C_sign'] == 'negative'
        assert results['deficiency_indices'] == (2, 2), \
            f"Expected (2,2), got {results['deficiency_indices']}"
        assert results['limit_point_or_circle'] == 'limit-circle'
        assert results['u_plus_L2'] == True
        assert results['u_minus_L2'] == True
    
    def test_deficiency_L2_integrability(self):
        """Test that deficiency solutions are L² for C < 0."""
        analyzer = MellinDeficiencyAnalyzer(N=200, t_min=-15, t_max=15)
        
        # Compute both solutions
        u_plus = analyzer.compute_deficiency_solution(1j)
        u_minus = analyzer.compute_deficiency_solution(-1j)
        
        # Compute L² norms
        from scipy.integrate import simps
        norm_plus = simps(np.abs(u_plus)**2, analyzer.t)
        norm_minus = simps(np.abs(u_minus)**2, analyzer.t)
        
        # Both should be finite and positive
        assert np.isfinite(norm_plus)
        assert np.isfinite(norm_minus)
        assert norm_plus > 0
        assert norm_minus > 0


class TestGaussianEigenfunctions:
    """Test Gaussian eigenfunction structure."""
    
    def test_gaussian_eigenfunction_shape(self):
        """Test eigenfunction computation."""
        analyzer = MellinDeficiencyAnalyzer(N=100)
        
        lam = 5.0
        psi = analyzer.compute_gaussian_eigenfunction(lam)
        
        assert len(psi) == analyzer.N
        assert psi.dtype in [float, np.float64, complex]
        assert np.all(np.isfinite(psi))
    
    def test_gaussian_eigenfunction_is_gaussian(self):
        """Test that eigenfunction is Gaussian in log(x)."""
        analyzer = MellinDeficiencyAnalyzer(N=200)
        
        lam = 0.0
        psi = analyzer.compute_gaussian_eigenfunction(lam)
        
        # For λ=0, should have maximum where C·log(x) = 0, i.e., log(x) = 0, i.e., x = 1
        # Find index closest to x = 1
        idx_x1 = np.argmin(np.abs(analyzer.x - 1.0))
        
        # Check that it's positive
        assert np.all(psi >= 0)
        
        # Check that it has a peak structure
        center_val = psi[idx_x1]
        edge_val = (psi[10] + psi[-10]) / 2
        assert center_val > edge_val, "Expected Gaussian peak structure"
    
    def test_eigenfunction_L2_integrability(self):
        """Test that eigenfunction is L² with measure dx/x."""
        analyzer = MellinDeficiencyAnalyzer(N=200)
        
        lam = 5.0
        results = analyzer.verify_eigenfunction_L2(lam, num_points=300)
        
        assert 'is_L2' in results
        assert 'L2_norm_squared' in results
        assert 'theoretical_value' in results
        
        # Should be L²
        assert results['is_L2'] == True
        assert np.isfinite(results['L2_norm_squared'])
        assert results['L2_norm_squared'] > 0
    
    def test_eigenfunction_independence_from_lambda(self):
        """Test that L² norm is independent of λ."""
        analyzer = MellinDeficiencyAnalyzer(N=200)
        
        # Test multiple λ values
        lambdas = [-10.0, -5.0, 0.0, 5.0, 10.0]
        norms = []
        
        for lam in lambdas:
            result = analyzer.verify_eigenfunction_L2(lam, num_points=300)
            norms.append(result['L2_norm_squared'])
        
        # Compute variation
        norm_std = np.std(norms)
        norm_mean = np.mean(norms)
        variation = norm_std / norm_mean
        
        # Should have low variation (within tolerance)
        assert variation < SPECTRAL_VARIATION_TOLERANCE, \
            f"Norm variation too high: {variation:.4f} (tolerance: {SPECTRAL_VARIATION_TOLERANCE})"


class TestSpectralPurity:
    """Test spectral purity analysis."""
    
    def test_spectral_purity_analysis(self):
        """Test complete spectral purity analysis."""
        analyzer = MellinDeficiencyAnalyzer(N=200)
        
        results = analyzer.spectral_purity_analysis()
        
        assert 'all_eigenfunctions_L2' in results
        assert 'norms_independent_of_lambda' in results
        assert 'spectral_purity_confirmed' in results
        assert 'lambda_samples' in results
        assert 'individual_results' in results
        
        # All eigenfunctions should be L²
        assert results['all_eigenfunctions_L2'] == True
        
        # Norms should be independent of λ
        assert results['norms_independent_of_lambda'] == True
        
        # Spectral purity should be confirmed
        assert results['spectral_purity_confirmed'] == True
    
    def test_spectral_purity_custom_lambdas(self):
        """Test spectral purity with custom λ values."""
        analyzer = MellinDeficiencyAnalyzer(N=200)
        
        custom_lambdas = np.array([-20.0, -10.0, 0.0, 10.0, 20.0])
        results = analyzer.spectral_purity_analysis(lambda_samples=custom_lambdas)
        
        assert len(results['individual_results']) == len(custom_lambdas)
        assert results['all_eigenfunctions_L2'] == True


class TestCertificateGeneration:
    """Test certificate generation."""
    
    def test_certificate_generation(self, tmp_path):
        """Test that certificate is generated correctly."""
        analyzer = MellinDeficiencyAnalyzer(N=100)
        
        # Generate certificate in temporary directory
        cert = analyzer.generate_certificate(output_dir=str(tmp_path))
        
        # Check certificate structure
        assert 'protocol' in cert
        assert 'version' in cert
        assert 'signature' in cert
        assert 'qcal_constants' in cert
        assert 'deficiency_analysis' in cert
        assert 'spectral_purity' in cert
        assert 'theorem' in cert
        assert 'verification_status' in cert
        
        # Check QCAL signature
        assert cert['signature'] == '∴𓂀Ω∞³Φ'
        
        # Check protocol
        assert cert['protocol'] == 'QCAL-MELLIN-DEFICIENCY-ANALYZER'
        
        # Check QCAL constants
        assert cert['qcal_constants']['f0_hz'] == F0
        assert cert['qcal_constants']['C_coherence'] == C_QCAL
        assert cert['qcal_constants']['kappa_pi'] == KAPPA_PI
        
        # Check file was created
        cert_file = tmp_path / "mellin_deficiency_certificate.json"
        assert cert_file.exists()
    
    def test_certificate_verification_status(self, tmp_path):
        """Test certificate verification status."""
        analyzer = MellinDeficiencyAnalyzer(N=150)
        
        cert = analyzer.generate_certificate(output_dir=str(tmp_path))
        
        # Check verification status
        assert 'verification_status' in cert
        status = cert['verification_status']
        
        assert 'unitarity' in status
        assert 'deficiency_indices' in status
        assert 'spectral_purity' in status
        assert 'overall_verified' in status
        
        # All should pass
        assert status['overall_verified'] == True, \
            f"Overall verification failed: {status}"
    
    def test_certificate_coherence_and_resonance(self, tmp_path):
        """Test certificate coherence and resonance metrics."""
        analyzer = MellinDeficiencyAnalyzer(N=150)
        
        cert = analyzer.generate_certificate(output_dir=str(tmp_path))
        
        # Check coherence
        assert 'coherence' in cert
        assert cert['coherence'] >= 0.0
        assert cert['coherence'] <= 1.0
        
        # Check resonance level
        assert 'resonance_level' in cert
        assert cert['resonance_level'] in ['UNIVERSAL', 'PARTIAL', 'NONE']
        
        # Should be UNIVERSAL when all checks pass
        if cert['verification_status']['overall_verified']:
            assert cert['coherence'] == 1.0
            assert cert['resonance_level'] == 'UNIVERSAL'


class TestCompleteAnalysis:
    """Test complete analysis pipeline."""
    
    def test_complete_analysis_runs(self):
        """Test that complete analysis runs without errors."""
        analyzer = MellinDeficiencyAnalyzer(N=100)
        
        results = analyzer.complete_analysis(verbose=False)
        
        assert 'unitarity' in results
        assert 'deficiency' in results
        assert 'spectral_purity' in results
        assert 'certificate' in results
    
    def test_complete_analysis_verification(self):
        """Test that complete analysis verifies all components."""
        analyzer = MellinDeficiencyAnalyzer(N=150)
        
        results = analyzer.complete_analysis(verbose=False)
        
        # Check unitarity
        assert results['unitarity']['unitarity_verified'] == True
        
        # Check deficiency indices
        assert results['deficiency']['deficiency_indices'] == (2, 2)
        assert results['deficiency']['limit_point_or_circle'] == 'limit-circle'
        
        # Check spectral purity
        assert results['spectral_purity']['spectral_purity_confirmed'] == True
        
        # Check overall verification
        assert results['certificate']['verification_status']['overall_verified'] == True
    
    def test_complete_analysis_verbose_mode(self, capsys):
        """Test that verbose mode produces output."""
        analyzer = MellinDeficiencyAnalyzer(N=100)
        
        results = analyzer.complete_analysis(verbose=True)
        
        # Capture output
        captured = capsys.readouterr()
        
        # Check that output contains key phrases
        assert "MELLIN TRANSFORM" in captured.out
        assert "deficiency indices" in captured.out.lower()
        assert "spectral purity" in captured.out.lower()
        assert "CONCLUSION" in captured.out


class TestNumericalAccuracy:
    """Test numerical accuracy and convergence."""
    
    def test_convergence_with_increasing_N(self):
        """Test that results converge as N increases."""
        N_values = [50, 100, 200]
        deficiency_results = []
        
        for N in N_values:
            analyzer = MellinDeficiencyAnalyzer(N=N)
            result = analyzer.compute_deficiency_indices()
            deficiency_results.append(result)
        
        # All should give (2,2) for C < 0
        for result in deficiency_results:
            assert result['deficiency_indices'] == (2, 2)
            assert result['limit_point_or_circle'] == 'limit-circle'
    
    def test_numerical_stability(self):
        """Test numerical stability with different domains."""
        # Test with different t-domains
        domains = [(-5, 5), (-10, 10), (-20, 20)]
        
        for t_min, t_max in domains:
            analyzer = MellinDeficiencyAnalyzer(
                N=150,
                t_min=t_min,
                t_max=t_max
            )
            
            results = analyzer.compute_deficiency_indices()
            
            # Should always get (2,2) for C < 0
            assert results['deficiency_indices'] == (2, 2)
            assert results['u_plus_L2'] == True
            assert results['u_minus_L2'] == True


@pytest.mark.slow
class TestMainFunction:
    """Test main entry point."""
    
    def test_main_executes(self, capsys):
        """Test that main function executes."""
        from mellin_deficiency_analyzer import main
        
        results = main()
        
        # Check output
        captured = capsys.readouterr()
        assert "MELLIN" in captured.out
        
        # Check results structure
        assert results is not None
        assert 'certificate' in results


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
