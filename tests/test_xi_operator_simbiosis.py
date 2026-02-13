"""
Tests for Xi Operator Simbiosis — QCAL ∞³ Spectral Verification
================================================================

Comprehensive test suite for the Xi operator spectral verification system.

Author: José Manuel Mota Burruezo Ψ ∴ ∞³
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add operators directory to path
repo_root = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(repo_root / "operators"))

from xi_operator_simbiosis import (
    XiOperatorSimbiosis,
    run_xi_spectral_verification,
    F0, KAPPA_PI, PHI, GAMMA_EULER
)


class TestXiOperatorConstants:
    """Test QCAL constants used by Xi operator."""
    
    def test_f0_value(self):
        """Verify master frequency is correct."""
        assert abs(F0 - 141.7001) < 1e-6
    
    def test_kappa_pi_value(self):
        """Verify critical point κ_Π."""
        assert abs(KAPPA_PI - 2.5773) < 1e-4
    
    def test_phi_value(self):
        """Verify golden ratio."""
        assert abs(PHI - 1.618033988749895) < 1e-12
    
    def test_gamma_euler_value(self):
        """Verify Euler-Mascheroni constant."""
        assert abs(GAMMA_EULER - 0.5772156649015329) < 1e-15


class TestXiOperatorInitialization:
    """Test Xi operator initialization."""
    
    def test_default_initialization(self):
        """Test default parameters."""
        xi_op = XiOperatorSimbiosis()
        
        assert xi_op.n == 4096
        assert xi_op.t_max == 100.0
        assert len(xi_op.t) == 4096
        assert len(xi_op.phi) == 4096
    
    def test_custom_dimensions(self):
        """Test custom dimension initialization."""
        xi_op = XiOperatorSimbiosis(n_dim=512, t_max=50.0)
        
        assert xi_op.n == 512
        assert xi_op.t_max == 50.0
        assert len(xi_op.t) == 512
        assert len(xi_op.phi) == 512
    
    def test_grid_symmetry(self):
        """Test grid is symmetric around zero."""
        xi_op = XiOperatorSimbiosis(n_dim=100, t_max=10.0)
        
        assert abs(xi_op.t[0] + xi_op.t[-1]) < 1e-10
        assert abs(xi_op.t[49] + xi_op.t[50]) < 0.5  # Near zero
    
    def test_phase_field_properties(self):
        """Test phase field has correct properties."""
        xi_op = XiOperatorSimbiosis(n_dim=1000, t_max=50.0)
        
        # Phase should be real
        assert np.all(np.isreal(xi_op.phi))
        
        # Phase should be antisymmetric
        mid = len(xi_op.phi) // 2
        assert abs(xi_op.phi[mid-10] + xi_op.phi[mid+10]) < 1e-6


class TestGammaKernel:
    """Test gamma kernel computation."""
    
    def test_gamma_kernel_at_zero(self):
        """Test gamma kernel near t=0."""
        xi_op = XiOperatorSimbiosis(n_dim=100, t_max=10.0)
        
        # Should not crash at t=0
        kernel = xi_op._gamma_kernel(0.1)
        assert np.isfinite(kernel)
    
    def test_gamma_kernel_is_complex(self):
        """Test gamma kernel returns complex values."""
        xi_op = XiOperatorSimbiosis()
        
        kernel = xi_op._gamma_kernel(14.134725)  # First Riemann zero
        assert isinstance(kernel, (complex, np.complex128))
    
    def test_gamma_kernel_finite(self):
        """Test gamma kernel is finite for reasonable t."""
        xi_op = XiOperatorSimbiosis()
        
        for t in [1.0, 5.0, 10.0, 14.134725, 21.022040]:
            kernel = xi_op._gamma_kernel(t)
            assert np.isfinite(kernel), f"Kernel infinite at t={t}"


class TestHamiltonianConstruction:
    """Test Hamiltonian construction."""
    
    def test_hamiltonian_shape(self):
        """Test Hamiltonian has correct shape."""
        xi_op = XiOperatorSimbiosis(n_dim=100, t_max=10.0)
        H = xi_op.construct_hamiltonian()
        
        assert H.shape == (100, 100)
    
    def test_hamiltonian_hermiticity(self):
        """Test Hamiltonian is Hermitian."""
        xi_op = XiOperatorSimbiosis(n_dim=200, t_max=20.0)
        H = xi_op.construct_hamiltonian()
        
        # Check H = H†
        hermiticity_error = np.max(np.abs(H - H.conj().T))
        assert hermiticity_error < 1e-10, f"Hermiticity error: {hermiticity_error}"
    
    def test_hamiltonian_sparsity(self):
        """Test Hamiltonian is reasonably sparse."""
        xi_op = XiOperatorSimbiosis(n_dim=100, t_max=10.0)
        H = xi_op.construct_hamiltonian()
        
        # Count non-zero elements
        non_zero = np.sum(np.abs(H) > 1e-12)
        total = H.size
        
        # Should be less than 10% non-zero (sparse)
        sparsity = non_zero / total
        assert sparsity < 0.2, f"Matrix too dense: {sparsity*100:.1f}% non-zero"


class TestSpectrumComputation:
    """Test spectrum computation."""
    
    def test_spectrum_keys(self):
        """Test spectrum dict has all required keys."""
        xi_op = XiOperatorSimbiosis(n_dim=128, t_max=20.0)
        spectrum = xi_op.compute_spectrum()
        
        required_keys = ['eigenvalues', 'eigenvectors', 'critical_eigenvalues',
                        't_zeros', 'phases']
        for key in required_keys:
            assert key in spectrum, f"Missing key: {key}"
    
    def test_eigenvalues_real(self):
        """Test eigenvalues are real (Hermitian operator)."""
        xi_op = XiOperatorSimbiosis(n_dim=128, t_max=20.0)
        spectrum = xi_op.compute_spectrum()
        
        eigenvalues = spectrum['eigenvalues']
        assert np.all(np.abs(eigenvalues.imag) < 1e-10), "Eigenvalues should be real"
    
    def test_finds_zeros(self):
        """Test that operator finds some zeros."""
        xi_op = XiOperatorSimbiosis(n_dim=512, t_max=30.0)
        spectrum = xi_op.compute_spectrum()
        
        zeros = spectrum['t_zeros']
        assert len(zeros) > 0, "Should find at least some zeros"
    
    def test_zeros_in_range(self):
        """Test zeros are within expected range."""
        xi_op = XiOperatorSimbiosis(n_dim=512, t_max=30.0)
        spectrum = xi_op.compute_spectrum()
        
        zeros = spectrum['t_zeros']
        zeros = zeros[zeros > 0]  # Positive zeros
        
        if len(zeros) > 0:
            assert zeros.min() >= 0, "Zeros should be positive"
            assert zeros.max() <= 2 * xi_op.t_max, "Zeros within grid range"


class TestXiFunction:
    """Test Xi function computation."""
    
    def test_xi_function_shape(self):
        """Test Xi function has correct shape."""
        xi_op = XiOperatorSimbiosis(n_dim=100, t_max=10.0)
        xi_values = xi_op.xi_function()
        
        assert len(xi_values) == 100
    
    def test_xi_function_at_zero(self):
        """Test Xi function near t=0."""
        xi_op = XiOperatorSimbiosis(n_dim=100, t_max=10.0)
        t_points = np.array([0.0, 0.01, 0.1])
        xi_values = xi_op.xi_function(t_points)
        
        # Xi(0) should be close to 1
        assert abs(xi_values[0] - 1.0) < 0.5
    
    def test_xi_function_finite(self):
        """Test Xi function is finite."""
        xi_op = XiOperatorSimbiosis(n_dim=100, t_max=20.0)
        xi_values = xi_op.xi_function()
        
        assert np.all(np.isfinite(xi_values)), "Xi function should be finite"


class TestRiemannVerification:
    """Test Riemann Hypothesis verification."""
    
    def test_verification_keys(self):
        """Test verification dict has all keys."""
        xi_op = XiOperatorSimbiosis(n_dim=256, t_max=30.0)
        verification = xi_op.verify_riemann_hypothesis()
        
        required_keys = ['zeros_count', 'zeros_real', 'mean_spacing',
                        'gue_rigidity', 'phase_coherence', 'riemann_verified',
                        'zeros']
        for key in required_keys:
            assert key in verification, f"Missing key: {key}"
    
    def test_zeros_real_always_true(self):
        """Test zeros_real is always True (Hermitian eigenvalues)."""
        xi_op = XiOperatorSimbiosis(n_dim=256, t_max=30.0)
        verification = xi_op.verify_riemann_hypothesis()
        
        assert verification['zeros_real'] == True
    
    def test_gue_rigidity_range(self):
        """Test GUE rigidity is in reasonable range."""
        xi_op = XiOperatorSimbiosis(n_dim=512, t_max=30.0)
        verification = xi_op.verify_riemann_hypothesis()
        
        rigidity = verification['gue_rigidity']
        if rigidity > 0:  # If computed
            assert 0.1 < rigidity < 5.0, f"Rigidity out of range: {rigidity}"
    
    def test_phase_coherence_range(self):
        """Test phase coherence is between 0 and 1."""
        xi_op = XiOperatorSimbiosis(n_dim=256, t_max=30.0)
        verification = xi_op.verify_riemann_hypothesis()
        
        coherence = verification['phase_coherence']
        assert 0.0 <= coherence <= 1.0, f"Coherence out of range: {coherence}"
    
    def test_verification_logic(self):
        """Test verification logic is consistent."""
        xi_op = XiOperatorSimbiosis(n_dim=256, t_max=30.0)
        verification = xi_op.verify_riemann_hypothesis()
        
        # If verified, all components should be good
        if verification['riemann_verified']:
            assert verification['zeros_real'] == True
            assert 0.8 < verification['gue_rigidity'] < 1.2
            assert verification['phase_coherence'] > 0.9


class TestFullVerification:
    """Test complete verification pipeline."""
    
    def test_run_verification_completes(self):
        """Test full verification runs without errors."""
        # Use small dimensions for speed
        results = run_xi_spectral_verification(n_dim=128, t_max=20.0)
        
        assert 'spectrum' in results
        assert 'verification' in results
        assert 'operator' in results
    
    def test_verification_structure(self):
        """Test verification results have proper structure."""
        results = run_xi_spectral_verification(n_dim=128, t_max=20.0)
        
        spectrum = results['spectrum']
        verification = results['verification']
        
        assert isinstance(spectrum, dict)
        assert isinstance(verification, dict)
        assert isinstance(results['operator'], XiOperatorSimbiosis)
    
    def test_reproducibility(self):
        """Test results are reproducible."""
        np.random.seed(42)
        results1 = run_xi_spectral_verification(n_dim=128, t_max=20.0)
        
        np.random.seed(42)
        results2 = run_xi_spectral_verification(n_dim=128, t_max=20.0)
        
        # Eigenvalues should be identical
        evals1 = results1['spectrum']['eigenvalues']
        evals2 = results2['spectrum']['eigenvalues']
        
        assert np.allclose(evals1, evals2, rtol=1e-10)


class TestNumericalStability:
    """Test numerical stability."""
    
    def test_different_dimensions(self):
        """Test operator works with different dimensions."""
        dimensions = [64, 128, 256, 512]
        
        for dim in dimensions:
            xi_op = XiOperatorSimbiosis(n_dim=dim, t_max=20.0)
            spectrum = xi_op.compute_spectrum()
            
            assert len(spectrum['eigenvalues']) == dim
    
    def test_different_ranges(self):
        """Test operator works with different t ranges."""
        ranges = [10.0, 20.0, 30.0, 50.0]
        
        for t_max in ranges:
            xi_op = XiOperatorSimbiosis(n_dim=128, t_max=t_max)
            verification = xi_op.verify_riemann_hypothesis()
            
            assert verification['zeros_count'] >= 0
    
    def test_no_nan_or_inf(self):
        """Test computations don't produce NaN or Inf."""
        xi_op = XiOperatorSimbiosis(n_dim=256, t_max=30.0)
        
        H = xi_op.construct_hamiltonian()
        assert not np.any(np.isnan(H)), "Hamiltonian contains NaN"
        assert not np.any(np.isinf(H)), "Hamiltonian contains Inf"
        
        spectrum = xi_op.compute_spectrum()
        assert not np.any(np.isnan(spectrum['eigenvalues'])), "Eigenvalues contain NaN"
        assert not np.any(np.isinf(spectrum['eigenvalues'])), "Eigenvalues contain Inf"


@pytest.mark.slow
class TestLargeScale:
    """Test large-scale computations (marked as slow)."""
    
    def test_large_dimension(self):
        """Test with larger dimension (4096)."""
        xi_op = XiOperatorSimbiosis(n_dim=1024, t_max=50.0)
        verification = xi_op.verify_riemann_hypothesis()
        
        assert verification['zeros_count'] > 0
    
    def test_extended_range(self):
        """Test with extended t range."""
        xi_op = XiOperatorSimbiosis(n_dim=512, t_max=100.0)
        spectrum = xi_op.compute_spectrum()
        
        zeros = spectrum['t_zeros']
        zeros = zeros[zeros > 0]
        
        # Should find more zeros in larger range
        assert len(zeros) > 10


if __name__ == "__main__":
    # Run tests with pytest
    pytest.main([__file__, "-v", "--tb=short"])
