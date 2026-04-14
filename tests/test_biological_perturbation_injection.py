"""
Tests for Biological Perturbation Injection
============================================

Unit tests for biological perturbation mechanism and GUE validation.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: 2026-02-14
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add paths
sys.path.insert(0, str(Path(__file__).parent.parent / 'operators'))
sys.path.insert(0, str(Path(__file__).parent.parent / 'utils'))
sys.path.insert(0, str(Path(__file__).parent.parent / 'src' / 'biological'))

from biological_perturbation import (
    BiologicalPerturbation,
    PerturbedXiOperator,
    create_hrv_perturbation,
    create_microtubule_perturbation
)
from gue_validator import GUEValidator, GUEStatistics
from hrv_data_generator import HRVGenerator, MicrotubuleOscillationGenerator


class TestBiologicalPerturbation:
    """Test BiologicalPerturbation class."""
    
    def test_initialization(self):
        """Test perturbation initialization."""
        t = np.linspace(0, 10, 100)
        signal = np.sin(2*np.pi*t)
        
        pert = BiologicalPerturbation(
            signal_time=t,
            signal_values=signal,
            perturbation_strength=0.01,
            signal_type="hrv"
        )
        
        assert pert.perturbation_strength == 0.01
        assert pert.signal_type == "hrv"
        assert len(pert.signal_normalized) == len(t)
    
    def test_signal_normalization(self):
        """Test signal normalization to [-1, 1]."""
        t = np.linspace(0, 10, 100)
        signal = 5.0 * np.sin(2*np.pi*t) + 3.0  # Non-normalized
        
        pert = BiologicalPerturbation(t, signal, perturbation_strength=0.01)
        
        # Should be normalized
        assert np.max(np.abs(pert.signal_normalized)) <= 1.0 + 1e-10
    
    def test_evaluate_at_points(self):
        """Test evaluation at arbitrary points."""
        t = np.linspace(0, 10, 100)
        signal = np.sin(2*np.pi*0.5*t)
        
        pert = BiologicalPerturbation(t, signal)
        
        # Evaluate at new points
        t_new = np.array([0.0, 2.5, 5.0, 7.5])
        values = pert.evaluate_at_points(t_new)
        
        assert len(values) == len(t_new)
    
    def test_diagonal_perturbation(self):
        """Test diagonal perturbation generation."""
        t = np.linspace(0, 10, 100)
        signal = np.sin(2*np.pi*t)
        
        pert = BiologicalPerturbation(t, signal, perturbation_strength=0.05)
        
        grid = np.linspace(0, 10, 50)
        diag_pert = pert.to_diagonal_perturbation(grid)
        
        assert len(diag_pert) == len(grid)
        assert np.max(np.abs(diag_pert)) <= 0.05  # Within strength
    
    def test_rank1_perturbation(self):
        """Test rank-1 perturbation generation."""
        t = np.linspace(0, 10, 100)
        signal = np.sin(2*np.pi*t)
        
        pert = BiologicalPerturbation(t, signal, perturbation_strength=0.01)
        
        grid = np.linspace(0, 10, 30)
        matrix_pert = pert.to_rank1_perturbation(grid)
        
        assert matrix_pert.shape == (30, 30)
        
        # Check rank is approximately 1
        singular_values = np.linalg.svd(matrix_pert, compute_uv=False)
        rank_estimate = np.sum(singular_values > 1e-10 * singular_values[0])
        assert rank_estimate <= 5  # Should be low rank
    
    def test_local_potential_perturbation(self):
        """Test local potential perturbation with smoothing."""
        t = np.linspace(0, 10, 100)
        signal = np.random.randn(100)  # Noisy signal
        
        pert = BiologicalPerturbation(t, signal, perturbation_strength=0.01)
        
        grid = np.linspace(0, 10, 50)
        local_pert = pert.to_local_potential_perturbation(grid, locality_scale=2.0)
        
        assert len(local_pert) == len(grid)
        
        # Smoothed version should be smoother than original
        # (smaller high-frequency content)


class TestPerturbedXiOperator:
    """Test PerturbedXiOperator class."""
    
    def test_initialization(self):
        """Test perturbed operator initialization."""
        # Create simple Hamiltonian
        n = 50
        H_base = np.random.randn(n, n)
        H_base = (H_base + H_base.T) / 2  # Hermitian
        
        # Create perturbation
        t = np.linspace(0, 10, 100)
        signal = np.sin(2*np.pi*t)
        pert = BiologicalPerturbation(t, signal, perturbation_strength=0.01)
        
        grid = np.linspace(0, 10, n)
        
        perturbed_op = PerturbedXiOperator(
            base_hamiltonian=H_base,
            operator_grid=grid,
            perturbation=pert,
            perturbation_type="diagonal"
        )
        
        assert perturbed_op.perturbed_hamiltonian.shape == (n, n)
    
    def test_hermiticity_preservation(self):
        """Test that perturbed operator is Hermitian."""
        n = 40
        H_base = np.random.randn(n, n)
        H_base = (H_base + H_base.T) / 2
        
        t = np.linspace(0, 10, 100)
        signal = np.sin(2*np.pi*t)
        pert = BiologicalPerturbation(t, signal, perturbation_strength=0.01)
        
        grid = np.linspace(0, 10, n)
        
        perturbed_op = PerturbedXiOperator(H_base, grid, pert, "diagonal")
        
        H_pert = perturbed_op.perturbed_hamiltonian
        
        # Check Hermiticity
        hermiticity_error = np.max(np.abs(H_pert - H_pert.T))
        assert hermiticity_error < 1e-12
    
    def test_spectrum_computation(self):
        """Test spectrum computation."""
        n = 30
        H_base = np.diag(np.arange(n, dtype=float))  # Simple diagonal
        
        t = np.linspace(0, 10, 100)
        signal = 0.1 * np.sin(2*np.pi*t)
        pert = BiologicalPerturbation(t, signal, perturbation_strength=0.01)
        
        grid = np.linspace(0, 10, n)
        
        perturbed_op = PerturbedXiOperator(H_base, grid, pert, "diagonal")
        spectrum = perturbed_op.compute_spectrum()
        
        assert 'eigenvalues' in spectrum
        assert 'eigenvectors' in spectrum
        assert len(spectrum['eigenvalues']) == n
    
    def test_perturbation_norm(self):
        """Test perturbation norm computation."""
        n = 50
        H_base = np.eye(n)
        
        t = np.linspace(0, 10, 100)
        signal = np.sin(2*np.pi*t)
        pert = BiologicalPerturbation(t, signal, perturbation_strength=0.05)
        
        grid = np.linspace(0, 10, n)
        
        perturbed_op = PerturbedXiOperator(H_base, grid, pert, "diagonal")
        norm = perturbed_op.compute_perturbation_norm()
        
        # Should be on order of perturbation strength
        assert norm < 0.1
        assert norm > 0.0
    
    def test_spectral_shift(self):
        """Test spectral shift computation."""
        n = 40
        base_eigenvalues = np.arange(n, dtype=float)
        H_base = np.diag(base_eigenvalues)
        
        t = np.linspace(0, 10, 100)
        signal = np.sin(2*np.pi*t)
        pert = BiologicalPerturbation(t, signal, perturbation_strength=0.02)
        
        grid = np.linspace(0, 10, n)
        
        perturbed_op = PerturbedXiOperator(H_base, grid, pert, "diagonal")
        mean_shift, max_shift = perturbed_op.compute_spectral_shift(base_eigenvalues)
        
        assert mean_shift >= 0
        assert max_shift >= mean_shift
        assert max_shift < 0.1  # Small perturbation


class TestGUEValidator:
    """Test GUE statistics validation."""
    
    def test_initialization(self):
        """Test validator initialization."""
        validator = GUEValidator(tolerance=0.15)
        assert validator.tolerance == 0.15
    
    def test_unfold_spectrum(self):
        """Test spectrum unfolding."""
        validator = GUEValidator()
        
        # Create test spectrum
        eigenvalues = np.random.rand(100)
        unfolded = validator.unfold_spectrum(eigenvalues)
        
        assert len(unfolded) == len(eigenvalues)
        
        # Mean spacing should be ~1
        spacings = np.diff(np.sort(unfolded))
        mean_spacing = np.mean(spacings)
        assert 0.8 < mean_spacing < 1.2
    
    def test_nearest_neighbor_spacings(self):
        """Test NN spacing computation."""
        validator = GUEValidator()
        
        eigenvalues = np.arange(100, dtype=float) + 0.1*np.random.randn(100)
        spacings = validator.compute_nearest_neighbor_spacings(eigenvalues)
        
        assert len(spacings) == len(eigenvalues) - 1
        assert np.all(spacings >= 0)
    
    def test_wigner_surmise_pdf(self):
        """Test Wigner surmise PDF."""
        validator = GUEValidator()
        
        s = np.linspace(0, 3, 100)
        pdf = validator.wigner_surmise_pdf(s)
        
        assert len(pdf) == len(s)
        assert np.all(pdf >= 0)
        
        # Should integrate to approximately 1
        ds = s[1] - s[0]
        integral = np.sum(pdf) * ds
        assert 0.9 < integral < 1.1
    
    def test_validate_gue_statistics(self):
        """Test complete GUE validation."""
        validator = GUEValidator()
        
        # Generate GUE-like spectrum
        n = 200
        H = np.random.randn(n, n) + 1j * np.random.randn(n, n)
        H = (H + H.conj().T) / (2 * np.sqrt(n))
        eigenvalues = np.linalg.eigvalsh(H)
        
        stats = validator.validate_gue_statistics(eigenvalues)
        
        assert isinstance(stats, GUEStatistics)
        assert stats.rigidity > 0
        assert 0 < stats.level_spacing_ratio < 1
        assert stats.nearest_neighbor_variance > 0
    
    def test_compare_gue_statistics(self):
        """Test GUE comparison before/after perturbation."""
        validator = GUEValidator(tolerance=0.25)
        
        # Generate two similar GUE spectra
        n = 150
        H1 = np.random.randn(n, n)
        H1 = (H1 + H1.T) / (2 * np.sqrt(n))
        eigs1 = np.linalg.eigvalsh(H1)
        
        # Small perturbation
        H2 = H1 + 0.01 * np.random.randn(n, n)
        H2 = (H2 + H2.T) / (2 * np.sqrt(n))
        eigs2 = np.linalg.eigvalsh(H2)
        
        comparison = validator.compare_gue_statistics(eigs1, eigs2)
        
        assert 'baseline' in comparison
        assert 'perturbed' in comparison
        assert 'gue_preserved' in comparison
        
        # With small perturbation, GUE should be preserved
        assert comparison['spacing_ratio_change_percent'] < 50


class TestFactoryFunctions:
    """Test factory functions for perturbation creation."""
    
    def test_create_hrv_perturbation(self):
        """Test HRV perturbation factory."""
        gen = HRVGenerator(duration=60.0)
        hrv_signal = gen.generate_hrv_signal()
        
        pert = create_hrv_perturbation(hrv_signal, perturbation_strength=0.02)
        
        assert isinstance(pert, BiologicalPerturbation)
        assert pert.perturbation_strength == 0.02
        assert pert.signal_type == "hrv"
    
    def test_create_microtubule_perturbation(self):
        """Test microtubule perturbation factory."""
        gen = MicrotubuleOscillationGenerator(duration=5.0)
        mt_signal = gen.generate_oscillation()
        
        pert = create_microtubule_perturbation(mt_signal, perturbation_strength=0.015)
        
        assert isinstance(pert, BiologicalPerturbation)
        assert pert.perturbation_strength == 0.015
        assert pert.signal_type == "microtubule"


class TestIntegration:
    """Integration tests for full workflow."""
    
    def test_hrv_injection_workflow(self):
        """Test complete HRV injection workflow."""
        # Generate HRV signal
        hrv_gen = HRVGenerator(duration=60.0)
        hrv_signal = hrv_gen.generate_hrv_signal()
        
        # Create perturbation
        pert = create_hrv_perturbation(hrv_signal, perturbation_strength=0.01)
        
        # Create base Hamiltonian
        n = 100
        H_base = np.random.randn(n, n)
        H_base = (H_base + H_base.T) / (2 * np.sqrt(n))
        base_eigs = np.linalg.eigvalsh(H_base)
        
        # Inject perturbation
        grid = np.linspace(0, 60, n)
        perturbed_op = PerturbedXiOperator(H_base, grid, pert, "diagonal")
        
        # Compute spectra
        spectrum = perturbed_op.compute_spectrum()
        perturbed_eigs = spectrum['eigenvalues'].real
        
        # Validate GUE
        validator = GUEValidator(tolerance=0.3)
        comparison = validator.compare_gue_statistics(base_eigs, perturbed_eigs)
        
        # Should complete without errors
        assert 'gue_preserved' in comparison


# Run tests if executed directly
if __name__ == "__main__":
    pytest.main([__file__, "-v"])
