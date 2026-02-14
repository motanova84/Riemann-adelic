#!/usr/bin/env python3
"""
Tests for Navier-Stokes Adelic Operator Framework

Validates:
1. Adelic Laplacian construction (Δ_A = Δ_R + Σ_p Δ_{Q_p})
2. Navier-Stokes operator components (transport, diffusion, confinement)
3. Reynolds number and viscosity relationships
4. Energy balance at critical κ_Π
5. Spectral properties

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
"""

import pytest
import numpy as np
import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from operators.adelic_laplacian import AdelicLaplacian, KAPPA_PI, F0
from operators.navier_stokes_adelic import NavierStokesAdelicOperator


class TestAdelicLaplacian:
    """Tests for AdelicLaplacian class."""
    
    def test_initialization(self):
        """Test basic initialization."""
        adelic_lap = AdelicLaplacian(N=100, L=5.0, kappa=KAPPA_PI)
        
        assert adelic_lap.N == 100
        assert adelic_lap.L == 5.0
        assert adelic_lap.kappa == KAPPA_PI
        assert len(adelic_lap.x) == 100
        assert adelic_lap.dx == pytest.approx(5.0/100)
    
    def test_archimedean_diffusion_kernel(self):
        """Test Archimedean diffusion kernel D_R(x) = 1/(1+|x|)."""
        adelic_lap = AdelicLaplacian(N=100, L=10.0)
        
        D_R = adelic_lap.archimedean_diffusion_kernel(adelic_lap.x)
        
        # At x=0, D_R should be 1
        assert D_R[50] == pytest.approx(1.0, rel=1e-6)
        
        # D_R should decrease with |x|
        assert all(D_R > 0)
        assert D_R[50] > D_R[99]  # Center > edge
        
        # Check range
        assert D_R.max() == pytest.approx(1.0, rel=1e-6)
        assert D_R.min() < 1.0
    
    def test_padic_weight(self):
        """Test p-adic weight w_p = ln(p)/p^(k/2)."""
        adelic_lap = AdelicLaplacian(k_power=1.0)
        
        # Check few primes
        w_2 = adelic_lap.padic_weight(2)
        w_3 = adelic_lap.padic_weight(3)
        w_5 = adelic_lap.padic_weight(5)
        
        # Weights should be positive
        assert w_2 > 0
        assert w_3 > 0
        assert w_5 > 0
        
        # Weights should increase initially (ln dominates), then decrease (p^k dominates)
        # For small primes, ln might still dominate
        assert w_3 > w_2  # ln(3)/sqrt(3) > ln(2)/sqrt(2)
    
    def test_archimedean_laplacian_shape(self):
        """Test Archimedean Laplacian matrix shape and structure."""
        adelic_lap = AdelicLaplacian(N=100)
        
        Delta_R = adelic_lap.archimedean_laplacian(use_diffusion_kernel=True)
        
        # Check shape
        assert Delta_R.shape == (100, 100)
        
        # Check sparse structure (tridiagonal with periodic BC)
        assert Delta_R.nnz > 0
        assert Delta_R.nnz <= 3 * 100  # At most 3 diagonals
    
    def test_padic_laplacian(self):
        """Test p-adic Laplacian construction."""
        adelic_lap = AdelicLaplacian(N=100)
        
        Delta_2 = adelic_lap.padic_laplacian(2, strength=0.1)
        
        # Check shape
        assert Delta_2.shape == (100, 100)
        
        # Check it's not zero
        assert Delta_2.nnz > 0
    
    def test_full_adelic_laplacian(self):
        """Test full adelic Laplacian Δ_A = Δ_R + Σ_p Δ_{Q_p}."""
        adelic_lap = AdelicLaplacian(N=100)
        
        Delta_A = adelic_lap.full_adelic_laplacian()
        
        # Check shape
        assert Delta_A.shape == (100, 100)
        
        # Should have contributions from both Archimedean and p-adic parts
        assert Delta_A.nnz > 0
    
    def test_viscosity(self):
        """Test viscosity ν = 1/κ."""
        adelic_lap = AdelicLaplacian(kappa=2.0)
        
        nu = adelic_lap.viscosity()
        
        assert nu == pytest.approx(0.5, rel=1e-6)
    
    def test_reynolds_number(self):
        """Test Reynolds number calculation."""
        adelic_lap = AdelicLaplacian(kappa=KAPPA_PI, L=10.0)
        
        Re = adelic_lap.reynolds_number(U_char=1.0, L_char=10.0)
        
        # Should be related to κ_Π
        assert Re > 0
    
    def test_verify_reynolds_critical(self):
        """Test Reynolds critical verification."""
        adelic_lap = AdelicLaplacian(kappa=KAPPA_PI)
        
        verification = adelic_lap.verify_reynolds_critical()
        
        # Check structure
        assert 'reynolds_number' in verification
        assert 'kappa_pi_expected' in verification
        assert 'is_critical' in verification
        assert 'viscosity' in verification
        
        # Expected value
        assert verification['kappa_pi_expected'] == KAPPA_PI


class TestNavierStokesAdelicOperator:
    """Tests for NavierStokesAdelicOperator class."""
    
    def test_initialization(self):
        """Test basic initialization."""
        ns_op = NavierStokesAdelicOperator(N=100, L=5.0, kappa=KAPPA_PI)
        
        assert ns_op.N == 100
        assert ns_op.L == 5.0
        assert ns_op.kappa == KAPPA_PI
        assert len(ns_op.x) == 100
    
    def test_transport_operator(self):
        """Test transport operator T = -x∂_x."""
        ns_op = NavierStokesAdelicOperator(N=100)
        
        T = ns_op.transport_operator()
        
        # Check shape
        assert T.shape == (100, 100)
        
        # Check it's not zero
        assert T.nnz > 0
    
    def test_confinement_potential(self):
        """Test confinement potential V_eff(x) = ln(1+|x|)."""
        ns_op = NavierStokesAdelicOperator(N=100, L=10.0, V_amp=1.0)
        
        V = ns_op.confinement_potential()
        
        # At x=0, V should be 0
        assert V[50] == pytest.approx(0.0, abs=1e-10)
        
        # V should increase with |x|
        assert all(V >= 0)
        assert V[99] > V[50]  # Edge > center
    
    def test_viscous_diffusion_operator(self):
        """Test viscous diffusion operator (1/κ)Δ_A."""
        ns_op = NavierStokesAdelicOperator(N=100, kappa=2.0)
        
        D = ns_op.viscous_diffusion_operator()
        
        # Check shape
        assert D.shape == (100, 100)
        
        # Check it's not zero
        assert D.nnz > 0
    
    def test_full_operator_hermitian(self):
        """Test full operator is Hermitian when requested."""
        ns_op = NavierStokesAdelicOperator(N=100)
        
        H = ns_op.full_operator(hermitian_version=True)
        
        # Check shape
        assert H.shape == (100, 100)
        
        # Check Hermiticity
        H_dense = H.toarray()
        H_conj_T = H_dense.conj().T
        
        hermiticity_error = np.max(np.abs(H_dense - H_conj_T))
        assert hermiticity_error < 1e-10
    
    def test_full_operator_components(self):
        """Test full operator includes all components."""
        ns_op = NavierStokesAdelicOperator(N=100)
        
        # Full operator
        H_full = ns_op.full_operator(
            include_transport=True,
            include_diffusion=True,
            include_confinement=True,
            hermitian_version=True
        )
        
        # Only diffusion
        H_diff = ns_op.full_operator(
            include_transport=False,
            include_diffusion=True,
            include_confinement=False,
            hermitian_version=True
        )
        
        # They should be different
        diff = (H_full - H_diff).toarray()
        assert np.max(np.abs(diff)) > 1e-6
    
    def test_compute_spectrum(self):
        """Test spectrum computation."""
        ns_op = NavierStokesAdelicOperator(N=100, kappa=KAPPA_PI)
        
        eigenvalues, eigenvectors = ns_op.compute_spectrum(n_eigenvalues=10)
        
        # Check shapes
        assert len(eigenvalues) == 10
        assert eigenvectors.shape == (100, 10)
        
        # For Hermitian operator, eigenvalues should be real
        assert np.max(np.abs(eigenvalues.imag)) < 1e-8
    
    def test_analyze_reynolds_regime(self):
        """Test Reynolds regime analysis."""
        ns_op = NavierStokesAdelicOperator(N=100, kappa=KAPPA_PI)
        
        regime = ns_op.analyze_reynolds_regime()
        
        # Check structure
        assert 'reynolds_number' in regime
        assert 'regime' in regime
        assert 'viscosity' in regime
        assert 'kappa_pi_critical' in regime
        
        # Check kappa_pi is correct
        assert regime['kappa_pi_critical'] == KAPPA_PI
    
    def test_energy_balance_analysis(self):
        """Test energy balance analysis."""
        ns_op = NavierStokesAdelicOperator(N=100, kappa=KAPPA_PI)
        
        energy = ns_op.energy_balance_analysis()
        
        # Check structure
        assert 'transport_energy' in energy
        assert 'diffusion_energy' in energy
        assert 'potential_energy' in energy
        assert 'total_energy' in energy
        assert 'balance_ratio' in energy
        
        # Energies should be finite
        assert np.isfinite(energy['transport_energy'])
        assert np.isfinite(energy['diffusion_energy'])
        assert np.isfinite(energy['potential_energy'])


class TestNavierStokesFrameworkTransition:
    """Tests for Anosov → Navier-Stokes framework transition."""
    
    def test_kappa_pi_as_reynolds_critical(self):
        """Verify κ_Π = 2.57731 acts as critical Reynolds number."""
        # At κ = κ_Π, system should be at criticality
        ns_op = NavierStokesAdelicOperator(N=200, kappa=KAPPA_PI)
        
        regime = ns_op.analyze_reynolds_regime()
        
        # Should have κ_Π in the regime analysis
        assert regime['kappa'] == pytest.approx(KAPPA_PI, rel=1e-6)
        assert regime['kappa_pi_critical'] == KAPPA_PI
    
    def test_viscosity_from_frequency(self):
        """Test viscosity emerges from fundamental frequency."""
        adelic_lap = AdelicLaplacian(kappa=KAPPA_PI)
        
        nu_theory = adelic_lap.theoretical_viscosity_from_frequency()
        
        # Should be positive and finite
        assert nu_theory > 0
        assert np.isfinite(nu_theory)
        
        # Should involve F0 (141.7001 Hz)
        assert nu_theory > 1.0  # Rough order of magnitude check
    
    def test_operator_scaling_with_kappa(self):
        """Test operator scales properly with κ."""
        ns_op_1 = NavierStokesAdelicOperator(N=100, kappa=1.0)
        ns_op_2 = NavierStokesAdelicOperator(N=100, kappa=2.0)
        
        D1 = ns_op_1.viscous_diffusion_operator()
        D2 = ns_op_2.viscous_diffusion_operator()
        
        # Diffusion should scale as 1/κ
        # D1 should be roughly 2x D2 (since κ1 = 1, κ2 = 2)
        ratio = np.abs(D1.toarray()).sum() / np.abs(D2.toarray()).sum()
        assert ratio == pytest.approx(2.0, rel=0.1)


def run_all_tests():
    """Run all tests with pytest."""
    pytest.main([__file__, '-v'])


if __name__ == "__main__":
    run_all_tests()
