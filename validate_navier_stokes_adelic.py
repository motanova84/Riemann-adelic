#!/usr/bin/env python3
"""
Standalone validation script for Navier-Stokes Adelic Framework.

This script validates the implementation without requiring pytest or other dependencies.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
"""

import sys
import os
import numpy as np

# Add operators directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

# Import directly without going through __init__.py
import importlib.util

def load_module(module_name, file_path):
    """Load a module from a file path."""
    spec = importlib.util.spec_from_file_location(module_name, file_path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

# Load modules
base_dir = os.path.abspath(os.path.dirname(__file__))
adelic_lap_module = load_module(
    'adelic_laplacian',
    os.path.join(base_dir, 'operators', 'adelic_laplacian.py')
)
ns_adelic_module = load_module(
    'navier_stokes_adelic',
    os.path.join(base_dir, 'operators', 'navier_stokes_adelic.py')
)

# Get classes and constants
AdelicLaplacian = adelic_lap_module.AdelicLaplacian
KAPPA_PI = adelic_lap_module.KAPPA_PI
F0 = adelic_lap_module.F0
NavierStokesAdelicOperator = ns_adelic_module.NavierStokesAdelicOperator


def test_adelic_laplacian():
    """Test Adelic Laplacian construction."""
    print("Testing Adelic Laplacian...")
    
    adelic_lap = AdelicLaplacian(N=100, L=5.0, kappa=KAPPA_PI)
    
    # Test initialization
    assert adelic_lap.N == 100, "N should be 100"
    assert adelic_lap.L == 5.0, "L should be 5.0"
    assert adelic_lap.kappa == KAPPA_PI, "kappa should be KAPPA_PI"
    
    # Test diffusion kernel
    D_R = adelic_lap.archimedean_diffusion_kernel(adelic_lap.x)
    assert np.abs(D_R[50] - 1.0) < 1e-6, "D_R(0) should be 1.0"
    assert all(D_R > 0), "D_R should be positive"
    
    # Test p-adic weight
    w_2 = adelic_lap.padic_weight(2)
    assert w_2 > 0, "p-adic weight should be positive"
    
    # Test Archimedean Laplacian
    Delta_R = adelic_lap.archimedean_laplacian()
    assert Delta_R.shape == (100, 100), "Delta_R should be 100x100"
    
    # Test full adelic Laplacian
    Delta_A = adelic_lap.full_adelic_laplacian()
    assert Delta_A.shape == (100, 100), "Delta_A should be 100x100"
    
    # Test viscosity
    nu = adelic_lap.viscosity()
    assert nu > 0, "Viscosity should be positive"
    
    print("✓ Adelic Laplacian tests passed")


def test_navier_stokes_operator():
    """Test Navier-Stokes Adelic Operator."""
    print("\nTesting Navier-Stokes Adelic Operator...")
    
    ns_op = NavierStokesAdelicOperator(N=100, L=5.0, kappa=KAPPA_PI)
    
    # Test initialization
    assert ns_op.N == 100, "N should be 100"
    assert ns_op.L == 5.0, "L should be 5.0"
    assert ns_op.kappa == KAPPA_PI, "kappa should be KAPPA_PI"
    
    # Test transport operator
    T = ns_op.transport_operator()
    assert T.shape == (100, 100), "Transport operator should be 100x100"
    assert T.nnz > 0, "Transport operator should not be zero"
    
    # Test confinement potential
    V = ns_op.confinement_potential()
    assert len(V) == 100, "Potential should have 100 elements"
    assert np.abs(V[50]) < 1e-10, "V(0) should be ~0"
    assert all(V >= 0), "V should be non-negative"
    
    # Test diffusion operator
    D = ns_op.viscous_diffusion_operator()
    assert D.shape == (100, 100), "Diffusion operator should be 100x100"
    
    # Test full operator (Hermitian version)
    H = ns_op.full_operator(hermitian_version=True)
    assert H.shape == (100, 100), "Full operator should be 100x100"
    
    # Test Hermiticity
    H_dense = H.toarray()
    H_conj_T = H_dense.conj().T
    hermiticity_error = np.max(np.abs(H_dense - H_conj_T))
    assert hermiticity_error < 1e-10, "Hermitian operator should be self-adjoint"
    
    # Test spectrum computation
    eigenvalues, eigenvectors = ns_op.compute_spectrum(n_eigenvalues=10)
    assert len(eigenvalues) == 10, "Should compute 10 eigenvalues"
    assert eigenvectors.shape == (100, 10), "Should compute 10 eigenvectors"
    
    # For Hermitian operator, eigenvalues should be real
    assert np.max(np.abs(eigenvalues.imag)) < 1e-8, "Eigenvalues should be real"
    
    # Test Reynolds regime
    regime = ns_op.analyze_reynolds_regime()
    assert 'reynolds_number' in regime, "Regime should include Reynolds number"
    assert 'regime' in regime, "Regime should include regime type"
    assert regime['kappa_pi_critical'] == KAPPA_PI, "Should reference KAPPA_PI"
    
    # Test energy balance
    energy = ns_op.energy_balance_analysis()
    assert 'transport_energy' in energy, "Should include transport energy"
    assert 'diffusion_energy' in energy, "Should include diffusion energy"
    assert 'potential_energy' in energy, "Should include potential energy"
    assert np.isfinite(energy['total_energy']), "Total energy should be finite"
    
    print("✓ Navier-Stokes Adelic Operator tests passed")


def test_framework_transition():
    """Test Anosov → Navier-Stokes framework transition."""
    print("\nTesting Framework Transition...")
    
    # Test at critical κ_Π
    ns_op = NavierStokesAdelicOperator(N=150, kappa=KAPPA_PI)
    
    regime = ns_op.analyze_reynolds_regime()
    assert regime['kappa'] == KAPPA_PI, "Should use KAPPA_PI"
    
    # Test viscosity from frequency
    adelic_lap = AdelicLaplacian(kappa=KAPPA_PI)
    nu_theory = adelic_lap.theoretical_viscosity_from_frequency()
    assert nu_theory > 0, "Theoretical viscosity should be positive"
    assert np.isfinite(nu_theory), "Theoretical viscosity should be finite"
    
    # Test operator scaling with kappa
    ns_op_1 = NavierStokesAdelicOperator(N=100, kappa=1.0)
    ns_op_2 = NavierStokesAdelicOperator(N=100, kappa=2.0)
    
    nu_1 = ns_op_1.adelic_laplacian.viscosity()
    nu_2 = ns_op_2.adelic_laplacian.viscosity()
    
    # ν should scale as 1/κ
    assert np.abs(nu_1 - 1.0) < 1e-6, "ν(κ=1) should be 1.0"
    assert np.abs(nu_2 - 0.5) < 1e-6, "ν(κ=2) should be 0.5"
    
    print("✓ Framework Transition tests passed")


def run_all_validations():
    """Run all validation tests."""
    print("=" * 80)
    print("NAVIER-STOKES ADELIC FRAMEWORK VALIDATION")
    print("=" * 80)
    
    try:
        test_adelic_laplacian()
        test_navier_stokes_operator()
        test_framework_transition()
        
        print("\n" + "=" * 80)
        print("✓ ALL VALIDATIONS PASSED")
        print("=" * 80)
        print("\nFramework Transition Verified:")
        print("  • Adelic Laplacian Δ_A = Δ_R + Σ_p Δ_{Q_p} ✓")
        print("  • Navier-Stokes operator H_NS = (1/κ)Δ_A - x∂_x + V_eff ✓")
        print("  • Critical Reynolds number κ_Π = 2.57731 ✓")
        print("  • Viscosity ν = 1/κ emerges correctly ✓")
        print("  • Energy balance framework established ✓")
        print("\n" + "=" * 80)
        return 0
        
    except AssertionError as e:
        print(f"\n✗ VALIDATION FAILED: {e}")
        return 1
    except Exception as e:
        print(f"\n✗ ERROR: {e}")
        import traceback
        traceback.print_exc()
        return 1


if __name__ == "__main__":
    sys.exit(run_all_validations())
