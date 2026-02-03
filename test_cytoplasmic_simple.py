#!/usr/bin/env python3
"""
Simple test runner for Cytoplasmic Flow Model (without pytest dependency conflicts)
"""

import sys
from pathlib import Path
import numpy as np

# Add src to path
sys.path.insert(0, str(Path(__file__).parent / "src"))

from biological.cytoplasmic_flow_model import (
    FlowParameters,
    NavierStokesRegularized,
    RiemannResonanceOperator,
    demonstrate_navier_stokes_coherence,
    F0_HZ,
    RHO_CYTOPLASM,
    NU_CYTOPLASM,
    CELL_LENGTH_SCALE,
    FLOW_VELOCITY,
)


def test_flow_parameters():
    """Test FlowParameters."""
    print("Testing FlowParameters...")
    
    params = FlowParameters()
    assert params.density == RHO_CYTOPLASM
    assert params.kinematic_viscosity == NU_CYTOPLASM
    assert params.reynolds_number < 1e-6
    assert params.has_smooth_solution
    
    print("  ✓ Default parameters")
    print("  ✓ Reynolds number calculation")
    print("  ✓ Viscous regime check")
    print("  ✅ FlowParameters tests passed")


def test_navier_stokes():
    """Test NavierStokesRegularized."""
    print("\nTesting NavierStokesRegularized...")
    
    flow = NavierStokesRegularized()
    assert flow.params is not None
    
    # Test velocity field
    vx, vy, vz = flow.velocity_field(0, 0, 0, 1.0)
    assert np.isfinite(vx)
    assert np.isfinite(vy)
    assert np.isfinite(vz)
    
    print("  ✓ Initialization")
    print("  ✓ Velocity field")
    
    # Test vorticity
    wx, wy, wz = flow.vorticity(0, 0, 0, 1.0)
    assert np.isfinite(wx)
    assert np.isfinite(wy)
    assert np.isfinite(wz)
    
    print("  ✓ Vorticity field")
    
    # Test pressure
    p = flow.pressure_field(0, 0, 0, 1.0)
    assert np.isfinite(p)
    
    print("  ✓ Pressure field")
    
    # Test energy spectrum
    k = np.logspace(0, 6, 10)
    E_k = flow.energy_spectrum(k)
    assert np.all(E_k >= 0)
    
    print("  ✓ Energy spectrum")
    print("  ✅ NavierStokesRegularized tests passed")


def test_riemann_operator():
    """Test RiemannResonanceOperator."""
    print("\nTesting RiemannResonanceOperator...")
    
    flow = NavierStokesRegularized()
    riemann_op = RiemannResonanceOperator(flow)
    
    # Test eigenfrequencies
    freqs = riemann_op.eigenfrequencies(n_modes=5)
    assert len(freqs) == 5
    assert freqs[0] == F0_HZ
    
    print("  ✓ Eigenfrequencies")
    
    # Test Hermitian property
    assert riemann_op.is_hermitian()
    
    print("  ✓ Hermitian check")
    
    # Test status
    status = riemann_op.riemann_hypothesis_status()
    assert status["operator_hermitian"]
    assert status["smooth_solution_exists"]
    assert status["riemann_zeros_accessible"]
    
    print("  ✓ Riemann status")
    print("  ✅ RiemannResonanceOperator tests passed")


def test_demonstration():
    """Test demonstration function."""
    print("\nTesting demonstration...")
    
    results = demonstrate_navier_stokes_coherence()
    
    assert "parameters" in results
    assert "riemann_status" in results
    assert "eigenfrequencies_hz" in results
    
    print("  ✅ Demonstration runs successfully")


def test_physical_consistency():
    """Test physical consistency."""
    print("\nTesting physical consistency...")
    
    flow = NavierStokesRegularized()
    
    # Test causality
    vx, vy, vz = flow.velocity_field(0, 0, 0, 1.0)
    v_mag = np.sqrt(vx**2 + vy**2 + vz**2)
    c = 3e8  # speed of light
    assert v_mag < c
    
    print("  ✓ Causality (v < c)")
    
    # Test QCAL frequency alignment
    riemann_op = RiemannResonanceOperator(flow)
    freqs = riemann_op.eigenfrequencies(n_modes=3)
    for i, f in enumerate(freqs, 1):
        expected = i * F0_HZ
        assert abs(f - expected) < 1e-6
    
    print("  ✓ QCAL frequency alignment")
    print("  ✅ Physical consistency tests passed")


def main():
    """Run all tests."""
    print("=" * 70)
    print("CYTOPLASMIC FLOW MODEL - Test Suite")
    print("=" * 70)
    print()
    
    try:
        test_flow_parameters()
        test_navier_stokes()
        test_riemann_operator()
        test_demonstration()
        test_physical_consistency()
        
        print()
        print("=" * 70)
        print("✅ ALL TESTS PASSED")
        print("=" * 70)
        return 0
        
    except AssertionError as e:
        print()
        print("=" * 70)
        print(f"❌ TEST FAILED: {e}")
        print("=" * 70)
        return 1
    except Exception as e:
        print()
        print("=" * 70)
        print(f"❌ ERROR: {e}")
        print("=" * 70)
        import traceback
        traceback.print_exc()
        return 1


if __name__ == "__main__":
    sys.exit(main())
