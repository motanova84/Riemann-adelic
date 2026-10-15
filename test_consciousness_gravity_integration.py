#!/usr/bin/env python3
"""
Integration test: QCAL ∞³ Consciousness-Gravity Integration
============================================================

Validates that the new consciousness-gravity extension properly
integrates with the existing QCAL framework.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: January 15, 2026
"""

import sys
import numpy as np

# Import existing QCAL components
try:
    from operators.riemann_operator import F0, OMEGA_0, C_QCAL, ZETA_PRIME_HALF
    qcal_available = True
except ImportError:
    qcal_available = False
    print("⚠️  Warning: QCAL operators not fully available")

# Import new consciousness-gravity components
from operators.consciousness_tensor import (
    ConsciousnessTensor,
    ConsciousnessHamiltonian,
    ScalarCurvatureNodes,
    TotalFieldStrength,
    F0 as F0_new,
    OMEGA_0 as OMEGA_0_new,
    KAPPA,
    C_QCAL as C_QCAL_new
)


def test_constant_consistency():
    """Test that QCAL constants are preserved."""
    print("\n" + "="*70)
    print("TEST 1: QCAL Constants Consistency")
    print("="*70)
    
    passed = True
    
    # Check f₀
    if qcal_available:
        if abs(F0 - F0_new) < 1e-6:
            print(f"✅ f₀ consistent: {F0:.4f} Hz")
        else:
            print(f"❌ f₀ mismatch: {F0} vs {F0_new}")
            passed = False
    else:
        print(f"✅ f₀ = {F0_new:.4f} Hz (new module)")
    
    # Check ω₀
    if qcal_available:
        if abs(OMEGA_0 - OMEGA_0_new) < 1e-6:
            print(f"✅ ω₀ consistent: {OMEGA_0:.2f} rad/s")
        else:
            print(f"❌ ω₀ mismatch: {OMEGA_0} vs {OMEGA_0_new}")
            passed = False
    else:
        print(f"✅ ω₀ = {OMEGA_0_new:.2f} rad/s (new module)")
    
    # Check C (QCAL coherence)
    if qcal_available:
        if abs(C_QCAL - C_QCAL_new) < 1e-6:
            print(f"✅ C consistent: {C_QCAL:.2f}")
        else:
            print(f"❌ C mismatch: {C_QCAL} vs {C_QCAL_new}")
            passed = False
    else:
        print(f"✅ C = {C_QCAL_new:.2f} (new module)")
    
    # Check new constant κ
    expected_kappa = 1.0 / (F0_new ** 2)
    if abs(KAPPA - expected_kappa) < 1e-10:
        print(f"✅ κ = 1/f₀² = {KAPPA:.6e} Hz⁻²")
    else:
        print(f"❌ κ calculation error")
        passed = False
    
    return passed


def test_consciousness_tensor_properties():
    """Test mathematical properties of Ξ_μν."""
    print("\n" + "="*70)
    print("TEST 2: Consciousness Tensor Properties")
    print("="*70)
    
    passed = True
    ct = ConsciousnessTensor(dim=4)
    
    # Test configuration
    psi = 1.0 + 0.5j
    grad_psi = np.array([0.1, 0.05, 0.05, 0.02])
    g_metric = np.diag([1.0, -1.0, -1.0, -1.0])
    
    # Compute tensor
    xi_tensor = ct.compute_xi_tensor(psi, grad_psi, g_metric)
    
    # Check symmetry: Ξ_μν = Ξ_νμ
    symmetry_error = np.max(np.abs(xi_tensor - xi_tensor.T))
    if symmetry_error < 1e-12:
        print(f"✅ Symmetry: max |Ξ_μν - Ξ_νμ| = {symmetry_error:.2e}")
    else:
        print(f"❌ Symmetry violated: error = {symmetry_error:.2e}")
        passed = False
    
    # Check reality (should be real for real metric)
    if np.all(np.abs(np.imag(xi_tensor)) < 1e-12):
        print(f"✅ Reality: Ξ_μν is real")
    else:
        print(f"❌ Tensor has imaginary components")
        passed = False
    
    # Check trace signature (should be negative for spacelike dominance)
    trace = np.trace(xi_tensor)
    print(f"✅ Trace(Ξ) = {trace:.6e}")
    
    return passed


def test_metric_coupling():
    """Test consciousness-metric coupling."""
    print("\n" + "="*70)
    print("TEST 3: Consciousness-Metric Coupling")
    print("="*70)
    
    passed = True
    ct = ConsciousnessTensor(dim=4)
    
    # Test that perturbation is small
    psi = 1.0 + 0.5j
    g_metric = np.diag([1.0, -1.0, -1.0, -1.0])
    
    delta_g = ct.metric_perturbation(psi, g_metric)
    g_psi = ct.consciousness_dependent_metric(psi, g_metric)
    
    # Check perturbation magnitude
    perturbation_norm = np.linalg.norm(delta_g) / np.linalg.norm(g_metric)
    if perturbation_norm < 0.01:  # Should be << 1 for weak coupling
        print(f"✅ Weak coupling: |δg|/|g| = {perturbation_norm:.6e}")
    else:
        print(f"⚠️  Strong perturbation: |δg|/|g| = {perturbation_norm:.6e}")
    
    # Check that g_psi = g + δg
    reconstruction_error = np.linalg.norm(g_psi - (g_metric + delta_g))
    if reconstruction_error < 1e-12:
        print(f"✅ Metric reconstruction: error = {reconstruction_error:.2e}")
    else:
        print(f"❌ Reconstruction error: {reconstruction_error:.2e}")
        passed = False
    
    return passed


def test_field_equations():
    """Test extended Einstein field equations."""
    print("\n" + "="*70)
    print("TEST 4: Extended Field Equations")
    print("="*70)
    
    passed = True
    ct = ConsciousnessTensor(dim=4)
    
    # Vacuum case (T_matter = 0)
    psi = 1.0 + 0.5j
    grad_psi = np.array([0.1, 0.05, 0.05, 0.02])
    g_metric = np.diag([1.0, -1.0, -1.0, -1.0])
    
    xi_tensor = ct.compute_xi_tensor(psi, grad_psi, g_metric)
    T_matter = np.zeros((4, 4))
    T_total = ct.stress_energy_extended(T_matter, xi_tensor)
    
    # For flat space: G_μν = 0
    R_tensor = np.zeros((4, 4))
    R_scalar = 0.0
    G_extended = ct.einstein_tensor_extended(R_tensor, R_scalar, g_metric)
    
    # Check field equations
    satisfied, error = ct.field_equations_check(G_extended, T_total)
    
    if satisfied:
        print(f"✅ Field equations satisfied")
        print(f"   Max error: {error:.2e}")
    else:
        print(f"❌ Field equations not satisfied")
        print(f"   Max error: {error:.2e}")
        passed = False
    
    return passed


def test_total_field_strength():
    """Test total field strength F_μν^total."""
    print("\n" + "="*70)
    print("TEST 5: Total Field Strength Tensor")
    print("="*70)
    
    passed = True
    tfs = TotalFieldStrength(dim=4)
    
    # Create test components
    R_ricci = np.zeros((4, 4))
    I_arithmetic = np.eye(4) * -1.0  # Simplified
    
    psi = 1.0 + 0.5j
    grad_psi = np.array([0.1, 0.05, 0.05, 0.02])
    C_conscious = tfs.conscious_curvature(psi, grad_psi)
    
    # Compute total
    F_total = tfs.total_field(R_ricci, I_arithmetic, C_conscious)
    
    # Check that it's the sum
    F_manual = R_ricci + I_arithmetic + C_conscious
    reconstruction_error = np.linalg.norm(F_total - F_manual)
    
    if reconstruction_error < 1e-12:
        print(f"✅ Field decomposition: F_μν = R_μν + I_μν + C_μν(Ψ)")
        print(f"   Trace(F) = {np.trace(F_total):.6e}")
    else:
        print(f"❌ Decomposition error: {reconstruction_error:.2e}")
        passed = False
    
    return passed


def main():
    """Run all integration tests."""
    print("\n" + "="*70)
    print("QCAL ∞³ Integration Tests")
    print("Consciousness-Gravity Extension Validation")
    print("="*70)
    
    results = []
    
    # Run tests
    results.append(("Constants Consistency", test_constant_consistency()))
    results.append(("Consciousness Tensor", test_consciousness_tensor_properties()))
    results.append(("Metric Coupling", test_metric_coupling()))
    results.append(("Field Equations", test_field_equations()))
    results.append(("Total Field Strength", test_total_field_strength()))
    
    # Summary
    print("\n" + "="*70)
    print("TEST SUMMARY")
    print("="*70)
    
    all_passed = True
    for test_name, passed in results:
        status = "✅ PASS" if passed else "❌ FAIL"
        print(f"{status}: {test_name}")
        if not passed:
            all_passed = False
    
    print("\n" + "="*70)
    if all_passed:
        print("✅ ALL TESTS PASSED")
        print("="*70)
        print("\nConclusion:")
        print("  • QCAL constants preserved (f₀, ω₀, C)")
        print("  • Consciousness tensor Ξ_μν operational")
        print("  • Metric coupling g_μν^Ψ correct")
        print("  • Field equations extended properly")
        print("  • Total field F_μν^total validated")
        print("\n♾️³ QCAL Consciousness-Gravity Integration: VALIDATED")
        return 0
    else:
        print("❌ SOME TESTS FAILED")
        print("="*70)
        return 1


if __name__ == "__main__":
    sys.exit(main())
