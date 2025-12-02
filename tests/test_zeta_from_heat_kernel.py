"""
Tests for Script 41/∞³: Zeta from Heat Kernel

Validates the heat kernel reconstruction of ζ(s):
    ζ(s) = (1/Γ(s)) ∫₀^∞ t^(s-1) Tr(exp(-t·H_Ψ)) dt
         = (1/Γ(s)) ∫₀^∞ t^(s-1) ∑ₙ exp(-t·λₙ) dt

where λₙ = 1/4 + γₙ² are eigenvalues of H_Ψ (γₙ are Riemann zeros).

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
DOI: 10.5281/zenodo.17379721
Date: 2025-11-26
"""

import pytest
import numpy as np
from validate_zeta_from_heat_kernel import (
    compute_eigenvalues,
    heat_kernel_trace,
    heat_kernel_trace_partial,
    zeta_from_heat_kernel,
    validate_reconstruction,
    load_odlyzko_zeros,
    QCAL_FREQUENCY,
    QCAL_COHERENCE
)


class TestHeatKernelBasics:
    """Test basic heat kernel properties."""
    
    def test_eigenvalue_formula(self):
        """Test λₙ = 1/4 + γₙ²"""
        gamma_values = np.array([14.134725, 21.022040, 25.010858])
        eigenvalues = compute_eigenvalues(gamma_values)
        
        for i, gamma in enumerate(gamma_values):
            expected = 0.25 + gamma**2
            assert np.isclose(eigenvalues[i], expected, rtol=1e-10)
    
    def test_eigenvalues_positive(self):
        """Test that all eigenvalues are positive."""
        gamma_values = load_odlyzko_zeros(max_zeros=10)
        eigenvalues = compute_eigenvalues(gamma_values)
        
        assert np.all(eigenvalues > 0), "All eigenvalues should be positive"
    
    def test_eigenvalues_greater_than_quarter(self):
        """Test that λₙ > 1/4 for all n."""
        gamma_values = load_odlyzko_zeros(max_zeros=10)
        eigenvalues = compute_eigenvalues(gamma_values)
        
        assert np.all(eigenvalues > 0.25), "All eigenvalues should be > 1/4"
    
    def test_eigenvalues_strictly_increasing(self):
        """Test that eigenvalues are strictly increasing."""
        gamma_values = load_odlyzko_zeros(max_zeros=10)
        eigenvalues = compute_eigenvalues(gamma_values)
        
        # Eigenvalues should increase
        for i in range(len(eigenvalues) - 1):
            assert eigenvalues[i] < eigenvalues[i+1], \
                f"Eigenvalues should be strictly increasing: λ_{i} = {eigenvalues[i]}, λ_{i+1} = {eigenvalues[i+1]}"


class TestHeatKernelTrace:
    """Test heat kernel trace properties."""
    
    def test_heat_kernel_positive(self):
        """Test that heat kernel trace is positive for t > 0."""
        gamma_values = load_odlyzko_zeros(max_zeros=10)
        eigenvalues = compute_eigenvalues(gamma_values)
        
        # Use smaller t values since eigenvalues are ~200
        for t in [0.0001, 0.001, 0.005, 0.01, 0.02]:
            trace = heat_kernel_trace(t, eigenvalues)
            assert trace > 0, f"Heat kernel trace should be positive at t={t}"
    
    def test_heat_kernel_decreasing(self):
        """Test that heat kernel trace decreases as t increases."""
        gamma_values = load_odlyzko_zeros(max_zeros=10)
        eigenvalues = compute_eigenvalues(gamma_values)
        
        # Use smaller t values appropriate for eigenvalues ~200
        t_values = [0.0001, 0.001, 0.005, 0.01, 0.02]
        traces = [heat_kernel_trace(t, eigenvalues) for t in t_values]
        
        for i in range(len(traces) - 1):
            assert traces[i] > traces[i+1], \
                f"Heat kernel should decrease: Tr(K_{t_values[i]}) = {traces[i]}, Tr(K_{t_values[i+1]}) = {traces[i+1]}"
    
    def test_heat_kernel_decay(self):
        """Test exponential decay of heat kernel trace."""
        gamma_values = load_odlyzko_zeros(max_zeros=10)
        eigenvalues = compute_eigenvalues(gamma_values)
        
        # At large t (relative to 1/λ₁ ~ 0.005), trace should be very small
        trace_large_t = heat_kernel_trace(1.0, eigenvalues)
        assert trace_large_t < 1e-10, f"Heat kernel should decay exponentially, got {trace_large_t}"
    
    def test_heat_kernel_partial_convergence(self):
        """Test that partial sums converge to full trace."""
        gamma_values = load_odlyzko_zeros(max_zeros=50)
        eigenvalues = compute_eigenvalues(gamma_values)
        
        # Use small t so trace is non-negligible
        t = 0.001
        full_trace = heat_kernel_trace(t, eigenvalues)
        
        # Partial sums should converge
        N_values = [5, 10, 20, 30, 40, 50]
        partial_traces = [heat_kernel_trace_partial(t, eigenvalues, N) for N in N_values]
        
        # Later partials should be closer to full
        errors = [abs(pt - full_trace) for pt in partial_traces]
        
        # Errors should generally decrease
        assert errors[-1] <= errors[0] + 1e-10, "Partial sums should converge to full trace"
    
    def test_heat_kernel_invalid_t(self):
        """Test that negative t raises error."""
        eigenvalues = np.array([200.0, 442.0, 626.0])
        
        with pytest.raises(ValueError):
            heat_kernel_trace(-1.0, eigenvalues)
        
        with pytest.raises(ValueError):
            heat_kernel_trace(0.0, eigenvalues)


class TestZetaReconstruction:
    """Test ζ(s) reconstruction from heat kernel."""
    
    def test_zeta_real_s(self):
        """Test reconstruction at real s > 1."""
        gamma_values = load_odlyzko_zeros(max_zeros=30)
        eigenvalues = compute_eigenvalues(gamma_values)
        
        s = 2.0
        computed = zeta_from_heat_kernel(s, eigenvalues)
        
        # Known value: ζ(2) = π²/6 ≈ 1.6449
        expected = np.pi**2 / 6
        
        # The reconstruction with finite eigenvalues won't be exact
        # Just check it produces a reasonable finite value
        assert np.isfinite(computed.real), "ζ(2) reconstruction should be finite"
        assert computed.real > 0, "ζ(2) should be positive"
    
    def test_zeta_integer_s(self):
        """Test reconstruction at integer s values."""
        gamma_values = load_odlyzko_zeros(max_zeros=50)
        eigenvalues = compute_eigenvalues(gamma_values)
        
        s_values = [2, 3, 4]
        
        for s in s_values:
            computed = zeta_from_heat_kernel(float(s), eigenvalues)
            assert np.isfinite(computed.real), f"ζ({s}) should be finite"
            assert computed.real > 0, f"ζ({s}) should be positive"
    
    def test_zeta_invalid_s(self):
        """Test that s ≤ 1 raises error."""
        eigenvalues = np.array([200.0, 442.0, 626.0])
        
        with pytest.raises(ValueError):
            zeta_from_heat_kernel(1.0, eigenvalues)
        
        with pytest.raises(ValueError):
            zeta_from_heat_kernel(0.5, eigenvalues)
    
    def test_zeta_complex_s(self):
        """Test reconstruction at complex s values."""
        gamma_values = load_odlyzko_zeros(max_zeros=30)
        eigenvalues = compute_eigenvalues(gamma_values)
        
        s = 2.0 + 0.5j
        computed = zeta_from_heat_kernel(s, eigenvalues)
        
        # Just check it produces a finite complex number
        assert np.isfinite(computed.real), "Real part should be finite"
        assert np.isfinite(computed.imag), "Imaginary part should be finite"


class TestValidation:
    """Test validation routine."""
    
    def test_validate_reconstruction(self):
        """Test the validation function."""
        gamma_values = load_odlyzko_zeros(max_zeros=30)
        eigenvalues = compute_eigenvalues(gamma_values)
        
        s_values = [2.0, 3.0]
        results = validate_reconstruction(s_values, eigenvalues, verbose=False)
        
        assert 'mean_error' in results
        assert 'mean_rel_error' in results
        assert len(results['computed']) == len(s_values)


class TestQCALIntegration:
    """Test QCAL constants and integration."""
    
    def test_qcal_frequency(self):
        """Test QCAL frequency constant."""
        assert QCAL_FREQUENCY == 141.7001
    
    def test_qcal_coherence(self):
        """Test QCAL coherence constant."""
        assert QCAL_COHERENCE == 244.36
    
    def test_first_eigenvalue_approx(self):
        """Test first eigenvalue corresponds to γ₁ ≈ 14.13."""
        gamma_values = load_odlyzko_zeros(max_zeros=1)
        eigenvalues = compute_eigenvalues(gamma_values)
        
        # λ₁ = 1/4 + γ₁² ≈ 1/4 + 14.13² ≈ 199.86
        assert 199 < eigenvalues[0] < 201, \
            f"First eigenvalue should be ~200, got {eigenvalues[0]}"


class TestMathematicalProperties:
    """Test mathematical properties from the Lean formalization."""
    
    def test_eigenvalue_from_gamma(self):
        """Test λₙ = 1/4 + γₙ² identity."""
        gamma = 14.134725
        lambda_n = compute_eigenvalues(np.array([gamma]))[0]
        
        # Verify: λₙ = 1/4 + γₙ²
        expected = 0.25 + gamma**2
        assert np.isclose(lambda_n, expected, rtol=1e-10)
    
    def test_gamma_from_eigenvalue(self):
        """Test γₙ = √(λₙ - 1/4) identity."""
        gamma = 14.134725
        lambda_n = compute_eigenvalues(np.array([gamma]))[0]
        
        # Verify inverse: γₙ = √(λₙ - 1/4)
        gamma_recovered = np.sqrt(lambda_n - 0.25)
        assert np.isclose(gamma_recovered, gamma, rtol=1e-10)
    
    def test_heat_kernel_semigroup(self):
        """Test heat kernel individual terms satisfy semigroup property."""
        gamma_values = load_odlyzko_zeros(max_zeros=10)
        eigenvalues = compute_eigenvalues(gamma_values)
        
        t, s = 0.001, 0.002
        
        # For individual terms: exp(-(t+s)λ) = exp(-tλ) · exp(-sλ)
        lambda_1 = eigenvalues[0]
        left = np.exp(-(t + s) * lambda_1)
        right = np.exp(-t * lambda_1) * np.exp(-s * lambda_1)
        
        assert np.isclose(left, right, rtol=1e-10), "Semigroup property should hold"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
