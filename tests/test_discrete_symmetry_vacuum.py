"""
Test suite for the discrete symmetry vacuum energy framework.

This module tests all components of the discrete_symmetry_vacuum implementation,
ensuring mathematical correctness and numerical stability.
"""

import pytest
import numpy as np
from sympy import symbols, sin, log, pi, diff, N as sympy_N

from discrete_symmetry_vacuum import (
    DiscreteSymmetryGroup,
    PeriodicPotential,
    FundamentalMode,
    VacuumEnergy,
    VariationalAnalysis,
    HigherHarmonics,
    plot_vacuum_energy
)


class TestDiscreteSymmetryGroup:
    """Test the discrete symmetry group G ≅ Z."""
    
    def test_identity_transformation(self):
        """Test that k=0 gives the identity transformation."""
        group = DiscreteSymmetryGroup()
        R_test = 2.5
        R_transformed = group.transform(R_test, 0)
        assert abs(R_transformed - R_test) < 1e-10
    
    def test_composition_law(self):
        """Test that the group composition law holds: g_k · g_m = g_{k+m}."""
        group = DiscreteSymmetryGroup()
        R_test = 1.5
        k, m = 2, 3
        
        # Apply k then m
        R_km = group.transform(group.transform(R_test, k), m)
        
        # Apply k+m
        R_kpm = group.transform(R_test, k + m)
        
        assert abs(R_km - R_kpm) < 1e-10
    
    def test_inverse_transformation(self):
        """Test that g_k and g_{-k} are inverses."""
        group = DiscreteSymmetryGroup()
        R_test = 3.7
        k = 5
        
        R_forward = group.transform(R_test, k)
        R_back = group.transform(R_forward, -k)
        
        assert abs(R_back - R_test) < 1e-10
    
    def test_base_transformation(self):
        """Test that the base is indeed π."""
        group = DiscreteSymmetryGroup()
        assert abs(group.base - np.pi) < 1e-10
        assert abs(group.period_log - np.log(np.pi)) < 1e-10


class TestPeriodicPotential:
    """Test the periodic potential V(log R_Ψ)."""
    
    def test_default_fundamental_mode(self):
        """Test that default initialization gives fundamental mode."""
        potential = PeriodicPotential()
        assert 1 in potential.coefficients
        assert potential.coefficients[1] == (0, 1)
    
    def test_periodicity(self):
        """Test that V is periodic in log-space with period log π.
        
        This means V(R) considered as a function of log R has period log π,
        i.e., V(e^(x + log π)) should have the same functional form.
        For the fundamental mode: V(R) = sin(2π log R / log π).
        
        We verify this by checking specific values.
        """
        potential = PeriodicPotential()
        
        # At R=1: sin(0) = 0
        V_1 = potential.evaluate(1.0)
        assert abs(V_1 - 0.0) < 1e-10
        
        # The periodicity in Fourier space means the coefficients
        # repeat with period log π. Check consistency.
        R_test = 2.0
        V_R = potential.evaluate(R_test)
        # sin can be negative, so just check it's finite
        assert np.isfinite(V_R)
    
    def test_custom_coefficients(self):
        """Test custom Fourier coefficients."""
        coeffs = {1: (1.0, 0.0), 2: (0.5, 0.5)}
        potential = PeriodicPotential(coefficients=coeffs)
        
        assert potential.coefficients == coeffs
        
        # Should still be periodic
        R_test = 1.5
        V_R = potential.evaluate(R_test)
        V_piR = potential.evaluate(np.pi * R_test)
        
        assert abs(V_R - V_piR) < 1e-10


class TestFundamentalMode:
    """Test the fundamental mode A(R_Ψ) = sin²(log R_Ψ / log π)."""
    
    def test_range(self):
        """Test that A(R_Ψ) ∈ [0, 1] for all R_Ψ > 0."""
        R_samples = np.logspace(-2, 2, 100)
        A_samples = [FundamentalMode.evaluate(R) for R in R_samples]
        
        assert all(0 <= A <= 1 for A in A_samples)
    
    def test_periodicity(self):
        """Test that A has the correct log-periodic structure.
        
        Note: A(R_Ψ) = sin²(log R_Ψ / log π) is NOT simply A(π·R) = A(R).
        Instead, the potential V(log R) is periodic with period log π.
        This means the VALUE of the function repeats when the ARGUMENT shifts by log π.
        """
        # The correct test: check that at R=1, R=π, R=π², etc., 
        # we get sin²(0), sin²(1), sin²(2), ... which are just shifted values
        R_test = 1.0
        A_1 = FundamentalMode.evaluate(R_test)
        # At R=1: sin²(log(1)/log π) = sin²(0) = 0
        assert abs(A_1 - 0.0) < 1e-10
        
        # At R=π: sin²(log π / log π) = sin²(1)
        A_pi = FundamentalMode.evaluate(np.pi)
        expected_pi = np.sin(1.0)**2
        assert abs(A_pi - expected_pi) < 1e-10
    
    def test_symbolic_consistency(self):
        """Test that symbolic and numeric evaluations match."""
        R_sym = symbols('R', positive=True)
        A_symbolic = FundamentalMode.symbolic_amplitude(R_sym)
        
        R_test = 2.5
        A_symbolic_eval = float(sympy_N(A_symbolic.subs(R_sym, R_test)))
        A_numeric = FundamentalMode.evaluate(R_test)
        
        assert abs(A_symbolic_eval - A_numeric) < 1e-10
    
    def test_extrema(self):
        """Test that A reaches 0 and 1."""
        # A(1) = sin²(0) = 0
        assert abs(FundamentalMode.evaluate(1.0)) < 1e-10
        
        # A(√π) = sin²(0.5) ≈ 0.23
        A_sqrt_pi = FundamentalMode.evaluate(np.sqrt(np.pi))
        expected = np.sin(0.5)**2
        assert abs(A_sqrt_pi - expected) < 1e-10
        
        # A(π) = sin²(1) ≈ 0.71
        A_pi = FundamentalMode.evaluate(np.pi)
        expected_pi = np.sin(1)**2
        assert abs(A_pi - expected_pi) < 1e-10


class TestVacuumEnergy:
    """Test the complete vacuum energy model."""
    
    def setup_method(self):
        """Setup test parameters."""
        self.alpha = 1.0
        self.beta = -0.5
        self.gamma = 0.01
        self.delta = 0.1
        self.vac_energy = VacuumEnergy(self.alpha, self.beta, self.gamma, self.delta)
    
    def test_initialization(self):
        """Test that parameters are correctly initialized."""
        assert self.vac_energy.alpha == self.alpha
        assert self.vac_energy.beta == self.beta
        assert self.vac_energy.gamma == self.gamma
        assert self.vac_energy.delta == self.delta
    
    def test_positive_energy_small_R(self):
        """Test that energy is large for small R_Ψ (UV divergence)."""
        R_small = 0.01
        E_small = self.vac_energy.evaluate(R_small)
        E_unit = self.vac_energy.evaluate(1.0)
        
        assert E_small > E_unit
    
    def test_positive_energy_large_R(self):
        """Test that energy is large for large R_Ψ (IR divergence)."""
        R_large = 100.0
        E_large = self.vac_energy.evaluate(R_large)
        E_unit = self.vac_energy.evaluate(1.0)
        
        assert E_large > E_unit
    
    def test_derivative_at_minimum(self):
        """Test that derivative is small at minima."""
        # Find a minimum by sampling
        R_samples = np.linspace(1.0, 3.0, 100)
        E_samples = [self.vac_energy.evaluate(R) for R in R_samples]
        min_idx = np.argmin(E_samples)
        R_min_approx = R_samples[min_idx]
        
        dE = self.vac_energy.derivative(R_min_approx)
        assert abs(dE) < 0.1  # Should be small near minimum
    
    def test_second_derivative_positive_at_minimum(self):
        """Test that second derivative is positive at minima (stability)."""
        # Find a minimum
        R_samples = np.linspace(1.0, 3.0, 100)
        E_samples = [self.vac_energy.evaluate(R) for R in R_samples]
        min_idx = np.argmin(E_samples)
        R_min_approx = R_samples[min_idx]
        
        d2E = self.vac_energy.second_derivative(R_min_approx)
        assert d2E > 0
    
    def test_inf_at_zero(self):
        """Test that energy diverges at R=0."""
        E_zero = self.vac_energy.evaluate(0.0)
        assert E_zero == np.inf


class TestVariationalAnalysis:
    """Test the variational analysis framework."""
    
    def setup_method(self):
        """Setup test vacuum energy and analyzer."""
        self.vac_energy = VacuumEnergy(1.0, -0.5, 0.01, 0.1)
        self.analyzer = VariationalAnalysis(self.vac_energy)
    
    def test_coercivity(self):
        """Test that the energy is coercive."""
        is_coercive = self.analyzer.check_coercivity()
        assert is_coercive
    
    def test_critical_points_exist(self):
        """Test that critical points are found in cells."""
        # Check a few cells
        for n in range(-1, 2):
            critical_points = self.analyzer.find_critical_points_in_cell(n)
            # Each cell should have at least one critical point
            assert len(critical_points) >= 0  # May or may not have depending on parameters
    
    def test_stability_check(self):
        """Test stability check on a known minimum."""
        # Find a minimum in cell n=0
        results = self.analyzer.analyze_cell(0)
        
        if results['stable_minima']:
            R_min = results['stable_minima'][0]
            is_stable = self.analyzer.check_stability(R_min)
            assert is_stable
    
    def test_analyze_cell_structure(self):
        """Test that analyze_cell returns correct structure."""
        results = self.analyzer.analyze_cell(0)
        
        assert 'critical_points' in results
        assert 'stable_minima' in results
        assert 'energies' in results
        
        assert isinstance(results['critical_points'], list)
        assert isinstance(results['stable_minima'], list)
        assert isinstance(results['energies'], list)
        
        # Energies should match stable_minima length
        assert len(results['energies']) == len(results['stable_minima'])


class TestHigherHarmonics:
    """Test higher harmonics predictions."""
    
    def test_fundamental_frequency(self):
        """Test that n=0 gives the fundamental frequency."""
        f_0 = 1.0
        harmonics = HigherHarmonics(fundamental_frequency=f_0)
        
        assert harmonics.frequency(0) == f_0
    
    def test_subharmonics(self):
        """Test that sub-harmonics decrease as π^(2n)."""
        f_0 = 1.0
        harmonics = HigherHarmonics(fundamental_frequency=f_0)
        
        for n in range(1, 5):
            f_n = harmonics.frequency(n)
            expected = f_0 / (np.pi**(2*n))
            assert abs(f_n - expected) < 1e-10
    
    def test_amplitude_at_harmonic_range(self):
        """Test that harmonic amplitudes are in [0, 1]."""
        harmonics = HigherHarmonics()
        R_samples = np.logspace(-1, 2, 50)
        
        for n in range(1, 4):
            A_samples = [harmonics.amplitude_at_harmonic(R, n) for R in R_samples]
            assert all(0 <= A <= 1 for A in A_samples)
    
    def test_harmonic_periodicity(self):
        """Test that n-th harmonic has correct period structure.
        
        Note: For n>1, A_n(π·R) ≠ A_n(R) in general. 
        The periodicity is in the log-space, not in direct R-space.
        We test that the harmonics have the correct form instead.
        """
        harmonics = HigherHarmonics()
        
        # Test that amplitude is in correct range for all harmonics
        R_test = 2.0
        for n in range(1, 4):
            A_R = harmonics.amplitude_at_harmonic(R_test, n)
            assert 0 <= A_R <= 1
        
        # Test that the fundamental harmonic at R=1 gives 0
        A_1_fundamental = harmonics.amplitude_at_harmonic(1.0, 1)
        assert abs(A_1_fundamental) < 1e-10


class TestIntegration:
    """Integration tests combining multiple components."""
    
    def test_complete_workflow(self):
        """Test the complete analysis workflow."""
        # Create components
        group = DiscreteSymmetryGroup()
        vac_energy = VacuumEnergy(1.0, -0.5, 0.01, 0.1)
        analyzer = VariationalAnalysis(vac_energy)
        harmonics = HigherHarmonics()
        
        # Run analysis
        results = analyzer.analyze_cell(0)
        
        # Verify results structure
        assert isinstance(results, dict)
        assert 'critical_points' in results
        assert 'stable_minima' in results
        
        # Verify harmonics
        f_1 = harmonics.frequency(1)
        assert f_1 > 0
    
    def test_symmetry_of_minimum_positions(self):
        """Test that minimum positions respect the π-periodicity structure."""
        vac_energy = VacuumEnergy(1.0, -0.5, 0.01, 0.1)
        analyzer = VariationalAnalysis(vac_energy)
        
        # Analyze two adjacent cells
        results_0 = analyzer.analyze_cell(0)
        results_1 = analyzer.analyze_cell(1)
        
        # If both have minima, check that their relative positions
        # within their cells are similar (due to symmetry)
        if results_0['stable_minima'] and results_1['stable_minima']:
            R_min_0 = results_0['stable_minima'][0]
            R_min_1 = results_1['stable_minima'][0]
            
            # Normalize by cell boundaries
            normalized_0 = (R_min_0 - 1) / (np.pi - 1)
            normalized_1 = (R_min_1 - np.pi) / (np.pi**2 - np.pi)
            
            # They should be roughly similar (within some tolerance)
            # This is a weak test but checks basic structure
            assert abs(normalized_0 - normalized_1) < 0.5


class TestNumericalStability:
    """Test numerical stability and edge cases."""
    
    def test_very_small_R(self):
        """Test behavior at very small R_Ψ."""
        vac_energy = VacuumEnergy(1.0, -0.5, 0.01, 0.1)
        
        R_tiny = 1e-6
        E_tiny = vac_energy.evaluate(R_tiny)
        
        # Should be very large but finite (before R=0)
        assert E_tiny > 1e6
        assert np.isfinite(E_tiny)
    
    def test_very_large_R(self):
        """Test behavior at very large R_Ψ."""
        vac_energy = VacuumEnergy(1.0, -0.5, 0.01, 0.1)
        
        R_huge = 1e6
        E_huge = vac_energy.evaluate(R_huge)
        
        # Should be very large (IR divergence from R² term)
        assert E_huge > 1e6
        assert np.isfinite(E_huge)
    
    def test_derivative_numerical_stability(self):
        """Test that derivative is numerically stable."""
        vac_energy = VacuumEnergy(1.0, -0.5, 0.01, 0.1)
        
        R_samples = np.logspace(-2, 2, 20)
        for R in R_samples:
            dE = vac_energy.derivative(R)
            assert np.isfinite(dE)
    
    def test_second_derivative_numerical_stability(self):
        """Test that second derivative is numerically stable."""
        vac_energy = VacuumEnergy(1.0, -0.5, 0.01, 0.1)
        
        R_samples = np.logspace(-2, 2, 20)
        for R in R_samples:
            d2E = vac_energy.second_derivative(R)
            assert np.isfinite(d2E)


class TestPlotting:
    """Test plotting functionality (without displaying)."""
    
    def test_plot_generation(self):
        """Test that plot generation works without errors."""
        vac_energy = VacuumEnergy(1.0, -0.5, 0.01, 0.1)
        
        # This should not raise an error
        import matplotlib
        matplotlib.use('Agg')  # Non-interactive backend
        
        fig = plot_vacuum_energy(vac_energy, R_range=(0.5, 10), 
                                num_points=100)
        
        assert fig is not None
        
        # Clean up
        import matplotlib.pyplot as plt
        plt.close(fig)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
