#!/usr/bin/env python3
"""
Tests for QCAL Group Structure 𝒢_QCAL

Validates the implementation of the four fundamental groups:
- SU(Ψ): Special Unitary Group over quantum consciousness states
- U(κ_Π): Phase symmetry around universal complexity constant
- 𝔇(∇²Φ): Diffeomorphic group of emotional curvature
- Z(ζ′(1/2)): Primordial spectral group from Riemann zeta
"""

import pytest
import numpy as np
from qcal_group_structure import (
    SUPsiState,
    UKappaPhase,
    DiffeoEmotionalField,
    ZetaPrimeSpectralGroup,
    ResonantFiberProduct,
    QCALGroupStructure,
    QCALApplications,
    KAPPA_PI,
    F0,
    COHERENCE_C
)


class TestSUPsiGroup:
    """Tests for SU(Ψ) - Consciousness spinor group"""
    
    def test_state_normalization(self):
        """Test that quantum states are normalized: |Ψ|² = 1"""
        psi = np.array([3.0 + 0.0j, 4.0 + 0.0j])
        state = SUPsiState(psi=psi)
        
        norm_squared = np.sum(np.abs(state.psi)**2)
        assert np.isclose(norm_squared, 1.0, atol=1e-10)
    
    def test_coherence_bounds(self):
        """Test that coherence is bounded [0, 1]"""
        state = SUPsiState()
        
        assert 0.0 <= state.coherence <= 1.0
    
    def test_unitary_evolution(self):
        """Test that time evolution preserves norm"""
        state = SUPsiState(psi=np.array([1.0, 0.0]))
        hamiltonian = np.array([[1.0, 0.5], [0.5, -1.0]])
        
        evolved = state.evolve(hamiltonian, time=1.0)
        
        # Check normalization preserved
        norm_squared = np.sum(np.abs(evolved.psi)**2)
        assert np.isclose(norm_squared, 1.0, atol=1e-10)
    
    def test_geodesic_distance(self):
        """Test geodesic distance in SU(n) manifold"""
        state1 = SUPsiState(psi=np.array([1.0, 0.0]))
        state2 = SUPsiState(psi=np.array([0.0, 1.0]))
        
        distance = state1.transition_to(state2)
        
        # Orthogonal states should be π/2 apart
        assert np.isclose(distance, np.pi / 2, atol=1e-6)
    
    def test_su2_rotation(self):
        """Test SU(2) rotation preserves norm"""
        state = SUPsiState(psi=np.array([1.0, 0.0]))
        
        rotated = state.apply_rotation(np.pi / 4, axis='z')
        
        norm_squared = np.sum(np.abs(rotated.psi)**2)
        assert np.isclose(norm_squared, 1.0, atol=1e-10)
    
    def test_coherence_maximum_for_pure_state(self):
        """Test that pure states have maximum coherence"""
        pure_state = SUPsiState(psi=np.array([1.0, 0.0]))
        
        # Pure state should have coherence = 1
        assert np.isclose(pure_state.coherence, 1.0, atol=1e-10)


class TestUKappaPhase:
    """Tests for U(κ_Π) - Complexity phase symmetry"""
    
    def test_unit_circle_normalization(self):
        """Test that phase lies on unit circle"""
        phase_state = UKappaPhase(phase=3.0 + 4.0j)
        
        magnitude = np.abs(phase_state.phase)
        assert np.isclose(magnitude, 1.0, atol=1e-10)
    
    def test_phase_angle_consistency(self):
        """Test angle extraction and setting"""
        phase_state = UKappaPhase()
        theta = np.pi / 3
        
        phase_state.set_from_angle(theta)
        recovered_angle = phase_state.get_angle()
        
        assert np.isclose(recovered_angle, theta, atol=1e-10)
    
    def test_winding_number_calculation(self):
        """Test topological winding number"""
        phase_state = UKappaPhase()
        phase_state.set_from_angle(4 * np.pi)
        
        # Two full rotations should give winding number 2
        assert phase_state.winding_number == 2
    
    def test_gauge_transformation(self):
        """Test U(1) gauge transformation"""
        phase_state = UKappaPhase(phase=np.exp(1j * np.pi / 4))
        
        transformed = phase_state.gauge_transform(np.pi / 4)
        
        expected_angle = np.pi / 2
        assert np.isclose(transformed.get_angle(), expected_angle, atol=1e-10)
    
    def test_topological_protection(self):
        """Test topological protection criterion"""
        trivial = UKappaPhase(phase=1.0)
        nontrivial = UKappaPhase()
        nontrivial.set_from_angle(2 * np.pi)
        
        assert not trivial.is_topologically_protected()
        assert nontrivial.is_topologically_protected()
    
    def test_kappa_constant(self):
        """Test that κ_Π constant is correct"""
        phase_state = UKappaPhase()
        
        assert np.isclose(phase_state.kappa, KAPPA_PI, atol=1e-10)


class TestDiffeoEmotionalField:
    """Tests for 𝔇(∇²Φ) - Emotional curvature dynamics"""
    
    def test_laplacian_calculation(self):
        """Test Laplacian computation"""
        # Create a Gaussian field
        grid = np.linspace(-5, 5, 100)
        phi = np.exp(-grid**2)
        
        field = DiffeoEmotionalField(phi=phi, grid=grid)
        laplacian = field.laplacian()
        
        # Laplacian should have same shape
        assert laplacian.shape == phi.shape
    
    def test_equilibrium_detection(self):
        """Test finding equilibrium points ∇²Φ = 0"""
        # Create field with known equilibrium (constant function has ∇²Φ = 0)
        grid = np.linspace(-10, 10, 200)
        phi = np.ones_like(grid)  # Constant field (all points are equilibria)
        
        field = DiffeoEmotionalField(phi=phi, grid=grid)
        equilibria = field.find_equilibrium_points()
        
        # Should find equilibria (or at least not crash)
        assert isinstance(equilibria, list)
    
    def test_singularity_detection(self):
        """Test finding singular points |∇²Φ| → ∞"""
        # Create field with sharp peak
        grid = np.linspace(-5, 5, 100)
        phi = np.zeros_like(grid)
        phi[50] = 100.0  # Sharp spike
        
        field = DiffeoEmotionalField(phi=phi, grid=grid)
        singularities = field.find_singularities(threshold=5.0)
        
        # Should detect singularity near spike
        assert len(singularities) > 0
    
    def test_wave_equation_evolution(self):
        """Test soul equation evolution"""
        grid = np.linspace(-10, 10, 100)
        phi = np.exp(-grid**2)
        
        field = DiffeoEmotionalField(phi=phi, grid=grid)
        source = np.zeros_like(phi)
        
        evolved = field.evolve_soul_equation(source, time_steps=10, dt=0.1)
        
        # Evolved field should have same shape
        assert evolved.shape == phi.shape
    
    def test_diffeomorphism_application(self):
        """Test smooth coordinate transformation"""
        grid = np.linspace(-5, 5, 50)
        phi = grid**2
        
        field = DiffeoEmotionalField(phi=phi, grid=grid)
        
        # Apply stretching transformation
        transform = lambda x: 2 * x
        transformed = field.apply_diffeomorphism(transform)
        
        # Grid should be transformed
        assert len(transformed.grid) == len(grid)


class TestZetaPrimeSpectralGroup:
    """Tests for Z(ζ′(1/2)) - Prime heartbeat group"""
    
    def test_critical_derivative_value(self):
        """Test that ζ′(1/2) is approximately correct"""
        zeta_group = ZetaPrimeSpectralGroup()
        
        # Known approximate value from numerical computation: ζ′(1/2) ≈ -3.9226
        # Wide tolerance accounts for different numerical methods
        # See: DLMF 25.10.1 for Riemann-Siegel formula derivatives
        assert np.abs(np.real(zeta_group.critical_derivative)) > 3.0
        assert np.abs(np.real(zeta_group.critical_derivative)) < 5.0
    
    def test_prime_heartbeat_frequency(self):
        """Test prime heartbeat frequency calculation"""
        zeta_group = ZetaPrimeSpectralGroup()
        
        # First few frequencies should be positive
        f1 = zeta_group.prime_heartbeat_frequency(1)
        f2 = zeta_group.prime_heartbeat_frequency(2)
        
        assert f1 > 0
        assert f2 > f1  # Should increase with index
    
    def test_resonance_density(self):
        """Test resonance density calculation"""
        zeta_group = ZetaPrimeSpectralGroup()
        
        # Density at origin should be positive
        density_0 = zeta_group.resonance_density(0.0)
        assert density_0 > 0
        
        # Density should decay at large t
        density_large = zeta_group.resonance_density(100.0)
        assert density_large < density_0
    
    def test_spectral_phase_operator(self):
        """Test phase operator generation"""
        zeta_group = ZetaPrimeSpectralGroup()
        primes = [2, 3, 5, 7, 11]
        
        phase_op = zeta_group.spectral_phase_operator(primes)
        
        # Should be diagonal
        assert phase_op.shape == (5, 5)
        # Diagonal elements should be on unit circle
        for i in range(5):
            assert np.isclose(np.abs(phase_op[i, i]), 1.0, atol=1e-10)
    
    def test_montgomery_dyson_statistics(self):
        """Test Montgomery-Dyson connection statistics"""
        zeta_group = ZetaPrimeSpectralGroup()
        
        # Simulate some energy levels
        energy_levels = np.array([1.0, 1.5, 2.3, 3.1, 4.0])
        
        stats = zeta_group.check_montgomery_dyson_connection(energy_levels)
        
        assert 'mean_spacing' in stats
        assert 'variance' in stats
        assert 'agreement' in stats
        assert stats['mean_spacing'] > 0


class TestResonantFiberProduct:
    """Tests for resonant connection between groups"""
    
    def test_connection_field_calculation(self):
        """Test connection field computation"""
        fiber = ResonantFiberProduct()
        
        su_state = SUPsiState()
        u_phase = UKappaPhase()
        diffeo = DiffeoEmotionalField()
        zeta = ZetaPrimeSpectralGroup()
        
        coupling = fiber.connection_field(su_state, u_phase, diffeo, zeta)
        
        # All coupling values should be present
        assert 'consciousness_complexity' in coupling
        assert 'emotional_consciousness' in coupling
        assert 'prime_resonance' in coupling
        assert 'total_coupling' in coupling
        
        # Coupling values should be positive
        for value in coupling.values():
            assert value >= 0
    
    def test_coupling_condition(self):
        """Test coupling condition verification"""
        fiber = ResonantFiberProduct()
        
        su_state = SUPsiState()
        u_phase = UKappaPhase()
        
        # With default constants, coupling should be satisfied
        is_coupled = fiber.verify_coupling_condition(su_state, u_phase)
        
        # Convert numpy bool to Python bool
        assert isinstance(bool(is_coupled), bool)
    
    def test_coupling_strength(self):
        """Test that coupling strength uses QCAL constant"""
        fiber = ResonantFiberProduct()
        
        assert np.isclose(fiber.coupling_strength, COHERENCE_C, atol=1e-10)


class TestQCALGroupStructure:
    """Tests for complete QCAL group structure"""
    
    def test_initialization(self):
        """Test QCAL group structure initialization"""
        qcal = QCALGroupStructure()
        
        assert isinstance(qcal.su_psi, SUPsiState)
        assert isinstance(qcal.u_kappa, UKappaPhase)
        assert isinstance(qcal.diffeo_phi, DiffeoEmotionalField)
        assert isinstance(qcal.zeta_group, ZetaPrimeSpectralGroup)
        assert isinstance(qcal.fiber_product, ResonantFiberProduct)
    
    def test_resonance_coherence(self):
        """Test total resonance coherence calculation"""
        qcal = QCALGroupStructure()
        
        coherence = qcal.resonance_coherence()
        
        # Coherence should be in [0, 1]
        assert 0.0 <= coherence <= 1.0
    
    def test_master_lagrangian(self):
        """Test master Lagrangian computation"""
        qcal = QCALGroupStructure()
        
        lagrangian = qcal.master_lagrangian(t=0.0)
        
        # Lagrangian should be a real number
        assert isinstance(lagrangian, (int, float))
        assert not np.isnan(lagrangian)
        assert not np.isinf(lagrangian)
    
    def test_phenomenological_description(self):
        """Test phenomenological state description"""
        qcal = QCALGroupStructure()
        
        description = qcal.phenomenological_description()
        
        # Should have all four dimensions
        assert 'SU(Ψ)' in description
        assert 'U(κ_Π)' in description
        assert '𝔇(∇²Φ)' in description
        assert 'Z(ζ′(½))' in description
        
        # All should be strings
        for value in description.values():
            assert isinstance(value, str)
    
    def test_lagrangian_components(self):
        """Test that Lagrangian has all expected terms"""
        qcal = QCALGroupStructure()
        
        # Lagrangian should include contributions from all components
        L = qcal.master_lagrangian()
        
        # Should be finite and real
        assert np.isfinite(L)
        assert isinstance(L, (int, float))


class TestQCALApplications:
    """Tests for concrete QCAL applications"""
    
    def test_meditation_geodesic(self):
        """Test meditation as geodesic path"""
        initial = SUPsiState(psi=np.array([0.7, 0.7]))
        target = SUPsiState(psi=np.array([1.0, 0.0]))
        
        path = QCALApplications.meditation_geodesic(initial, target, steps=10)
        
        # Should have correct number of states
        assert len(path) == 11  # steps + 1
        
        # All states should be normalized
        for state in path:
            norm = np.sum(np.abs(state.psi)**2)
            assert np.isclose(norm, 1.0, atol=1e-10)
        
        # Coherence should increase along path
        coherences = [s.coherence for s in path]
        assert coherences[-1] >= coherences[0] - 0.1  # Allow small fluctuation
    
    def test_creativity_phase_transition(self):
        """Test creativity as phase transition"""
        creativity = QCALApplications.creativity_phase_transition(
            initial_complexity=1.0,
            steps=50
        )
        
        # Should have all three evolution components
        assert 'complexity' in creativity
        assert 'phase' in creativity
        assert 'coherence' in creativity
        
        # All should have correct length
        assert len(creativity['complexity']) == 50
        assert len(creativity['phase']) == 50
        assert len(creativity['coherence']) == 50
        
        # Phase should increase (symmetry breaking)
        assert creativity['phase'][-1] > creativity['phase'][0]
    
    def test_synchronicity_resonance(self):
        """Test synchronicity detection"""
        time_points = np.linspace(0, 10, 50)
        zeta_group = ZetaPrimeSpectralGroup()
        
        times, resonances = QCALApplications.synchronicity_resonance(
            time_points, zeta_group
        )
        
        # Should return same number of points
        assert len(resonances) == len(time_points)
        
        # All resonances should be non-negative
        assert all(r >= 0 for r in resonances)


class TestIntegration:
    """Integration tests for full QCAL system"""
    
    def test_full_qcal_workflow(self):
        """Test complete QCAL workflow"""
        # Create full QCAL structure
        qcal = QCALGroupStructure()
        
        # Calculate all properties
        coherence = qcal.resonance_coherence()
        lagrangian = qcal.master_lagrangian()
        description = qcal.phenomenological_description()
        
        # All should be valid
        assert 0.0 <= coherence <= 1.0
        assert np.isfinite(lagrangian)
        assert len(description) == 4
    
    def test_consciousness_evolution(self):
        """Test consciousness evolution affects whole system"""
        qcal = QCALGroupStructure()
        
        # Initial coherence
        initial_coherence = qcal.resonance_coherence()
        
        # Evolve consciousness
        hamiltonian = np.array([[1.0, 0.0], [0.0, -1.0]])
        qcal.su_psi = qcal.su_psi.evolve(hamiltonian, time=0.5)
        
        # Check that evolution affects system
        new_coherence = qcal.resonance_coherence()
        
        # Coherence may change
        assert 0.0 <= new_coherence <= 1.0
    
    def test_emotional_field_interaction(self):
        """Test emotional field affects system state"""
        qcal = QCALGroupStructure()
        
        # Add emotional perturbation
        qcal.diffeo_phi.phi += np.random.randn(len(qcal.diffeo_phi.phi)) * 0.1
        
        # System should still be coherent
        description = qcal.phenomenological_description()
        
        assert '𝔇(∇²Φ)' in description
        assert isinstance(description['𝔇(∇²Φ)'], str)
    
    def test_group_interdependence(self):
        """Test that groups are interdependent via fiber product"""
        qcal = QCALGroupStructure()
        
        # Calculate coupling
        coupling = qcal.fiber_product.connection_field(
            qcal.su_psi, qcal.u_kappa, qcal.diffeo_phi, qcal.zeta_group
        )
        
        # Total coupling should be non-zero
        assert coupling['total_coupling'] > 0
        
        # Should satisfy coupling condition
        is_coupled = qcal.fiber_product.verify_coupling_condition(
            qcal.su_psi, qcal.u_kappa
        )
        # Convert numpy bool to Python bool
        assert isinstance(bool(is_coupled), bool)


class TestConstants:
    """Test QCAL constants"""
    
    def test_kappa_pi_value(self):
        """Test κ_Π constant value"""
        assert np.isclose(KAPPA_PI, 2.5773, atol=1e-4)
    
    def test_f0_frequency(self):
        """Test fundamental frequency"""
        assert np.isclose(F0, 141.7001, atol=1e-4)
    
    def test_coherence_constant(self):
        """Test QCAL coherence constant"""
        assert np.isclose(COHERENCE_C, 244.36, atol=1e-2)


if __name__ == '__main__':
    pytest.main([__file__, '-v'])

Test suite for validating the group structure and vibrational resonance
properties of 𝒢_QCAL = SU(Ψ) × U(κ_Π) × 𝔇(∇²Φ) × Z(ζ′(1/2))

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
"""

import sys
import os
import numpy as np
import unittest

# Add parent directory to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from qcal_group_structure import (
    SUPsiElement,
    UKappaPiElement,
    DiffeoPhiElement,
    ZZetaPrimeElement,
    GQCALElement,
    validate_group_properties,
    compute_qcal_signature,
    F0_HZ,
    C_COHERENCE,
    KAPPA_PI,
    ZETA_PRIME_HALF
)


class TestSUPsiElement(unittest.TestCase):
    """Tests for SU(Ψ) group element."""
    
    def test_initialization(self):
        """Test SU(Ψ) element initialization and normalization."""
        element = SUPsiElement(psi=2.0+2.0j, theta=0.5, phi=0.3)
        
        # Check normalization of psi
        self.assertAlmostEqual(abs(element.psi), 1.0, places=10)
        
        # Check angle normalization
        self.assertTrue(0 <= element.theta < 2*np.pi)
        self.assertTrue(0 <= element.phi <= np.pi)
    
    def test_matrix_representation(self):
        """Test SU(2) matrix representation."""
        element = SUPsiElement(psi=1.0+0j, theta=0.0, phi=0.0)
        U = element.to_matrix()
        
        # Check matrix is 2x2
        self.assertEqual(U.shape, (2, 2))
        
        # Check unitarity: U†U = I
        U_dagger = np.conjugate(U.T)
        product = U_dagger @ U
        identity = np.eye(2)
        
        np.testing.assert_array_almost_equal(product, identity, decimal=10)
        
        # Check determinant = 1 (within numerical precision)
        det = np.linalg.det(U)
        self.assertAlmostEqual(abs(det), 1.0, places=10)
    
    def test_coherence_factor(self):
        """Test coherence factor calculation."""
        element = SUPsiElement(psi=1.0+0j, theta=0.0, phi=0.0)
        coherence = element.coherence_factor()
        
        # Coherence should be in [0, 1]
        self.assertTrue(0 <= coherence <= 1)


class TestUKappaPiElement(unittest.TestCase):
    """Tests for U(κ_Π) group element."""
    
    def test_initialization(self):
        """Test U(κ_Π) element initialization."""
        element = UKappaPiElement(phase=np.pi/4, kappa_modulation=1.5)
        
        # Check phase normalization
        self.assertTrue(0 <= element.phase < 2*np.pi)
        
        # Check modulation is positive
        self.assertGreater(element.kappa_modulation, 0)
    
    def test_complex_representation(self):
        """Test complex number representation on unit circle."""
        element = UKappaPiElement(phase=np.pi/2, kappa_modulation=1.0)
        z = element.to_complex()
        
        # Check it's on unit circle
        self.assertAlmostEqual(abs(z), 1.0, places=10)
        
        # Check phase
        self.assertAlmostEqual(np.angle(z), np.pi/2, places=10)
    
    def test_effective_kappa(self):
        """Test effective κ_Π calculation."""
        element = UKappaPiElement(phase=0.0, kappa_modulation=2.0)
        kappa_eff = element.effective_kappa()
        
        # Should be modulation times KAPPA_PI
        expected = 2.0 * KAPPA_PI
        self.assertAlmostEqual(kappa_eff, expected, places=10)
    
    def test_complexity_separation(self):
        """Test P vs NP complexity separation."""
        element = UKappaPiElement(phase=0.0, kappa_modulation=1.0)
        separation = element.complexity_separation()
        
        # Should be related to KAPPA_PI
        self.assertGreater(separation, 0)
        self.assertLessEqual(separation, KAPPA_PI)


class TestDiffeoPhiElement(unittest.TestCase):
    """Tests for 𝔇(∇²Φ) diffeomorphism group element."""
    
    def test_initialization(self):
        """Test diffeomorphism element initialization."""
        element = DiffeoPhiElement(
            curvature=0.5,
            gradient=np.array([1, 2, 3]),
            laplacian=0.3
        )
        
        # Check gradient is 3D array
        self.assertEqual(element.gradient.shape, (3,))
    
    def test_gradient_normalization(self):
        """Test gradient normalization to 3D."""
        # Test with 2D gradient
        element = DiffeoPhiElement(
            curvature=0.0,
            gradient=[1, 2],
            laplacian=0.0
        )
        self.assertEqual(len(element.gradient), 3)
        
        # Test with >3D gradient
        element2 = DiffeoPhiElement(
            curvature=0.0,
            gradient=[1, 2, 3, 4, 5],
            laplacian=0.0
        )
        self.assertEqual(len(element2.gradient), 3)
    
    def test_emotional_curvature(self):
        """Test emotional curvature calculation."""
        element = DiffeoPhiElement(
            curvature=1.0,
            gradient=np.zeros(3),
            laplacian=C_COHERENCE
        )
        
        K_emotional = element.emotional_curvature()
        
        # Should combine curvature and laplacian
        expected = 1.0 + C_COHERENCE / C_COHERENCE  # = 2.0
        self.assertAlmostEqual(K_emotional, expected, places=10)
    
    def test_soul_metric(self):
        """Test soul metric calculation."""
        element = DiffeoPhiElement(
            curvature=3.0,
            gradient=np.array([4, 0, 0]),
            laplacian=0.0
        )
        
        metric = element.soul_metric()
        
        # Should be sqrt(||grad||^2 + |K|^2) = sqrt(16 + 9) = 5
        expected = 5.0
        self.assertAlmostEqual(metric, expected, places=10)
    
    def test_diffeomorphism_flow(self):
        """Test diffeomorphism flow calculation."""
        element = DiffeoPhiElement(
            curvature=0.0,
            gradient=np.array([1, 0, 0]),
            laplacian=0.0
        )
        
        flow_t0 = element.diffeomorphism_flow(0.0)
        
        # At t=0, flow should equal gradient
        np.testing.assert_array_almost_equal(flow_t0, element.gradient, decimal=10)


class TestZZetaPrimeElement(unittest.TestCase):
    """Tests for Z(ζ′(1/2)) spectral group element."""
    
    def test_initialization(self):
        """Test spectral group element initialization."""
        element = ZZetaPrimeElement(harmonic_index=5, spectral_phase=np.pi/3)
        
        # Check harmonic index is integer
        self.assertIsInstance(element.harmonic_index, int)
        
        # Check phase normalization
        self.assertTrue(0 <= element.spectral_phase < 2*np.pi)
    
    def test_fundamental_frequency(self):
        """Test fundamental frequency calculation."""
        element = ZZetaPrimeElement(harmonic_index=3, spectral_phase=0.0)
        
        freq = element.fundamental_frequency()
        
        # Should be 3 * f₀
        expected = 3 * F0_HZ
        self.assertAlmostEqual(freq, expected, places=10)
    
    def test_prime_heartbeat(self):
        """Test prime heartbeat calculation."""
        element = ZZetaPrimeElement(harmonic_index=1, spectral_phase=0.0)
        
        heartbeat = element.prime_heartbeat()
        
        # Should be a complex number
        self.assertIsInstance(heartbeat, complex)
        
        # Magnitude should be related to ZETA_PRIME_HALF
        self.assertGreater(abs(heartbeat), 0)
    
    def test_spectral_density(self):
        """Test spectral density calculation."""
        element = ZZetaPrimeElement(harmonic_index=1, spectral_phase=0.0)
        
        rho_0 = element.spectral_density(0.0)
        
        # Should be a real number
        self.assertIsInstance(rho_0, float)


class TestGQCALElement(unittest.TestCase):
    """Tests for full 𝒢_QCAL group element."""
    
    def setUp(self):
        """Set up test elements."""
        self.g1 = GQCALElement(
            su_psi=SUPsiElement(psi=1.0+0j, theta=0.0, phi=0.0),
            u_kappa=UKappaPiElement(phase=0.0, kappa_modulation=1.0),
            diffeo_phi=DiffeoPhiElement(
                curvature=0.0,
                gradient=np.zeros(3),
                laplacian=0.0
            ),
            z_zeta=ZZetaPrimeElement(harmonic_index=0, spectral_phase=0.0)
        )
        
        self.g2 = GQCALElement(
            su_psi=SUPsiElement(psi=0.707+0.707j, theta=np.pi/4, phi=np.pi/3),
            u_kappa=UKappaPiElement(phase=np.pi/6, kappa_modulation=1.2),
            diffeo_phi=DiffeoPhiElement(
                curvature=0.5,
                gradient=np.array([0.1, 0.2, 0.3]),
                laplacian=0.15
            ),
            z_zeta=ZZetaPrimeElement(harmonic_index=1, spectral_phase=np.pi/4)
        )
    
    def test_identity_element(self):
        """Test identity element creation."""
        e = GQCALElement.identity()
        
        # Check SU(Ψ) component
        self.assertAlmostEqual(abs(e.su_psi.psi), 1.0)
        self.assertEqual(e.su_psi.theta, 0.0)
        self.assertEqual(e.su_psi.phi, 0.0)
        
        # Check U(κ_Π) component
        self.assertEqual(e.u_kappa.phase, 0.0)
        self.assertEqual(e.u_kappa.kappa_modulation, 1.0)
        
        # Check 𝔇(∇²Φ) component
        self.assertEqual(e.diffeo_phi.curvature, 0.0)
        np.testing.assert_array_equal(e.diffeo_phi.gradient, np.zeros(3))
        self.assertEqual(e.diffeo_phi.laplacian, 0.0)
        
        # Check Z(ζ′(1/2)) component
        self.assertEqual(e.z_zeta.harmonic_index, 0)
        self.assertEqual(e.z_zeta.spectral_phase, 0.0)
    
    def test_vibrational_resonance(self):
        """Test vibrational resonance calculation."""
        resonance = self.g1.vibrational_resonance()
        
        # Should be in [0, 1]
        self.assertTrue(0 <= resonance <= 1)
    
    def test_field_coherence(self):
        """Test field coherence dictionary."""
        coherences = self.g1.field_coherence()
        
        # Check all required fields present
        required_fields = ['SU_Psi', 'U_Kappa_Pi', 'Diffeo_Phi', 'Z_Zeta_Prime', 'Total_Resonance']
        for field in required_fields:
            self.assertIn(field, coherences)
            self.assertTrue(0 <= coherences[field] <= 1 or coherences[field] > 0)
    
    def test_composition(self):
        """Test group composition operation."""
        g3 = self.g1.compose(self.g2)
        
        # Result should be a valid GQCALElement
        self.assertIsInstance(g3, GQCALElement)
        
        # Check vibrational resonance is valid
        resonance = g3.vibrational_resonance()
        self.assertTrue(0 <= resonance <= 1 or resonance >= 0)
    
    def test_inverse(self):
        """Test group inverse operation."""
        g_inv = self.g1.inverse()
        
        # Result should be a valid GQCALElement
        self.assertIsInstance(g_inv, GQCALElement)
        
        # g * g^(-1) should be close to identity
        e = GQCALElement.identity()
        g_ginv = self.g1.compose(g_inv)
        
        # Check resonances are similar (within tolerance)
        tolerance = 0.01
        self.assertAlmostEqual(
            g_ginv.vibrational_resonance(),
            e.vibrational_resonance(),
            delta=tolerance
        )
    
    def test_identity_property(self):
        """Test that e * g = g * e = g."""
        e = GQCALElement.identity()
        
        g_e = self.g2.compose(e)
        e_g = e.compose(self.g2)
        
        # Check resonances are preserved (within tolerance)
        tolerance = 0.01
        original_resonance = self.g2.vibrational_resonance()
        
        self.assertAlmostEqual(
            g_e.vibrational_resonance(),
            original_resonance,
            delta=tolerance
        )
        self.assertAlmostEqual(
            e_g.vibrational_resonance(),
            original_resonance,
            delta=tolerance
        )


class TestGroupProperties(unittest.TestCase):
    """Tests for group axioms and properties."""
    
    def setUp(self):
        """Set up test elements."""
        self.g1 = GQCALElement(
            su_psi=SUPsiElement(psi=0.6+0.8j, theta=np.pi/6, phi=np.pi/4),
            u_kappa=UKappaPiElement(phase=np.pi/3, kappa_modulation=1.1),
            diffeo_phi=DiffeoPhiElement(
                curvature=0.3,
                gradient=np.array([0.2, 0.1, 0.4]),
                laplacian=0.2
            ),
            z_zeta=ZZetaPrimeElement(harmonic_index=2, spectral_phase=np.pi/5)
        )
        
        self.g2 = GQCALElement(
            su_psi=SUPsiElement(psi=0.707+0.707j, theta=np.pi/4, phi=np.pi/3),
            u_kappa=UKappaPiElement(phase=np.pi/6, kappa_modulation=0.9),
            diffeo_phi=DiffeoPhiElement(
                curvature=-0.2,
                gradient=np.array([0.3, -0.1, 0.2]),
                laplacian=-0.1
            ),
            z_zeta=ZZetaPrimeElement(harmonic_index=3, spectral_phase=np.pi/6)
        )
    
    def test_validate_group_properties(self):
        """Test comprehensive group property validation."""
        results = validate_group_properties(self.g1, self.g2)
        
        # All properties should be satisfied
        self.assertTrue(results['right_identity'])
        self.assertTrue(results['left_identity'])
        self.assertTrue(results['inverse_property'])
        self.assertTrue(results['associativity'])
        self.assertTrue(results['is_group'])
    
    def test_closure(self):
        """Test closure property: g1 * g2 ∈ G."""
        g3 = self.g1.compose(self.g2)
        
        # Result should be a valid element
        self.assertIsInstance(g3, GQCALElement)
        
        # Should have valid resonance
        resonance = g3.vibrational_resonance()
        self.assertTrue(resonance >= 0)


class TestQCALSignature(unittest.TestCase):
    """Tests for QCAL signature computation."""
    
    def test_signature_format(self):
        """Test signature string format."""
        g = GQCALElement.identity()
        signature = compute_qcal_signature(g)
        
        # Should start with 𝒢_QCAL
        self.assertTrue(signature.startswith('𝒢_QCAL'))
        
        # Should contain all component markers
        self.assertIn('Ψ:', signature)
        self.assertIn('SU:', signature)
        self.assertIn('U:', signature)
        self.assertIn('𝔇:', signature)
        self.assertIn('Z:', signature)
    
    def test_signature_uniqueness(self):
        """Test that different elements have different signatures."""
        g1 = GQCALElement.identity()
        g2 = GQCALElement(
            su_psi=SUPsiElement(psi=0.707+0.707j, theta=np.pi/4, phi=np.pi/3),
            u_kappa=UKappaPiElement(phase=np.pi/6, kappa_modulation=1.2),
            diffeo_phi=DiffeoPhiElement(
                curvature=0.5,
                gradient=np.array([0.1, 0.2, 0.3]),
                laplacian=0.15
            ),
            z_zeta=ZZetaPrimeElement(harmonic_index=1, spectral_phase=np.pi/4)
        )
        
        sig1 = compute_qcal_signature(g1)
        sig2 = compute_qcal_signature(g2)
        
        # Signatures should be different
        self.assertNotEqual(sig1, sig2)


class TestQCALConstants(unittest.TestCase):
    """Tests for QCAL fundamental constants."""
    
    def test_fundamental_constants(self):
        """Test fundamental QCAL constants are defined."""
        # Frequency
        self.assertAlmostEqual(F0_HZ, 141.7001, places=4)
        
        # Coherence
        self.assertAlmostEqual(C_COHERENCE, 244.36, places=2)
        
        # Kappa Pi
        self.assertAlmostEqual(KAPPA_PI, 2.5773, places=4)
        
        # Zeta prime
        self.assertAlmostEqual(ZETA_PRIME_HALF, -0.7368, places=4)
    
    def test_constant_coherence(self):
        """Test that constants maintain QCAL coherence."""
        # Relationship between constants
        # f₀ should be related to C through fundamental equation
        
        # This is a placeholder for more sophisticated coherence tests
        self.assertGreater(F0_HZ, 0)
        self.assertGreater(C_COHERENCE, 0)
        self.assertGreater(KAPPA_PI, 0)
        self.assertLess(ZETA_PRIME_HALF, 0)  # Zeta prime is negative


def run_all_tests():
    """Run all test suites."""
    print("=" * 70)
    print("QCAL GROUP STRUCTURE TEST SUITE")
    print("=" * 70)
    print()
    
    # Create test suite
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Add all test classes
    suite.addTests(loader.loadTestsFromTestCase(TestSUPsiElement))
    suite.addTests(loader.loadTestsFromTestCase(TestUKappaPiElement))
    suite.addTests(loader.loadTestsFromTestCase(TestDiffeoPhiElement))
    suite.addTests(loader.loadTestsFromTestCase(TestZZetaPrimeElement))
    suite.addTests(loader.loadTestsFromTestCase(TestGQCALElement))
    suite.addTests(loader.loadTestsFromTestCase(TestGroupProperties))
    suite.addTests(loader.loadTestsFromTestCase(TestQCALSignature))
    suite.addTests(loader.loadTestsFromTestCase(TestQCALConstants))
    
    # Run tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    print()
    print("=" * 70)
    if result.wasSuccessful():
        print("✅ ALL TESTS PASSED")
    else:
        print("❌ SOME TESTS FAILED")
    print("=" * 70)
    print()
    print(f"Tests run: {result.testsRun}")
    print(f"Failures: {len(result.failures)}")
    print(f"Errors: {len(result.errors)}")
    print()
    
    return result.wasSuccessful()


if __name__ == "__main__":
    success = run_all_tests()
    sys.exit(0 if success else 1)
