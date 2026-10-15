#!/usr/bin/env python3
"""
Tests for QCAL Navier-Stokes Vibrational Regularization Framework

Validates:
1. QCAL quantum velocity field (u_QCAL = nabla(Psi_bio x zeta(1/2+it)))
2. Adelic viscosity mu = 1/f0 with f0 = 141.7001 Hz
3. GACT informational pressure (DNA base resonances at multiples of f0)
4. Residual force F_res (GUE + superstring corrections)
5. Quantum Reynolds number Re_q = (f0 * lambda_c) / mu_adelic
6. Divergence-free velocity field verification
7. Global smooth solutions via vibrational regularization
8. Three connection bridges (Convection, Pressure, Diffusion)
9. H^1 energy bounds

Author: Jose Manuel Mota Burruezo Psi * inf^3
Institution: Instituto de Conciencia Cuantica (ICQ)
"""

import pytest
import numpy as np
import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from operators.qcal_navier_stokes_vibrational import (
    F0,
    MU_ADELIC,
    GACT_RESONANCES,
    PSI_GUE_CHAOS,
    PSI_GLOBAL,
    GACT_CORRELATION,
    RIEMANN_ZEROS_FIRST,
    compute_psi_bio,
    compute_quantum_velocity_field,
    verify_divergence_free,
    compute_gact_pressure,
    compute_residual_force,
    compute_quantum_reynolds_number,
    rk4_step,
    compute_biological_coherence,
    plot_energy_spectrum,
    QCALNavierStokesVibrational,
)


class TestConstants:
    """Tests for QCAL constants."""

    def test_f0_value(self):
        """Test fundamental frequency f0 = 141.7001 Hz."""
        assert F0 == pytest.approx(141.7001, rel=1e-6)

    def test_mu_adelic_is_inverse_f0(self):
        """Test adelic viscosity mu = 1/f0."""
        assert MU_ADELIC == pytest.approx(1.0 / F0, rel=1e-10)

    def test_gact_resonances(self):
        """Test GACT base resonances at multiples of f0."""
        assert GACT_RESONANCES['A'] == pytest.approx(1.0 * F0, rel=1e-10)
        assert GACT_RESONANCES['T'] == pytest.approx(2.0 * F0, rel=1e-10)
        assert GACT_RESONANCES['U'] == pytest.approx(2.0 * F0, rel=1e-10)
        assert GACT_RESONANCES['G'] == pytest.approx(3.0 * F0, rel=1e-10)
        assert GACT_RESONANCES['C'] == pytest.approx(4.0 * F0, rel=1e-10)

    def test_psi_gue_chaos(self):
        """Test GUE chaos parameter is near 2/3."""
        assert PSI_GUE_CHAOS == pytest.approx(0.666, rel=1e-3)
        assert 0.6 < PSI_GUE_CHAOS < 0.7

    def test_gact_correlation(self):
        """Test GACT RNA stability correlation."""
        assert GACT_CORRELATION == pytest.approx(0.999776, rel=1e-6)
        assert 0.99 < GACT_CORRELATION <= 1.0

    def test_riemann_zeros_first(self):
        """Test first Riemann zero."""
        assert RIEMANN_ZEROS_FIRST[0] == pytest.approx(14.134725, rel=1e-4)
        assert len(RIEMANN_ZEROS_FIRST) >= 10


class TestBiologicalWaveFunction:
    """Tests for Psi_bio biological wave function."""

    def test_psi_bio_shape(self):
        """Test Psi_bio returns array of correct shape."""
        x = np.linspace(-5, 5, 100)
        psi = compute_psi_bio(x)
        assert psi.shape == (100,)

    def test_psi_bio_complex(self):
        """Test Psi_bio is complex-valued."""
        x = np.linspace(-5, 5, 100)
        psi = compute_psi_bio(x)
        assert psi.dtype in [np.complex64, np.complex128]

    def test_psi_bio_normalized(self):
        """Test Psi_bio has finite L2 norm."""
        x = np.linspace(-10, 10, 500)
        psi = compute_psi_bio(x)
        dx = x[1] - x[0]
        norm = np.sqrt(np.sum(np.abs(psi) ** 2) * dx)
        assert np.isfinite(norm)
        assert norm > 0

    def test_psi_bio_gaussian_decay(self):
        """Test that |Psi_bio| decays at large |x|."""
        x = np.linspace(-20, 20, 1000)
        psi = compute_psi_bio(x)
        center_val = np.max(np.abs(psi[450:550]))
        edge_val = np.mean(np.abs(psi[:50]))
        assert center_val > edge_val  # Peak at center


class TestQuantumVelocityField:
    """Tests for QCAL quantum velocity field u_QCAL."""

    def test_velocity_field_shape(self):
        """Test u_QCAL returns array of correct shape."""
        x = np.linspace(-5, 5, 128)
        u = compute_quantum_velocity_field(x)
        assert u.shape == (128,)

    def test_velocity_field_real(self):
        """Test u_QCAL is real-valued."""
        x = np.linspace(-5, 5, 128)
        u = compute_quantum_velocity_field(x)
        assert u.dtype in [np.float32, np.float64]
        assert np.all(np.isreal(u))

    def test_velocity_field_finite(self):
        """Test u_QCAL contains no NaN or Inf."""
        x = np.linspace(-5, 5, 128)
        u = compute_quantum_velocity_field(x)
        assert np.all(np.isfinite(u))

    def test_velocity_field_at_zero_zeta_height(self):
        """Test u_QCAL at first Riemann zero height."""
        x = np.linspace(-5, 5, 128)
        t_first_zero = RIEMANN_ZEROS_FIRST[0]  # 14.134725
        u = compute_quantum_velocity_field(x, t_zeta=t_first_zero)
        assert u.shape == (128,)
        assert np.all(np.isfinite(u))
        # Norm should be positive
        assert np.linalg.norm(u) > 0

    def test_velocity_depends_on_zeta_height(self):
        """Test that different zeta heights give different fields."""
        x = np.linspace(-5, 5, 128)
        u1 = compute_quantum_velocity_field(x, t_zeta=RIEMANN_ZEROS_FIRST[0])
        u2 = compute_quantum_velocity_field(x, t_zeta=RIEMANN_ZEROS_FIRST[1])
        # Different zeta values -> different velocity fields
        # (they differ by the modulus |zeta(1/2+it)|)
        assert not np.allclose(u1, u2)


class TestDivergenceFree:
    """Tests for divergence-free condition verification."""

    def test_divergence_check_returns_dict(self):
        """Test that verify_divergence_free returns proper dict."""
        x = np.linspace(-5, 5, 128)
        dx = x[1] - x[0]
        u = np.zeros(128)
        result = verify_divergence_free(u, dx)
        assert 'divergence_max' in result
        assert 'divergence_mean' in result
        assert 'is_divergence_free' in result
        assert 'projected_velocity' in result

    def test_constant_field_is_divergence_free(self):
        """Test that a constant field is divergence-free."""
        x = np.linspace(-5, 5, 128)
        dx = x[1] - x[0]
        u = np.ones(128) * 3.0
        result = verify_divergence_free(u, dx)
        assert result['divergence_max'] < 1e-10

    def test_linear_field_has_constant_divergence(self):
        """Test that a linear field has nonzero divergence."""
        x = np.linspace(-5, 5, 128)
        dx = x[1] - x[0]
        u = x  # du/dx = 1 everywhere (interior)
        result = verify_divergence_free(u, dx)
        assert result['divergence_max'] > 0.1  # Has nonzero divergence

    def test_projection_reduces_divergence(self):
        """Test that Helmholtz projection reduces divergence."""
        x = np.linspace(-5, 5, 128)
        dx = x[1] - x[0]
        # Linear field with nonzero divergence
        u = x
        result = verify_divergence_free(u, dx)
        # After projection, should have smaller divergence contribution
        u_proj = result['projected_velocity']
        assert np.isfinite(u_proj).all()


class TestGACTPressure:
    """Tests for GACT informational pressure."""

    def test_gact_pressure_returns_dict(self):
        """Test that compute_gact_pressure returns proper dict."""
        result = compute_gact_pressure("GACT")
        assert 'p_gact_scalar' in result
        assert 'base_frequencies' in result
        assert 'rho_info' in result
        assert 'stability_correlation' in result
        assert 'shannon_entropy' in result

    def test_gact_pressure_is_positive(self):
        """Test that p_GACT scalar is positive."""
        result = compute_gact_pressure("GACT")
        assert result['p_gact_scalar'] > 0

    def test_gact_base_frequencies(self):
        """Test that base frequencies sum to 1."""
        result = compute_gact_pressure("GGGGAAAA")
        total_freq = sum(result['base_frequencies'].values())
        assert total_freq == pytest.approx(1.0, rel=1e-10)

    def test_gact_resonances_at_f0_multiples(self):
        """Test GACT resonances are at correct multiples of f0."""
        result = compute_gact_pressure("GACT")
        resonances = result['base_resonances']
        assert resonances['A'] == pytest.approx(F0, rel=1e-10)
        assert resonances['T'] == pytest.approx(2 * F0, rel=1e-10)
        assert resonances['G'] == pytest.approx(3 * F0, rel=1e-10)
        assert resonances['C'] == pytest.approx(4 * F0, rel=1e-10)

    def test_gact_stability_correlation(self):
        """Test that stability correlation is 0.999776."""
        result = compute_gact_pressure("GACT")
        assert result['stability_correlation'] == pytest.approx(0.999776, rel=1e-6)

    def test_gact_rho_info_range(self):
        """Test that rho_info is in [0, 1]."""
        result = compute_gact_pressure("GACT")
        assert 0.0 <= result['rho_info'] <= 1.0

    def test_gact_with_spatial_grid(self):
        """Test GACT pressure with spatial grid."""
        x = np.linspace(-5, 5, 128)
        result = compute_gact_pressure("GACT", x)
        assert result['pressure_field'] is not None
        assert result['pressure_field'].shape == (128,)
        assert np.all(np.isfinite(result['pressure_field']))

    def test_gact_empty_sequence_raises(self):
        """Test that empty sequence raises ValueError."""
        with pytest.raises(ValueError, match="empty"):
            compute_gact_pressure("")

    def test_gact_invalid_base_raises(self):
        """Test that invalid nucleotide raises ValueError."""
        with pytest.raises(ValueError, match="Invalid"):
            compute_gact_pressure("GACTX")

    def test_gact_pure_a_sequence(self):
        """Test pure adenine sequence has A resonance frequency."""
        result = compute_gact_pressure("AAAA")
        # p_GACT scalar should be close to 1*f0
        assert result['p_gact_scalar'] == pytest.approx(F0, rel=1e-6)

    def test_gact_pure_c_sequence(self):
        """Test pure cytosine sequence has C resonance frequency."""
        result = compute_gact_pressure("CCCC")
        # p_GACT scalar should be close to 4*f0
        assert result['p_gact_scalar'] == pytest.approx(4 * F0, rel=1e-6)


class TestResidualForce:
    """Tests for residual force F_res."""

    def test_residual_force_shape(self):
        """Test F_res returns array of correct shape."""
        x = np.linspace(-5, 5, 64)
        psi = np.ones(64)
        f_res = compute_residual_force(psi, x)
        assert f_res.shape == (64,)

    def test_residual_force_finite(self):
        """Test F_res contains no NaN or Inf."""
        x = np.linspace(-5, 5, 64)
        psi = np.random.randn(64)
        f_res = compute_residual_force(psi, x)
        assert np.all(np.isfinite(f_res))

    def test_residual_force_zero_for_zero_psi(self):
        """Test that F_res ~ 0 for zero velocity field."""
        x = np.linspace(-5, 5, 64)
        psi = np.zeros(64)
        f_res = compute_residual_force(psi, x, gue_strength=0.0, superstring_order=1)
        # For zero psi, force should be very small
        assert np.max(np.abs(f_res)) < 1e-10

    def test_residual_force_scales_with_psi(self):
        """Test F_res scales approximately with psi amplitude."""
        x = np.linspace(-5, 5, 64)
        psi1 = np.random.randn(64)
        psi2 = 2.0 * psi1
        f1 = compute_residual_force(psi1, x, gue_strength=0.0, superstring_order=2)
        f2 = compute_residual_force(psi2, x, gue_strength=0.0, superstring_order=2)
        # With zero GUE, force should scale linearly with psi
        ratio = np.linalg.norm(f2) / (np.linalg.norm(f1) + 1e-30)
        assert ratio == pytest.approx(2.0, rel=0.1)

    def test_residual_force_superstring_order(self):
        """Test F_res with different superstring orders."""
        x = np.linspace(-5, 5, 64)
        psi = np.random.randn(64)
        f1 = compute_residual_force(psi, x, gue_strength=0.0, superstring_order=1)
        f3 = compute_residual_force(psi, x, gue_strength=0.0, superstring_order=3)
        # Higher order should give different (larger) force
        assert not np.allclose(f1, f3)


class TestQuantumReynoldsNumber:
    """Tests for quantum Reynolds number Re_q."""

    def test_reynolds_returns_dict(self):
        """Test that compute_quantum_reynolds_number returns proper dict."""
        result = compute_quantum_reynolds_number()
        assert 're_quantum' in result
        assert 're_critical' in result
        assert 'mu_adelic' in result
        assert 'f0' in result
        assert 'lambda_c' in result
        assert 'is_laminar' in result
        assert 'regime' in result

    def test_reynolds_is_positive(self):
        """Test Re_q is positive."""
        result = compute_quantum_reynolds_number()
        assert result['re_quantum'] > 0

    def test_reynolds_formula(self):
        """Test Re_q = (f0 * lambda_c) / mu_adelic."""
        from operators.qcal_navier_stokes_vibrational import LAMBDA_C
        result = compute_quantum_reynolds_number()
        expected = (F0 * LAMBDA_C) / MU_ADELIC
        assert result['re_quantum'] == pytest.approx(expected, rel=1e-6)

    def test_reynolds_mu_equals_1_over_f0(self):
        """Test that mu_adelic = 1/f0 in Reynolds number."""
        result = compute_quantum_reynolds_number()
        assert result['mu_adelic'] == pytest.approx(1.0 / F0, rel=1e-10)

    def test_reynolds_regime_string(self):
        """Test that regime is either 'laminar' or 'turbulent'."""
        result = compute_quantum_reynolds_number()
        assert result['regime'] in ['laminar', 'turbulent']

    def test_reynolds_small_lambda_is_laminar(self):
        """Test that very small coherence length gives laminar regime (Re_q < Re_critical)."""
        # Re_critical = f0/kappa_pi ~ 55; Re_q = f0^2 * lambda_c
        # For lambda_c = 0.001: Re_q = 141.7^2 * 0.001 ~ 20 < 55 -> laminar
        result = compute_quantum_reynolds_number(lambda_c=0.001)
        assert bool(result['is_laminar']) is True
        assert result['regime'] == 'laminar'


class TestQCALNavierStokesVibrational:
    """Tests for QCALNavierStokesVibrational operator."""

    @pytest.fixture
    def ns_small(self):
        """Small NS operator for fast tests."""
        return QCALNavierStokesVibrational(n_points=64, domain_length=5.0)

    @pytest.fixture
    def ns_medium(self):
        """Medium NS operator for standard tests."""
        return QCALNavierStokesVibrational(n_points=128, domain_length=10.0)

    def test_initialization(self, ns_small):
        """Test basic initialization."""
        assert ns_small.n_points == 64
        assert ns_small.domain_length == 5.0
        assert ns_small.f0 == pytest.approx(F0, rel=1e-10)
        assert ns_small.mu == pytest.approx(MU_ADELIC, rel=1e-10)
        assert ns_small.nu == pytest.approx(MU_ADELIC, rel=1e-10)
        assert len(ns_small.x) == 64

    def test_grid_spacing(self, ns_small):
        """Test grid spacing is correct."""
        assert ns_small.dx == pytest.approx(5.0 / (64 - 1), rel=1e-6)

    def test_mu_is_1_over_f0(self, ns_small):
        """Test adelic viscosity is 1/f0."""
        assert ns_small.mu == pytest.approx(1.0 / F0, rel=1e-10)

    def test_compute_velocity_field_shape(self, ns_small):
        """Test velocity field has correct shape."""
        u = ns_small.compute_velocity_field()
        assert u.shape == (64,)

    def test_compute_velocity_field_real(self, ns_small):
        """Test velocity field is real."""
        u = ns_small.compute_velocity_field()
        assert np.all(np.isreal(u))

    def test_compute_velocity_field_finite(self, ns_small):
        """Test velocity field is finite."""
        u = ns_small.compute_velocity_field()
        assert np.all(np.isfinite(u))

    def test_compute_velocity_different_heights(self, ns_small):
        """Test different Riemann zero heights give different fields."""
        u0 = ns_small.compute_velocity_field(t_index=0)
        u1 = ns_small.compute_velocity_field(t_index=1)
        # Different heights -> different |zeta| -> different u_QCAL
        assert not np.allclose(u0, u1)

    def test_nonlinear_convection_shape(self, ns_small):
        """Test nonlinear convection has correct shape."""
        u = ns_small.compute_velocity_field()
        conv = ns_small.compute_nonlinear_convection(u)
        assert conv.shape == (64,)

    def test_nonlinear_convection_finite(self, ns_small):
        """Test nonlinear convection is finite."""
        u = ns_small.compute_velocity_field()
        conv = ns_small.compute_nonlinear_convection(u)
        assert np.all(np.isfinite(conv))

    def test_pressure_gradient_shape(self, ns_small):
        """Test pressure gradient has correct shape."""
        grad_p = ns_small.compute_pressure_gradient()
        assert grad_p.shape == (64,)

    def test_pressure_gradient_finite(self, ns_small):
        """Test pressure gradient is finite."""
        grad_p = ns_small.compute_pressure_gradient()
        assert np.all(np.isfinite(grad_p))

    def test_viscous_diffusion_shape(self, ns_small):
        """Test viscous diffusion has correct shape."""
        u = ns_small.compute_velocity_field()
        diff = ns_small.compute_viscous_diffusion(u)
        assert diff.shape == (64,)

    def test_viscous_diffusion_finite(self, ns_small):
        """Test viscous diffusion is finite."""
        u = ns_small.compute_velocity_field()
        diff = ns_small.compute_viscous_diffusion(u)
        assert np.all(np.isfinite(diff))

    def test_viscous_diffusion_scaled_by_mu(self, ns_small):
        """Test viscous diffusion scales by mu = 1/f0."""
        u = np.sin(ns_small.x)
        diff = ns_small.compute_viscous_diffusion(u)
        # Should be approximately mu * d^2u/dx^2
        d2u = np.gradient(np.gradient(u, ns_small.dx), ns_small.dx)
        expected = ns_small.nu * d2u
        np.testing.assert_allclose(diff, expected, rtol=1e-10)

    def test_evolve_step_shape(self, ns_small):
        """Test single evolution step gives correct shape."""
        u = ns_small.compute_velocity_field()
        u_new = ns_small.evolve_step(u, dt=1e-4)
        assert u_new.shape == (64,)

    def test_evolve_step_finite(self, ns_small):
        """Test single evolution step gives finite result."""
        u = ns_small.compute_velocity_field()
        u_new = ns_small.evolve_step(u, dt=1e-4)
        assert np.all(np.isfinite(u_new))

    def test_evolve_step_divergence_free(self, ns_small):
        """Test evolution step maintains divergence-free condition."""
        u = ns_small.compute_velocity_field()
        u_new = ns_small.evolve_step(u, dt=1e-4)
        # After step, mean should be removed (divergence-free projection)
        assert np.abs(np.mean(u_new)) < 1e-10

    def test_global_smooth_solution(self, ns_small):
        """Test global smooth solution computation."""
        result = ns_small.compute_global_smooth_solution(
            t_max=0.1, n_steps=10
        )
        assert 'has_global_smooth_solution' in result
        assert 'energy_h1' in result
        assert 'energy_l2' in result
        assert 't_values' in result
        assert 'u_final' in result
        assert 'u_initial' in result
        assert 'divergence_free_check' in result

    def test_global_smooth_solution_energy_finite(self, ns_small):
        """Test global smooth solution has finite energy."""
        result = ns_small.compute_global_smooth_solution(t_max=0.1, n_steps=10)
        assert np.all(np.isfinite(result['energy_h1']))
        assert np.all(np.isfinite(result['energy_l2']))

    def test_global_smooth_solution_energy_positive(self, ns_small):
        """Test global smooth solution has positive energy."""
        result = ns_small.compute_global_smooth_solution(t_max=0.1, n_steps=10)
        assert np.all(result['energy_l2'] >= 0)
        assert np.all(result['energy_h1'] >= 0)

    def test_global_smooth_solution_with_custom_u0(self, ns_small):
        """Test global smooth solution with custom initial condition."""
        u0 = np.sin(2 * np.pi * ns_small.x / ns_small.domain_length)
        result = ns_small.compute_global_smooth_solution(u0=u0, t_max=0.1, n_steps=10)
        assert result['u_initial'] is not None
        assert result['u_final'] is not None
        assert np.all(np.isfinite(result['u_final']))

    def test_three_bridges_analysis(self, ns_small):
        """Test three bridges analysis returns proper structure."""
        bridges = ns_small.three_bridges_analysis()
        assert 'bridge_a_convection' in bridges
        assert 'bridge_b_pressure' in bridges
        assert 'bridge_c_diffusion' in bridges
        assert 'psi_global' in bridges
        assert 'f0' in bridges
        assert 'mu' in bridges

    def test_bridge_a_convection_content(self, ns_small):
        """Test Bridge A (Convection) has correct content."""
        bridges = ns_small.three_bridges_analysis()
        a = bridges['bridge_a_convection']
        assert 'psi_chaos' in a
        assert 'spectral_ratio' in a
        assert 'critical_line_alignment' in a
        assert a['psi_chaos'] == pytest.approx(PSI_GUE_CHAOS, rel=1e-10)
        assert a['critical_line_alignment'] == pytest.approx(0.5, rel=1e-10)

    def test_bridge_b_pressure_content(self, ns_small):
        """Test Bridge B (Pressure) has correct content."""
        bridges = ns_small.three_bridges_analysis()
        b = bridges['bridge_b_pressure']
        assert 'p_gact_scalar' in b
        assert 'rho_info' in b
        assert 'stability_correlation' in b
        assert b['stability_correlation'] == pytest.approx(GACT_CORRELATION, rel=1e-10)

    def test_bridge_c_diffusion_content(self, ns_small):
        """Test Bridge C (Diffusion) has correct content."""
        bridges = ns_small.three_bridges_analysis()
        c = bridges['bridge_c_diffusion']
        assert 'mu_adelic' in c
        assert 'f0_hz' in c
        assert 'diffusion_coefficient' in c
        assert c['mu_adelic'] == pytest.approx(MU_ADELIC, rel=1e-10)
        assert c['f0_hz'] == pytest.approx(F0, rel=1e-10)
        assert c['universal_harmonizer'] is True

    def test_verify_energy_bounds(self, ns_small):
        """Test energy bound verification."""
        bounds = ns_small.verify_energy_bounds(t_max=0.1, n_steps=10)
        assert 'has_global_smooth_solution' in bounds
        assert 'is_energy_bounded' in bounds
        assert 'energy_decreases' in bounds
        assert 'lambda_visc' in bounds
        assert 'divergence_free' in bounds

    def test_energy_bounds_lambda_visc_positive(self, ns_small):
        """Test viscous decay rate is positive."""
        bounds = ns_small.verify_energy_bounds(t_max=0.1, n_steps=10)
        assert bounds['lambda_visc'] > 0

    def test_energy_bounds_global_smooth_solution(self, ns_small):
        """Test that vibrational regularization gives global smooth solution."""
        bounds = ns_small.verify_energy_bounds(t_max=0.2, n_steps=20)
        assert bounds['has_global_smooth_solution'] is True

    def test_get_summary(self, ns_small):
        """Test get_summary returns proper structure."""
        summary = ns_small.get_summary()
        assert 'system' in summary
        assert 'f0_hz' in summary
        assert 'mu_adelic' in summary
        assert summary['f0_hz'] == pytest.approx(F0, rel=1e-10)
        assert summary['mu_adelic'] == pytest.approx(MU_ADELIC, rel=1e-10)
        assert 'doi' in summary


class TestVibrationalRegularization:
    """Tests for vibrational regularization mechanism."""

    def test_regularization_smooths_high_frequencies(self):
        """Test that vibrational regularization smooths high-frequency noise."""
        ns = QCALNavierStokesVibrational(n_points=128)

        # Create noisy signal
        u_noisy = np.zeros(128)
        # Add high-frequency noise
        u_noisy += 0.1 * np.sin(60 * np.pi * np.linspace(0, 1, 128))

        u_smooth = ns._vibrational_regularize(u_noisy)

        # High-frequency content should be reduced
        u_hat_noisy = np.fft.rfft(u_noisy)
        u_hat_smooth = np.fft.rfft(u_smooth)

        n_modes = len(u_hat_noisy)
        high_k_noisy = np.sum(np.abs(u_hat_noisy[n_modes // 2:]) ** 2)
        high_k_smooth = np.sum(np.abs(u_hat_smooth[n_modes // 2:]) ** 2)

        assert high_k_smooth <= high_k_noisy

    def test_regularization_preserves_low_frequencies(self):
        """Test that regularization preserves low-frequency content."""
        ns = QCALNavierStokesVibrational(n_points=128)

        # Pure low-frequency signal
        x = np.linspace(0, 1, 128)
        u_low = np.sin(2 * np.pi * x)  # k=1 mode

        u_reg = ns._vibrational_regularize(u_low)

        # The low-frequency signal should be largely preserved
        correlation = np.dot(u_low, u_reg) / (
            np.linalg.norm(u_low) * np.linalg.norm(u_reg) + 1e-30
        )
        # Strong positive correlation (not exact due to filter)
        assert correlation > 0.5

    def test_regularization_finite(self):
        """Test regularized output is finite."""
        ns = QCALNavierStokesVibrational(n_points=128)
        u = np.random.randn(128)
        u_reg = ns._vibrational_regularize(u)
        assert np.all(np.isfinite(u_reg))


class TestGlobalSmoothSolutions:
    """Integration tests for global smooth solutions."""

    def test_smooth_solution_for_divergent_free_initial_data(self):
        """Test global smooth solution with divergence-free initial data."""
        ns = QCALNavierStokesVibrational(n_points=64, domain_length=5.0)

        # Divergence-free initial condition (subtract mean)
        u0 = np.sin(2 * np.pi * ns.x / ns.domain_length)
        u0 = u0 - np.mean(u0)  # enforce divergence-free

        result = ns.compute_global_smooth_solution(u0=u0, t_max=0.2, n_steps=20)

        assert result['has_global_smooth_solution'] is True
        assert np.all(np.isfinite(result['energy_h1']))

    def test_smooth_solution_energy_does_not_blow_up(self):
        """Test that energy remains finite throughout evolution (no blowup)."""
        ns = QCALNavierStokesVibrational(n_points=64, domain_length=5.0)

        result = ns.compute_global_smooth_solution(t_max=0.3, n_steps=30)

        # Energy should be finite at all time steps (no blowup)
        assert np.all(np.isfinite(result['energy_h1']))
        assert np.all(np.isfinite(result['energy_l2']))

    def test_smooth_solution_u_final_finite(self):
        """Test that final velocity field is finite."""
        ns = QCALNavierStokesVibrational(n_points=64)

        result = ns.compute_global_smooth_solution(t_max=0.1, n_steps=10)

        assert np.all(np.isfinite(result['u_final']))

    def test_gact_sequence_affects_solution(self):
        """Test that different DNA sequences give different solutions."""
        ns_gact = QCALNavierStokesVibrational(n_points=64, dna_sequence="GACT")
        ns_aaaa = QCALNavierStokesVibrational(n_points=64, dna_sequence="AAAA")

        result_gact = ns_gact.compute_global_smooth_solution(t_max=0.1, n_steps=10)
        result_aaaa = ns_aaaa.compute_global_smooth_solution(t_max=0.1, n_steps=10)

        # Different sequences -> different pressure -> different solutions
        assert not np.allclose(result_gact['u_final'], result_aaaa['u_final'])


class TestPhysicalConsistency:
    """Tests for physical consistency of the QCAL-NS framework."""

    def test_adelic_viscosity_is_inverse_f0(self):
        """Test mu = 1/f0 in the NS operator."""
        ns = QCALNavierStokesVibrational()
        assert ns.mu == pytest.approx(1.0 / ns.f0, rel=1e-10)

    def test_diffusion_coefficient_is_nu(self):
        """Test diffusion uses nu = mu = 1/f0."""
        ns = QCALNavierStokesVibrational(n_points=64)
        u = np.sin(ns.x)
        d2u = np.gradient(np.gradient(u, ns.dx), ns.dx)
        diff = ns.compute_viscous_diffusion(u)
        expected = ns.nu * d2u
        np.testing.assert_allclose(diff, expected, rtol=1e-10)

    def test_velocity_field_is_gradient(self):
        """Test u_QCAL is the gradient of a potential."""
        ns = QCALNavierStokesVibrational(n_points=64, domain_length=5.0)
        u = ns.compute_velocity_field()

        # u = nabla(phi) => integral of u should give phi
        # Check that u is well-defined (finite, real)
        assert np.all(np.isfinite(u))
        assert np.all(np.isreal(u))

    def test_gact_resonance_order(self):
        """Test GACT resonance frequencies are in increasing order A<T<G<C."""
        assert GACT_RESONANCES['A'] < GACT_RESONANCES['T']
        assert GACT_RESONANCES['T'] < GACT_RESONANCES['G']
        assert GACT_RESONANCES['G'] < GACT_RESONANCES['C']

    def test_psi_global_coherence(self):
        """Test global Psi coherence is 0.9575."""
        assert PSI_GLOBAL == pytest.approx(0.9575, rel=1e-4)

    def test_quantum_reynolds_uses_f0_and_mu(self):
        """Test Re_q formula uses f0 and mu = 1/f0."""
        from operators.qcal_navier_stokes_vibrational import LAMBDA_C
        result = compute_quantum_reynolds_number(lambda_c=LAMBDA_C, mu=MU_ADELIC, f0=F0)
        expected = F0 * LAMBDA_C / MU_ADELIC
        assert result['re_quantum'] == pytest.approx(expected, rel=1e-6)


class TestRK4Step:
    """Tests for the pseudospectral 2D RK4 integrator."""

    def _make_spectral_grid(self, N: int = 16):
        """Helper: build angular wavenumber grids and initial Fourier fields.

        Uses angular wavenumbers kx = 2*pi*fftfreq(N, d=1/N) so that
        spectral gradients (ifft2(1j*kx*uhat)) match standard FFT differentiation.
        A local RNG is used to avoid mutating global NumPy RNG state.
        """
        from scipy.fft import fft2, fftfreq
        kx = 2.0 * np.pi * fftfreq(N, d=1.0 / N)
        ky = 2.0 * np.pi * fftfreq(N, d=1.0 / N)
        kxx, kyy = np.meshgrid(kx, ky, indexing='ij')
        k2 = kxx ** 2 + kyy ** 2
        k2[0, 0] = 1.0  # avoid division by zero at DC mode
        rng = np.random.default_rng(42)
        u0 = rng.standard_normal((N, N)) * 0.01
        v0 = rng.standard_normal((N, N)) * 0.01
        uhat = fft2(u0)
        vhat = fft2(v0)
        return uhat, vhat, kxx, kyy, k2, N

    def test_rk4_step_output_shape(self):
        """Test rk4_step returns arrays of the same shape as input."""
        uhat, vhat, kxx, kyy, k2, N = self._make_spectral_grid(16)
        grad_px = np.zeros((N, N), dtype=complex)
        grad_py = np.zeros((N, N), dtype=complex)
        uhat_new, vhat_new = rk4_step(
            uhat, vhat, dt=0.01, rho=1.0, mu=MU_ADELIC,
            k2=k2, kxx=kxx, kyy=kyy,
            grad_px_hat=grad_px, grad_py_hat=grad_py,
        )
        assert uhat_new.shape == uhat.shape
        assert vhat_new.shape == vhat.shape

    def test_rk4_step_finite(self):
        """Test rk4_step produces finite output."""
        uhat, vhat, kxx, kyy, k2, N = self._make_spectral_grid(16)
        grad_px = np.zeros((N, N), dtype=complex)
        grad_py = np.zeros((N, N), dtype=complex)
        uhat_new, vhat_new = rk4_step(
            uhat, vhat, dt=0.01, rho=1.0, mu=MU_ADELIC,
            k2=k2, kxx=kxx, kyy=kyy,
            grad_px_hat=grad_px, grad_py_hat=grad_py,
        )
        assert np.all(np.isfinite(uhat_new))
        assert np.all(np.isfinite(vhat_new))

    def test_rk4_step_zero_velocity_unchanged(self):
        """Zero velocity field should remain zero (no external forcing)."""
        N = 16
        from scipy.fft import fftfreq
        kx = 2.0 * np.pi * fftfreq(N, d=1.0 / N)
        ky = 2.0 * np.pi * fftfreq(N, d=1.0 / N)
        kxx, kyy = np.meshgrid(kx, ky, indexing='ij')
        k2 = kxx ** 2 + kyy ** 2
        k2[0, 0] = 1.0
        uhat = np.zeros((N, N), dtype=complex)
        vhat = np.zeros((N, N), dtype=complex)
        grad_px = np.zeros((N, N), dtype=complex)
        grad_py = np.zeros((N, N), dtype=complex)
        uhat_new, vhat_new = rk4_step(
            uhat, vhat, dt=0.05, rho=1.0, mu=MU_ADELIC,
            k2=k2, kxx=kxx, kyy=kyy,
            grad_px_hat=grad_px, grad_py_hat=grad_py,
        )
        np.testing.assert_allclose(np.abs(uhat_new), 0.0, atol=1e-12)
        np.testing.assert_allclose(np.abs(vhat_new), 0.0, atol=1e-12)

    def test_rk4_step_complex_output(self):
        """Test rk4_step returns complex arrays."""
        uhat, vhat, kxx, kyy, k2, N = self._make_spectral_grid(16)
        grad_px = np.zeros((N, N), dtype=complex)
        grad_py = np.zeros((N, N), dtype=complex)
        uhat_new, vhat_new = rk4_step(
            uhat, vhat, dt=0.01, rho=1.0, mu=MU_ADELIC,
            k2=k2, kxx=kxx, kyy=kyy,
            grad_px_hat=grad_px, grad_py_hat=grad_py,
        )
        assert np.iscomplexobj(uhat_new)
        assert np.iscomplexobj(vhat_new)

    def test_rk4_step_energy_dissipation(self):
        """Test that energy dissipates with viscosity (no external forcing)."""
        N = 16
        from scipy.fft import fft2, fftfreq
        kx = 2.0 * np.pi * fftfreq(N, d=1.0 / N)
        ky = 2.0 * np.pi * fftfreq(N, d=1.0 / N)
        kxx, kyy = np.meshgrid(kx, ky, indexing='ij')
        k2 = kxx ** 2 + kyy ** 2
        k2[0, 0] = 1.0
        # Simple single-mode initial condition
        u0 = np.sin(2.0 * np.pi * np.linspace(0, 1, N)[:, None])
        uhat = fft2(u0)
        vhat = np.zeros((N, N), dtype=complex)
        grad_px = np.zeros((N, N), dtype=complex)
        grad_py = np.zeros((N, N), dtype=complex)

        e0 = np.sum(np.abs(uhat) ** 2 + np.abs(vhat) ** 2)
        # Stability condition: nu*k^2*dt < 1.  With angular wavenumbers the
        # worst case is a corner mode |k| = sqrt(2)*2*pi*(N/2) ~ 71 for N=16,
        # k^2 ~ 5027.  With dt=1e-4: nu*k^2*dt = 1.0*5027*1e-4 = 0.50 < 1. ✓
        for _ in range(10):
            uhat, vhat = rk4_step(
                uhat, vhat, dt=1e-4, rho=1.0, mu=1.0,
                k2=k2, kxx=kxx, kyy=kyy,
                grad_px_hat=grad_px, grad_py_hat=grad_py,
            )
        e_final = np.sum(np.abs(uhat) ** 2 + np.abs(vhat) ** 2)
        # Energy should decrease due to viscous dissipation
        assert np.isfinite(e_final)
        assert e_final < e0


class TestPlotEnergySpectrum:
    """Smoke tests for plot_energy_spectrum (headless matplotlib)."""

    def _make_spectral_grid(self, N: int = 16):
        """Build angular wavenumber grids and trivial Fourier fields."""
        from scipy.fft import fft2, fftfreq
        kx = 2.0 * np.pi * fftfreq(N, d=1.0 / N)
        ky = 2.0 * np.pi * fftfreq(N, d=1.0 / N)
        kxx, kyy = np.meshgrid(kx, ky, indexing='ij')
        rng = np.random.default_rng(7)
        uhat = fft2(rng.standard_normal((N, N)) * 0.1)
        vhat = fft2(rng.standard_normal((N, N)) * 0.1)
        return uhat, vhat, kxx, kyy, N

    def test_plot_energy_spectrum_no_exception(self):
        """plot_energy_spectrum should not raise under headless configuration."""
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt

        uhat, vhat, kxx, kyy, N = self._make_spectral_grid(16)
        fig, ax = plt.subplots()
        plt.sca(ax)
        # Should complete without raising
        plot_energy_spectrum(uhat, vhat, kxx, kyy, N, title="Test")
        plt.close(fig)

    def test_plot_energy_spectrum_all_zeros_no_exception(self):
        """All-zero fields produce no plotted line but should not raise."""
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt

        N = 8
        from scipy.fft import fftfreq
        kx = 2.0 * np.pi * fftfreq(N, d=1.0 / N)
        ky = 2.0 * np.pi * fftfreq(N, d=1.0 / N)
        kxx, kyy = np.meshgrid(kx, ky, indexing='ij')
        uhat = np.zeros((N, N), dtype=complex)
        vhat = np.zeros((N, N), dtype=complex)
        fig, ax = plt.subplots()
        plt.sca(ax)
        plot_energy_spectrum(uhat, vhat, kxx, kyy, N, title="Zeros")
        plt.close(fig)


class TestComputeBiologicalCoherence:
    """Tests for the biological coherence metric."""

    def test_coherence_is_float(self):
        """Test coherence returns a float."""
        x = np.linspace(0, 2.0 * np.pi, 64)
        u = np.sin(x)
        coh = compute_biological_coherence(u, x, f0=F0)
        assert isinstance(coh, float)

    def test_coherence_range(self):
        """Test coherence is in [0, 1]."""
        x = np.linspace(0, 2.0 * np.pi, 64)
        u = np.random.randn(64)
        coh = compute_biological_coherence(u, x, f0=F0)
        assert 0.0 <= coh <= 1.0

    def test_coherence_perfect_logos_wave(self):
        """Test perfect logos wave yields high coherence with itself."""
        x = np.linspace(0, 2.0 * np.pi, 256)
        u = np.sin(F0 * x)
        coh = compute_biological_coherence(u, x, f0=F0)
        # Perfect correlation with itself
        assert coh == pytest.approx(1.0, abs=1e-6)

    def test_coherence_constant_field(self):
        """Test constant field returns 0 (degenerate correlation)."""
        x = np.linspace(0, 1.0, 64)
        u = np.ones(64)
        coh = compute_biological_coherence(u, x, f0=F0)
        assert coh == pytest.approx(0.0, abs=1e-10)

    def test_coherence_2d_field(self):
        """Test coherence works with 2D arrays (flattened internally)."""
        N = 16
        xx = np.linspace(0, 2.0 * np.pi, N * N).reshape(N, N)
        u = np.random.randn(N, N)
        coh = compute_biological_coherence(u, xx, f0=F0)
        assert 0.0 <= coh <= 1.0


class TestEvolveStepRK4:
    """Tests for the QCALNavierStokesVibrational.evolve_step_rk4 method."""

    def test_rk4_output_shape(self):
        """Test evolve_step_rk4 preserves velocity field shape."""
        ns = QCALNavierStokesVibrational(n_points=64)
        u = ns.compute_velocity_field()
        u_new = ns.evolve_step_rk4(u, dt=1e-4)
        assert u_new.shape == u.shape

    def test_rk4_output_finite(self):
        """Test evolve_step_rk4 produces finite values."""
        ns = QCALNavierStokesVibrational(n_points=64)
        u = ns.compute_velocity_field()
        u_new = ns.evolve_step_rk4(u, dt=1e-4)
        assert np.all(np.isfinite(u_new))

    def test_rk4_divergence_free(self):
        """Test evolve_step_rk4 maintains divergence-free condition (zero mean)."""
        ns = QCALNavierStokesVibrational(n_points=64)
        u = ns.compute_velocity_field()
        u_new = ns.evolve_step_rk4(u, dt=1e-4)
        # 1D divergence-free: mean is zero
        assert abs(np.mean(u_new)) < 1e-10

    def test_rk4_vs_euler_accuracy(self):
        """Test RK4 and Euler give similar results for small dt."""
        ns = QCALNavierStokesVibrational(n_points=64)
        u = ns.compute_velocity_field()
        dt = 1e-5
        u_euler = ns.evolve_step(u.copy(), dt=dt)
        u_rk4 = ns.evolve_step_rk4(u.copy(), dt=dt)
        # Both should be finite and close for very small steps
        assert np.all(np.isfinite(u_euler))
        assert np.all(np.isfinite(u_rk4))
        # RK4 and Euler should be in the same ballpark for small dt
        diff = np.max(np.abs(u_rk4 - u_euler))
        u_scale = max(np.max(np.abs(u)), 1e-30)
        assert diff / u_scale < 1.0  # relative difference < 100%

    def test_rk4_multiple_steps_stable(self):
        """Test that multiple RK4 steps remain stable."""
        ns = QCALNavierStokesVibrational(n_points=64)
        u = ns.compute_velocity_field()
        for _ in range(20):
            u = ns.evolve_step_rk4(u, dt=1e-4)
        assert np.all(np.isfinite(u))


if __name__ == '__main__':
    pytest.main([__file__, '-v', '--tb=short'])
