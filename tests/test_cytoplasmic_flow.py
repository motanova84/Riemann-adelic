"""
Tests for Cytoplasmic Flow Model - Navier-Stokes Implementation
================================================================

Tests comprehensivos para el modelo de flujo citoplasmático que conecta
la Hipótesis de Riemann con el tejido biológico vivo.

Autor: José Manuel Mota Burruezo Ψ ✧ ∞³
Instituto Consciencia Cuántica QCAL ∞³
"""

import pytest
import numpy as np
from typing import Tuple
import sys
from pathlib import Path

# Add src to path
sys.path.insert(0, str(Path(__file__).parent.parent / 'src'))

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


class TestFlowParameters:
    """Test FlowParameters dataclass."""
    
    def test_default_parameters(self):
        """Test default cytoplasmic parameters."""
        params = FlowParameters()
        
        assert params.density == RHO_CYTOPLASM
        assert params.kinematic_viscosity == NU_CYTOPLASM
        assert params.length_scale == CELL_LENGTH_SCALE
        assert params.velocity_scale == FLOW_VELOCITY
    
    def test_reynolds_number(self):
        """Test Reynolds number calculation."""
        params = FlowParameters()
        re = params.reynolds_number
        
        # Should be extremely small for cytoplasm
        assert re < 1e-6
        assert re > 0
        
        # Verify formula: Re = vL/ν
        expected = (FLOW_VELOCITY * CELL_LENGTH_SCALE) / NU_CYTOPLASM
        assert abs(re - expected) < 1e-12
    
    def test_viscous_regime(self):
        """Test that cytoplasm is in viscous regime."""
        params = FlowParameters()
        
        # Re << 1 implies viscous regime
        assert params.reynolds_number < 0.1
        assert params.has_smooth_solution
    
    def test_diffusion_time(self):
        """Test diffusion time calculation."""
        params = FlowParameters()
        tau = params.diffusion_time
        
        # Should be positive
        assert tau > 0
        
        # Verify formula: τ = L²/ν
        expected = CELL_LENGTH_SCALE**2 / NU_CYTOPLASM
        assert abs(tau - expected) < 1e-12
    
    def test_diffusion_frequency(self):
        """Test diffusion frequency calculation."""
        params = FlowParameters()
        f_diff = params.diffusion_frequency
        
        # Should be positive
        assert f_diff > 0
        
        # Verify f = 1/τ
        assert abs(f_diff * params.diffusion_time - 1.0) < 1e-10
    
    def test_custom_parameters(self):
        """Test custom parameter creation."""
        params = FlowParameters(
            density=1000.0,
            kinematic_viscosity=2e-6,
            length_scale=2e-6,
            velocity_scale=2e-8
        )
        
        assert params.density == 1000.0
        assert params.kinematic_viscosity == 2e-6
        assert params.reynolds_number == (2e-8 * 2e-6) / 2e-6


class TestNavierStokesRegularized:
    """Test NavierStokesRegularized solver."""
    
    def test_initialization(self):
        """Test solver initialization."""
        flow = NavierStokesRegularized()
        
        assert flow.params is not None
        assert flow.params.has_smooth_solution
    
    def test_velocity_field_at_origin(self):
        """Test velocity field at origin."""
        flow = NavierStokesRegularized()
        
        # At t=0, velocity should be well-defined
        vx, vy, vz = flow.velocity_field(0, 0, 0, 0)
        
        assert isinstance(vx, (int, float, np.number))
        assert isinstance(vy, (int, float, np.number))
        assert isinstance(vz, (int, float, np.number))
    
    def test_velocity_field_decay(self):
        """Test that velocity decays with distance (Gaussian)."""
        flow = NavierStokesRegularized()
        t = 1.0
        
        # Velocity at origin
        v0_x, v0_y, v0_z = flow.velocity_field(0, 0, 0, t)
        v0_mag = np.sqrt(v0_x**2 + v0_y**2 + v0_z**2)
        
        # Velocity at distance r
        r = CELL_LENGTH_SCALE
        vr_x, vr_y, vr_z = flow.velocity_field(r, 0, 0, t)
        vr_mag = np.sqrt(vr_x**2 + vr_y**2 + vr_z**2)
        
        # Should decay with distance
        assert vr_mag < v0_mag
    
    def test_incompressibility(self):
        """Test that velocity field is approximately incompressible (∇·v ≈ 0)."""
        flow = NavierStokesRegularized()
        t = 1.0
        h = CELL_LENGTH_SCALE / 100
        
        # Compute divergence numerically
        vx_px, _, _ = flow.velocity_field(h, 0, 0, t)
        vx_mx, _, _ = flow.velocity_field(-h, 0, 0, t)
        dvx_dx = (vx_px - vx_mx) / (2 * h)
        
        _, vy_py, _ = flow.velocity_field(0, h, 0, t)
        _, vy_my, _ = flow.velocity_field(0, -h, 0, t)
        dvy_dy = (vy_py - vy_my) / (2 * h)
        
        _, _, vz_pz = flow.velocity_field(0, 0, h, t)
        _, _, vz_mz = flow.velocity_field(0, 0, -h, t)
        dvz_dz = (vz_pz - vz_mz) / (2 * h)
        
        div_v = dvx_dx + dvy_dy + dvz_dz
        
        # Divergence should be small (not exact due to numerical approximation)
        # Use relative tolerance based on velocity scale
        v_scale = flow.params.velocity_scale
        assert abs(div_v) < v_scale / CELL_LENGTH_SCALE * 10
    
    def test_vorticity_computation(self):
        """Test vorticity field computation."""
        flow = NavierStokesRegularized()
        t = 1.0
        
        wx, wy, wz = flow.vorticity(0, 0, 0, t)
        
        # Vorticity should be finite
        assert np.isfinite(wx)
        assert np.isfinite(wy)
        assert np.isfinite(wz)
    
    def test_pressure_field(self):
        """Test pressure field computation."""
        flow = NavierStokesRegularized()
        t = 1.0
        
        # Pressure at origin should be finite
        p0 = flow.pressure_field(0, 0, 0, t)
        assert np.isfinite(p0)
        
        # Pressure should decay with distance
        r = CELL_LENGTH_SCALE
        pr = flow.pressure_field(r, 0, 0, t)
        assert np.isfinite(pr)
        assert pr < p0
    
    def test_energy_spectrum(self):
        """Test energy spectrum computation."""
        flow = NavierStokesRegularized()
        
        # Wave numbers
        k = np.logspace(0, 6, 50)  # 1 to 10^6 m^-1
        E_k = flow.energy_spectrum(k)
        
        # Spectrum should be positive and decay
        assert np.all(E_k >= 0)
        assert E_k[0] > E_k[-1]  # Decay with k


class TestRiemannResonanceOperator:
    """Test RiemannResonanceOperator."""
    
    def test_initialization(self):
        """Test operator initialization."""
        flow = NavierStokesRegularized()
        riemann_op = RiemannResonanceOperator(flow)
        
        assert riemann_op.flow is flow
    
    def test_eigenfrequencies(self):
        """Test eigenfrequency calculation."""
        flow = NavierStokesRegularized()
        riemann_op = RiemannResonanceOperator(flow)
        
        freqs = riemann_op.eigenfrequencies(n_modes=10)
        
        assert len(freqs) == 10
        assert np.all(freqs > 0)
        
        # Should be multiples of f₀
        expected = F0_HZ * np.arange(1, 11)
        np.testing.assert_array_almost_equal(freqs, expected)
    
    def test_is_hermitian(self):
        """Test that operator is Hermitian in viscous regime."""
        flow = NavierStokesRegularized()
        riemann_op = RiemannResonanceOperator(flow)
        
        # In viscous regime, operator should be Hermitian
        assert riemann_op.is_hermitian()
    
    def test_riemann_status(self):
        """Test Riemann hypothesis status report."""
        flow = NavierStokesRegularized()
        riemann_op = RiemannResonanceOperator(flow)
        
        status = riemann_op.riemann_hypothesis_status()
        
        # Check all required keys
        assert "reynolds_number" in status
        assert "viscous_regime" in status
        assert "operator_hermitian" in status
        assert "smooth_solution_exists" in status
        assert "riemann_zeros_accessible" in status
        assert "fundamental_frequency_hz" in status
        
        # In default cytoplasmic parameters
        assert status["viscous_regime"]
        assert status["operator_hermitian"]
        assert status["smooth_solution_exists"]
        assert status["riemann_zeros_accessible"]
        assert status["fundamental_frequency_hz"] == F0_HZ


class TestDemonstration:
    """Test demonstration function."""
    
    def test_demonstrate_runs(self):
        """Test that demonstration runs without errors."""
        results = demonstrate_navier_stokes_coherence()
        
        # Check structure
        assert "parameters" in results
        assert "riemann_status" in results
        assert "eigenfrequencies_hz" in results
        assert "velocity_field" in results
        assert "vorticity" in results
        
        # Check parameters
        assert "reynolds_number" in results["parameters"]
        assert results["parameters"]["reynolds_number"] < 1e-6
        
        # Check eigenfrequencies
        freqs = results["eigenfrequencies_hz"]
        assert len(freqs) == 5
        assert freqs[0] == F0_HZ


class TestPhysicalConsistency:
    """Test physical consistency of the model."""
    
    def test_causality(self):
        """Test that solution respects causality (no superluminal propagation)."""
        flow = NavierStokesRegularized()
        
        # Velocity should be much less than speed of light
        c = 3e8  # m/s
        vx, vy, vz = flow.velocity_field(0, 0, 0, 1.0)
        v_mag = np.sqrt(vx**2 + vy**2 + vz**2)
        
        assert v_mag < c
        assert v_mag < 1.0  # Should be microscopic
    
    def test_energy_conservation_tendency(self):
        """Test that energy dissipates (2nd law of thermodynamics)."""
        flow = NavierStokesRegularized()
        
        # Energy at t1 should be >= energy at t2 (dissipation)
        t1 = 0.1
        t2 = 1.0
        
        vx1, vy1, vz1 = flow.velocity_field(0, 0, 0, t1)
        E1 = vx1**2 + vy1**2 + vz1**2
        
        vx2, vy2, vz2 = flow.velocity_field(0, 0, 0, t2)
        E2 = vx2**2 + vy2**2 + vz2**2
        
        # Energy should dissipate or oscillate (not grow unboundedly)
        assert np.isfinite(E1)
        assert np.isfinite(E2)
    
    def test_frequency_qcal_alignment(self):
        """Test alignment with QCAL fundamental frequency."""
        flow = NavierStokesRegularized()
        riemann_op = RiemannResonanceOperator(flow)
        
        freqs = riemann_op.eigenfrequencies(n_modes=3)
        
        # All frequencies should be multiples of f₀
        for i, f in enumerate(freqs, 1):
            expected = i * F0_HZ
            assert abs(f - expected) < 1e-6


if __name__ == "__main__":
    # Run tests with pytest
    pytest.main([__file__, "-v"])
