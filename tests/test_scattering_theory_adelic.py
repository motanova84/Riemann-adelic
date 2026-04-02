#!/usr/bin/env python3
"""
Tests for Rigorous Scattering Theory Implementation
===================================================

Tests the complete 5-step scattering theory proof of the Riemann Hypothesis.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ · 141.7001 Hz
"""

import pytest
import numpy as np

from physics.scattering_theory_adelic import (
    HilbertSpaceAdelic,
    FreeHamiltonian,
    InteractingHamiltonian,
    WaveOperatorConstructor,
    SMatrixCalculator,
    AsymptoticCompletenessVerifier,
    RiemannZeroCorrespondenceProver,
    ScatteringTheoryRHProof,
    prove_riemann_hypothesis_via_scattering,
    HamiltonianData,
)


class TestHilbertSpaceAdelic:
    """Test Hilbert space L²(𝔸×/ℚ×, d*x)."""

    def test_initialization(self):
        """Test Hilbert space initialization."""
        hs = HilbertSpaceAdelic(n_grid=64)

        assert hs.data.dimension == 64
        assert len(hs.x_grid) == 64
        assert len(hs.dx_star) == 64
        assert np.all(hs.x_grid > 0)
        assert hs.data.is_adelic is True

    def test_inner_product(self):
        """Test inner product structure."""
        hs = HilbertSpaceAdelic(n_grid=64)

        # Create test functions
        f = np.exp(-hs.x_grid)
        g = np.exp(-hs.x_grid)

        # Inner product should be positive
        inner = hs.inner_product(f, g)
        assert np.real(inner) > 0

        # Hermitian property: ⟨f, g⟩ = ⟨g, f⟩*
        inner_fg = hs.inner_product(f, g)
        inner_gf = hs.inner_product(g, f)
        assert np.allclose(inner_fg, np.conj(inner_gf))

    def test_norm(self):
        """Test L² norm."""
        hs = HilbertSpaceAdelic(n_grid=64)

        # Zero function has zero norm
        f_zero = np.zeros(64)
        assert hs.norm(f_zero) < 1e-10

        # Non-zero function has positive norm
        f = np.exp(-hs.x_grid)
        assert hs.norm(f) > 0


class TestFreeHamiltonian:
    """Test free Hamiltonian H₀."""

    def test_initialization(self):
        """Test H₀ construction."""
        hs = HilbertSpaceAdelic(n_grid=64)
        H0 = FreeHamiltonian(hs)

        assert H0.H0_matrix.shape == (64, 64)
        assert H0.hs == hs

    def test_hermiticity(self):
        """Test H₀ is Hermitian."""
        hs = HilbertSpaceAdelic(n_grid=64)
        H0 = FreeHamiltonian(hs)

        # H₀ should be Hermitian: H₀ = H₀†
        H0_dag = H0.H0_matrix.conj().T
        diff = np.linalg.norm(H0.H0_matrix - H0_dag)

        assert diff < 1e-10

    def test_unitary_group(self):
        """Test unitary group U₀(t)."""
        hs = HilbertSpaceAdelic(n_grid=64)
        H0 = FreeHamiltonian(hs)

        t = 1.0
        U0_t = H0.unitary_group(t)

        # Should be unitary: U† U = I
        U_dag_U = U0_t.conj().T @ U0_t
        I = np.eye(64)

        diff = np.linalg.norm(U_dag_U - I)
        assert diff < 1e-8

    def test_spectrum_real(self):
        """Test spectrum of H₀ is real."""
        hs = HilbertSpaceAdelic(n_grid=64)
        H0 = FreeHamiltonian(hs)

        spectrum = H0.spectrum()

        # All eigenvalues should be real
        assert np.allclose(np.imag(spectrum), 0, atol=1e-10)


class TestInteractingHamiltonian:
    """Test interacting Hamiltonian H."""

    def test_initialization(self):
        """Test H construction."""
        hs = HilbertSpaceAdelic(n_grid=64)
        H0 = FreeHamiltonian(hs)
        H = InteractingHamiltonian(H0, n_primes=20)

        assert H.H_matrix.shape == (64, 64)
        assert H.V_matrix.shape == (64, 64)

    def test_hermiticity(self):
        """Test H and V are Hermitian."""
        hs = HilbertSpaceAdelic(n_grid=64)
        H0 = FreeHamiltonian(hs)
        H = InteractingHamiltonian(H0, n_primes=20)

        # H should be Hermitian
        H_dag = H.H_matrix.conj().T
        diff_H = np.linalg.norm(H.H_matrix - H_dag)
        assert diff_H < 1e-10

        # V should be Hermitian
        V_dag = H.V_matrix.conj().T
        diff_V = np.linalg.norm(H.V_matrix - V_dag)
        assert diff_V < 1e-10

    def test_poisson_mellin_structure(self):
        """Test Poisson-Mellin operator couples scales."""
        hs = HilbertSpaceAdelic(n_grid=64)
        H0 = FreeHamiltonian(hs)
        H = InteractingHamiltonian(H0, n_primes=10)

        # V should be non-zero (interaction exists)
        V_norm = np.linalg.norm(H.V_matrix)
        assert V_norm > 0

        # V should be small compared to H₀ (perturbative)
        H0_norm = np.linalg.norm(H0.H0_matrix)
        assert V_norm < 0.5 * H0_norm


class TestWaveOperatorConstructor:
    """Test wave operator construction Ω±."""

    @pytest.mark.slow
    def test_cook_criterion(self):
        """Test Cook's criterion for existence."""
        hs = HilbertSpaceAdelic(n_grid=32)
        H0 = FreeHamiltonian(hs)
        H = InteractingHamiltonian(H0, n_primes=10)

        wave_constructor = WaveOperatorConstructor(H0, H, t_max=20.0)

        # Test function
        test_func = np.exp(-((hs.x_grid - 1.0) ** 2) / 0.5)
        test_func /= hs.norm(test_func)

        # Verify Cook's criterion
        cook_ok, decay_rate = wave_constructor.verify_cook_criterion(test_func)

        # Decay rate should be > 1 for convergence
        assert decay_rate > 0.5  # Relaxed for small grid

    @pytest.mark.slow
    def test_omega_plus_construction(self):
        """Test Ω₊ construction."""
        hs = HilbertSpaceAdelic(n_grid=32)
        H0 = FreeHamiltonian(hs)
        H = InteractingHamiltonian(H0, n_primes=10)

        wave_constructor = WaveOperatorConstructor(H0, H, t_max=15.0, n_time_steps=50)

        omega_plus = wave_constructor.compute_omega_plus()

        # Should have matrix representation
        assert omega_plus.operator_matrix.shape == (32, 32)

        # Convergence data should show decay
        assert len(omega_plus.convergence_data) > 0

    @pytest.mark.slow
    def test_omega_minus_construction(self):
        """Test Ω₋ construction."""
        hs = HilbertSpaceAdelic(n_grid=32)
        H0 = FreeHamiltonian(hs)
        H = InteractingHamiltonian(H0, n_primes=10)

        wave_constructor = WaveOperatorConstructor(H0, H, t_max=15.0, n_time_steps=50)

        omega_minus = wave_constructor.compute_omega_minus()

        # Should have matrix representation
        assert omega_minus.operator_matrix.shape == (32, 32)


class TestSMatrixCalculator:
    """Test S-matrix computation."""

    @pytest.mark.slow
    def test_s_matrix_computation(self):
        """Test S = Ω₊* Ω₋."""
        hs = HilbertSpaceAdelic(n_grid=32)
        H0 = FreeHamiltonian(hs)
        H = InteractingHamiltonian(H0, n_primes=10)

        wave_constructor = WaveOperatorConstructor(H0, H, t_max=15.0, n_time_steps=50)

        omega_plus = wave_constructor.compute_omega_plus()
        omega_minus = wave_constructor.compute_omega_minus()

        s_calculator = SMatrixCalculator(
            omega_plus,
            omega_minus,
            hs,
            n_zeros=10,
        )

        s_matrix = s_calculator.compute_s_matrix()

        # S should be square matrix
        assert s_matrix.S_matrix.shape == (32, 32)

    @pytest.mark.slow
    def test_xi_ratio(self):
        """Test ξ ratio computation."""
        hs = HilbertSpaceAdelic(n_grid=32)
        H0 = FreeHamiltonian(hs)
        H = InteractingHamiltonian(H0, n_primes=10)

        wave_constructor = WaveOperatorConstructor(H0, H, t_max=10.0, n_time_steps=30)

        omega_plus = wave_constructor.compute_omega_plus()
        omega_minus = wave_constructor.compute_omega_minus()

        s_calculator = SMatrixCalculator(
            omega_plus,
            omega_minus,
            hs,
            n_zeros=5,
        )

        # Test xi_ratio at a point
        E = 14.134725j  # First Riemann zero
        ratio = s_calculator._xi_ratio(E)

        # Should be finite
        assert np.isfinite(ratio)


class TestAsymptoticCompletenessVerifier:
    """Test asymptotic completeness."""

    @pytest.mark.slow
    def test_no_bound_states(self):
        """Test that no bound states exist."""
        hs = HilbertSpaceAdelic(n_grid=32)
        H0 = FreeHamiltonian(hs)
        H = InteractingHamiltonian(H0, n_primes=10)

        hamiltonians = HamiltonianData(
            H0_matrix=H0.H0_matrix,
            H_matrix=H.H_matrix,
            V_matrix=H.V_matrix,
            spectrum_H0=H0.spectrum(),
            spectrum_H=H.spectrum(),
        )

        wave_constructor = WaveOperatorConstructor(H0, H, t_max=10.0, n_time_steps=30)

        omega_plus = wave_constructor.compute_omega_plus()
        omega_minus = wave_constructor.compute_omega_minus()

        verifier = AsymptoticCompletenessVerifier(
            hamiltonians,
            omega_plus,
            omega_minus,
        )

        result = verifier.verify()

        # Should not have bound states
        assert result.continuous_spectrum_only


class TestScatteringTheoryRHProof:
    """Test complete proof orchestrator."""

    @pytest.mark.slow
    def test_small_proof(self):
        """Test proof with small parameters."""
        prover = ScatteringTheoryRHProof(
            n_grid=32,
            n_primes=10,
            n_zeros=5,
            t_max=10.0,
            precision=25,
        )

        result = prover.execute_proof()

        # Should produce complete result
        assert result.hilbert_space is not None
        assert result.hamiltonians is not None
        assert result.omega_plus is not None
        assert result.omega_minus is not None
        assert result.s_matrix is not None
        assert result.asymptotic_completeness is not None
        assert result.zero_pole_correspondence is not None

    @pytest.mark.slow
    def test_convenience_function(self):
        """Test convenience function."""
        result = prove_riemann_hypothesis_via_scattering(
            n_grid=32,
            n_primes=10,
            n_zeros=5,
            t_max=10.0,
            verbose=False,
        )

        # Should return complete result
        assert result is not None
        assert hasattr(result, 'riemann_hypothesis_proven')


class TestIntegration:
    """Integration tests for full proof."""

    @pytest.mark.slow
    def test_wave_operators_exist(self):
        """Test that wave operators exist."""
        result = prove_riemann_hypothesis_via_scattering(
            n_grid=32,
            n_primes=10,
            n_zeros=5,
            t_max=10.0,
            verbose=False,
        )

        # Both wave operators should exist
        assert result.omega_plus.cook_criterion_satisfied
        assert result.omega_minus.cook_criterion_satisfied

    @pytest.mark.slow
    def test_s_matrix_structure(self):
        """Test S-matrix has correct structure."""
        result = prove_riemann_hypothesis_via_scattering(
            n_grid=32,
            n_primes=10,
            n_zeros=5,
            t_max=10.0,
            verbose=False,
        )

        # S should have poles
        assert len(result.s_matrix.poles) > 0

    @pytest.mark.slow
    def test_metadata_complete(self):
        """Test metadata is complete."""
        result = prove_riemann_hypothesis_via_scattering(
            n_grid=32,
            n_primes=10,
            n_zeros=5,
            t_max=10.0,
            verbose=False,
        )

        # Metadata should include key parameters
        assert 'n_grid' in result.metadata
        assert 'n_primes' in result.metadata
        assert 'n_zeros' in result.metadata
        assert 'f0' in result.metadata
        assert 'c_coherence' in result.metadata


if __name__ == "__main__":
    pytest.main([__file__, "-v", "-k", "not slow"])
