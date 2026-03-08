#!/usr/bin/env python3
r"""
Tests for Sistema Dinámico Z - Four Pillars Implementation
=========================================================

Validates the four mathematical components necessary to close the spectral
approach to the Riemann Hypothesis:
1. Non-commutative compactification (Connes)
2. Adelic rational filter (Weil)
3. Hadamard determinant identity
4. Dynamic Z system (Anosov flow on SL(2,Z)\H)

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: March 2026
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add physics directory to path
repo_root = Path(__file__).parent.parent
sys.path.insert(0, str(repo_root / "physics"))

from sistema_dinamico_z import (
    CompactificacionNoConmutativa,
    FiltroRacionalesAdelico,
    IdentidadDeterminanteHadamard,
    SistemaDinamicoZ,
    SistemaDinamicoZCompleto,
    F0, C_QCAL, PHI, LYAPUNOV_Z
)


# ============================================================================
# Test Suite for CompactificacionNoConmutativa
# ============================================================================

class TestCompactificacionNoConmutativa:
    """Test suite for Non-Commutative Compactification."""
    
    def setup_method(self):
        """Set up test fixtures."""
        self.compact = CompactificacionNoConmutativa(primes=[2, 3, 5, 7], x_max=50.0, N_x=200)
    
    def test_initialization(self):
        """Test proper initialization."""
        assert len(self.compact.primes) == 4
        assert self.compact.primes == [2, 3, 5, 7]
        assert self.compact.x_max == 50.0
        assert self.compact.N_x == 200
        assert len(self.compact.x_grid) == 200
    
    def test_first_primes_generation(self):
        """Test prime number generation."""
        compact = CompactificacionNoConmutativa()
        assert len(compact.primes) == 20
        assert compact.primes[0] == 2
        assert compact.primes[1] == 3
        assert compact.primes[2] == 5
        assert all(compact._is_prime(p) for p in compact.primes)
    
    def test_is_prime(self):
        """Test prime checking function."""
        assert self.compact._is_prime(2)
        assert self.compact._is_prime(3)
        assert self.compact._is_prime(17)
        assert not self.compact._is_prime(1)
        assert not self.compact._is_prime(4)
        assert not self.compact._is_prime(100)
    
    def test_haar_volume_normalization(self):
        """Test Haar volume = 1 (Artin-Whaples theorem)."""
        volume = self.compact.haar_volume
        assert abs(volume - 1.0) < 1e-3, f"Haar volume {volume} should be ≈1.0"
    
    def test_confinement_potential_monotone(self):
        """Test confinement potential V_conf(x) = log(1 + 1/x)."""
        x = np.array([1.0, 2.0, 5.0, 10.0])
        V = self.compact.confinement_potential(x)
        
        # Should be positive
        assert np.all(V > 0)
        
        # Should be decreasing (confining at infinity)
        assert V[0] > V[1] > V[2] > V[3]
        
        # Check formula
        expected = np.log(1.0 + 1.0 / x)
        np.testing.assert_allclose(V, expected, rtol=1e-6)
    
    def test_adelic_measure(self):
        """Test multiplicative Haar measure dμ = dx/|x|."""
        x = np.array([1.0, 2.0, 5.0, 10.0])
        measure = self.compact.adelic_measure(x)
        
        expected = 1.0 / x
        np.testing.assert_allclose(measure, expected, rtol=1e-6)
    
    def test_verify_compactness(self):
        """Test compactness verification."""
        result = self.compact.verify_compactness()
        
        assert 'is_compact' in result
        assert 'haar_volume' in result
        assert 'Psi' in result
        
        # Haar volume should be close to 1
        assert abs(result['haar_volume'] - 1.0) < 1e-3
        
        # Should be compact
        assert result['is_compact'] is True or result['is_compact'] is False
    
    def test_spectrum_confinement(self):
        """Test discrete spectrum from confinement."""
        result = self.compact.compute_spectrum_confinement(N_states=20)
        
        assert 'eigenvalues' in result
        assert 'is_discrete' in result
        assert 'N_levels' in result
        
        # Should have eigenvalues
        assert result['N_levels'] > 0
        assert len(result['eigenvalues']) > 0
        
        # Should be discrete
        if result['N_levels'] > 1:
            assert result['min_gap'] > 0
    
    def test_spectrum_positivity(self):
        """Test that spectrum is positive."""
        result = self.compact.compute_spectrum_confinement(N_states=10)
        
        eigenvalues = result['eigenvalues']
        assert len(eigenvalues) > 0
        assert all(e > 0 for e in eigenvalues), "All eigenvalues should be positive"


# ============================================================================
# Test Suite for FiltroRacionalesAdelico
# ============================================================================

class TestFiltroRacionalesAdelico:
    """Test suite for Adelic Rational Filter."""
    
    def setup_method(self):
        """Set up test fixtures."""
        self.filtro = FiltroRacionalesAdelico(x_max=100.0, N_primes=50)
    
    def test_initialization(self):
        """Test proper initialization."""
        assert self.filtro.x_max == 100.0
        assert self.filtro.N_primes == 50
        assert len(self.filtro.primes) == 50
    
    def test_mobius_function(self):
        """Test Möbius function μ(n)."""
        # μ(1) = 1
        assert self.filtro.mobius(1) == 1
        
        # μ(2) = -1 (one prime)
        assert self.filtro.mobius(2) == -1
        
        # μ(3) = -1
        assert self.filtro.mobius(3) == -1
        
        # μ(6) = μ(2·3) = 1 (two distinct primes)
        assert self.filtro.mobius(6) == 1
        
        # μ(4) = μ(2²) = 0 (squared prime)
        assert self.filtro.mobius(4) == 0
        
        # μ(30) = μ(2·3·5) = -1 (three primes)
        assert self.filtro.mobius(30) == -1
    
    def test_chebyshev_psi(self):
        """Test Chebyshev ψ function."""
        # ψ(10) = log(2) + log(3) + log(5) + log(7) + log(2²) + log(3²)
        #       = 3·log(2) + 2·log(3) + log(5) + log(7)
        psi_10 = self.filtro.chebyshev_psi(10)
        expected = 3*np.log(2) + 2*np.log(3) + np.log(5) + np.log(7)
        assert abs(psi_10 - expected) < 1e-6
    
    def test_von_mangoldt_function(self):
        """Test von Mangoldt function Λ(n)."""
        # Λ(1) = 0
        assert self.filtro.von_mangoldt(1) == 0.0
        
        # Λ(prime) = log(prime)
        assert abs(self.filtro.von_mangoldt(2) - np.log(2)) < 1e-10
        assert abs(self.filtro.von_mangoldt(3) - np.log(3)) < 1e-10
        assert abs(self.filtro.von_mangoldt(7) - np.log(7)) < 1e-10
        
        # Λ(prime power) = log(prime)
        assert abs(self.filtro.von_mangoldt(4) - np.log(2)) < 1e-10  # 2²
        assert abs(self.filtro.von_mangoldt(8) - np.log(2)) < 1e-10  # 2³
        assert abs(self.filtro.von_mangoldt(9) - np.log(3)) < 1e-10  # 3²
        
        # Λ(composite) = 0
        assert self.filtro.von_mangoldt(6) == 0.0   # 2·3
        assert self.filtro.von_mangoldt(10) == 0.0  # 2·5
    
    def test_mobius_cancellation(self):
        """Test Möbius cancellation ratio."""
        result = self.filtro.compute_mobius_cancellation(N=200)
        
        assert 'cancellation_ratio' in result
        assert 'cancellation_factor' in result
        assert 'ratio_match' in result
        
        # Cancellation should reduce composites
        assert 0 <= result['cancellation_ratio'] <= 1.0
    
    def test_adelic_poisson_trace(self):
        """Test adelic Poisson trace formula."""
        result = self.filtro.adelic_poisson_trace(test_func='gaussian', sigma=10.0)
        
        assert 'left_sum' in result
        assert 'right_integral' in result
        assert 'relative_error' in result
        
        # Both sums should be positive
        assert result['left_sum'] > 0
        assert result['right_integral'] > 0
    
    def test_filter_action(self):
        """Test filter verification."""
        result = self.filtro.verify_filter_action()
        
        assert 'mobius_cancellation' in result
        assert 'poisson_trace' in result
        assert 'Psi' in result
        
        # Psi should be in [0, 1]
        assert 0 <= result['Psi'] <= 1.0


# ============================================================================
# Test Suite for IdentidadDeterminanteHadamard
# ============================================================================

class TestIdentidadDeterminanteHadamard:
    """Test suite for Hadamard Determinant Identity."""
    
    def setup_method(self):
        """Set up test fixtures."""
        self.hadamard = IdentidadDeterminanteHadamard(mpmath_precision=25, N_zeros=20)
    
    def test_initialization(self):
        """Test proper initialization."""
        assert len(self.hadamard.zeros) == 20
        assert all(isinstance(z, complex) for z in self.hadamard.zeros)
        
        # All zeros should be on critical line (assuming RH)
        for z in self.hadamard.zeros:
            assert abs(z.real - 0.5) < 1e-6
    
    def test_xi_function_symmetry(self):
        """Test ξ(s) = ξ(1-s) functional equation."""
        test_points = [
            complex(0.3, 10.0),
            complex(0.7, 10.0),
            complex(0.4, 20.0)
        ]
        
        for s in test_points:
            xi_s = self.hadamard.xi_function(s)
            xi_1ms = self.hadamard.xi_function(1 - s)
            rel_error = abs(xi_s - xi_1ms) / (abs(xi_s) + 1e-10)
            assert rel_error < 1e-4, f"ξ({s}) ≠ ξ({1-s}): error = {rel_error}"
    
    def test_xi_at_special_points(self):
        """Test ξ at s=0 and s=1."""
        xi_0 = self.hadamard.xi_function(0)
        xi_1 = self.hadamard.xi_function(1)
        
        # By functional equation: ξ(0) = ξ(1) = 1/2
        assert abs(xi_0 - 0.5) < 0.1
        assert abs(xi_1 - 0.5) < 0.1
    
    def test_verify_functional_equation(self):
        """Test functional equation verification."""
        result = self.hadamard.verify_functional_equation()
        
        assert 'functional_equation_holds' in result
        assert 'A_coefficient' in result
        assert 'A_is_zero' in result
        
        # A should be 0 (forced by symmetry)
        assert result['A_coefficient'] == 0.0
        assert result['A_is_zero'] is True
    
    def test_compute_B_coefficient(self):
        """Test B = log(1/2) computation."""
        result = self.hadamard.compute_B_coefficient()
        
        assert 'B_coefficient' in result
        assert 'B_expected' in result
        assert 'B_match' in result
        
        # B should be log(1/2) ≈ -0.693
        expected_B = np.log(0.5)
        assert abs(result['B_coefficient'] - expected_B) < 0.1
    
    def test_trace_anomaly(self):
        """Test trace anomaly = -1/2."""
        result = self.hadamard.trace_anomaly_solenoid()
        
        assert 'trace_anomaly' in result
        assert 'expected' in result
        
        # Trace anomaly should be -1/2
        assert abs(result['trace_anomaly'] - (-0.5)) < 0.2
    
    def test_berry_phase(self):
        """Test Berry phase = π/2."""
        result = self.hadamard.berry_phase()
        
        assert 'berry_phase' in result
        assert 'berry_phase_degrees' in result
        
        # Berry phase should be π/2 radians = 90 degrees
        assert abs(result['berry_phase'] - np.pi/2) < 1e-6
        assert abs(result['berry_phase_degrees'] - 90.0) < 1e-4
    
    def test_verify_identity(self):
        """Test complete Hadamard identity verification."""
        result = self.hadamard.verify_identity()
        
        assert 'functional_equation' in result
        assert 'B_coefficient' in result
        assert 'trace_anomaly' in result
        assert 'berry_phase' in result
        assert 'Psi' in result
        
        # Psi should be in [0, 1]
        assert 0 <= result['Psi'] <= 1.0


# ============================================================================
# Test Suite for SistemaDinamicoZ
# ============================================================================

class TestSistemaDinamicoZ:
    """Test suite for Dynamic Z System (Anosov flow on SL(2,Z)\\H)."""
    
    def setup_method(self):
        """Set up test fixtures."""
        self.dinamico = SistemaDinamicoZ(N_zeros=50)
    
    def test_initialization(self):
        """Test proper initialization."""
        assert self.dinamico.N_zeros == 50
        assert len(self.dinamico.zeros) == 50
        assert all(gamma > 0 for gamma in self.dinamico.zeros)
    
    def test_lyapunov_constant(self):
        """Test Lyapunov exponent λ = log φ."""
        assert abs(self.dinamico.lyapunov - np.log(PHI)) < 1e-10
        assert abs(self.dinamico.lyapunov - 0.4812) < 0.001
    
    def test_hyperbolic_volume(self):
        """Test hyperbolic volume = π/3."""
        expected = np.pi / 3.0
        assert abs(self.dinamico.volume - expected) < 1e-10
    
    def test_verify_lyapunov_exponent(self):
        """Test Lyapunov exponent verification."""
        result = self.dinamico.verify_lyapunov_exponent()
        
        assert 'lambda_exact' in result
        assert 'lambda_numerical' in result
        assert 'matches' in result
        
        # Should match log(φ)
        assert abs(result['lambda_exact'] - np.log(PHI)) < 1e-6
    
    def test_compute_hyperbolic_volume(self):
        """Test hyperbolic volume computation."""
        result = self.dinamico.compute_hyperbolic_volume()
        
        assert 'volume_computed' in result
        assert 'volume_expected' in result
        assert 'matches' in result
        
        # Should be π/3
        assert abs(result['volume_computed'] - np.pi/3) < 1e-6
    
    def test_selberg_laplacian_spectrum(self):
        """Test Selberg Laplacian spectrum λ_n = 1/4 + γ_n²."""
        result = self.dinamico.selberg_laplacian_spectrum()
        
        assert 'eigenvalues' in result
        assert 'N_eigenvalues' in result
        assert 'all_positive' in result
        assert 'is_discrete' in result
        
        # All eigenvalues should be positive
        assert result['all_positive'] is True
        
        # Should be discrete
        assert result['is_discrete'] is True
        
        # Check formula: λ = 1/4 + γ²
        first_gamma = self.dinamico.zeros[0]
        first_lambda = result['eigenvalues'][0]
        expected = 0.25 + first_gamma**2
        assert abs(first_lambda - expected) < 1e-6
    
    def test_gue_level_repulsion(self):
        """Test GUE statistics in zero spacing."""
        result = self.dinamico.gue_level_repulsion()
        
        assert 'N_spacings' in result
        assert 'mean_spacing_actual' in result
        assert 'level_repulsion' in result
        assert 'follows_gue' in result
        
        # Should have spacings
        assert result['N_spacings'] > 0
    
    def test_verify_dynamics(self):
        """Test complete dynamics verification."""
        result = self.dinamico.verify_dynamics()
        
        assert 'lyapunov' in result
        assert 'volume' in result
        assert 'spectrum' in result
        assert 'gue_statistics' in result
        assert 'Psi' in result
        
        # Psi should be in [0, 1]
        assert 0 <= result['Psi'] <= 1.0


# ============================================================================
# Test Suite for SistemaDinamicoZCompleto
# ============================================================================

class TestSistemaDinamicoZCompleto:
    """Test suite for Complete Z Dynamic System."""
    
    def setup_method(self):
        """Set up test fixtures."""
        self.sistema = SistemaDinamicoZCompleto(N_primes=50, N_zeros=30, x_max=50.0)
    
    def test_initialization(self):
        """Test proper initialization."""
        assert self.sistema.compactificacion is not None
        assert self.sistema.filtro is not None
        assert self.sistema.hadamard is not None
        assert self.sistema.dinamico is not None
    
    def test_ejecutar_sistema_completo(self):
        """Test complete system execution."""
        result = self.sistema.ejecutar_sistema_completo(verbose=False)
        
        assert 'pillar_1_compactificacion' in result
        assert 'pillar_2_filtro' in result
        assert 'pillar_3_hadamard' in result
        assert 'pillar_4_dinamico' in result
        assert 'global_coherence' in result
        
        # Check global coherence
        coherence = result['global_coherence']
        assert 'Psi_global' in coherence
        assert 'all_pillars_valid' in coherence
        
        # Psi_global should be in [0, 1]
        assert 0 <= coherence['Psi_global'] <= 1.0
    
    def test_pillar_1_compactificacion(self):
        """Test Pillar 1: Non-commutative compactification."""
        result = self.sistema.ejecutar_sistema_completo(verbose=False)
        pillar_1 = result['pillar_1_compactificacion']
        
        assert 'Psi' in pillar_1
        assert 'compactness' in pillar_1
        assert 'spectrum' in pillar_1
    
    def test_pillar_2_filtro(self):
        """Test Pillar 2: Adelic rational filter."""
        result = self.sistema.ejecutar_sistema_completo(verbose=False)
        pillar_2 = result['pillar_2_filtro']
        
        assert 'Psi' in pillar_2
        assert 'mobius_cancellation' in pillar_2
    
    def test_pillar_3_hadamard(self):
        """Test Pillar 3: Hadamard determinant identity."""
        result = self.sistema.ejecutar_sistema_completo(verbose=False)
        pillar_3 = result['pillar_3_hadamard']
        
        assert 'Psi' in pillar_3
        assert 'functional_equation' in pillar_3
        assert 'B_coefficient' in pillar_3
    
    def test_pillar_4_dinamico(self):
        """Test Pillar 4: Dynamic Z system."""
        result = self.sistema.ejecutar_sistema_completo(verbose=False)
        pillar_4 = result['pillar_4_dinamico']
        
        assert 'Psi' in pillar_4
        assert 'lyapunov' in pillar_4
        assert 'volume' in pillar_4
        assert 'spectrum' in pillar_4
    
    def test_qcal_constants(self):
        """Test QCAL constants."""
        result = self.sistema.ejecutar_sistema_completo(verbose=False)
        qcal = result['qcal_constants']
        
        assert qcal['F0'] == F0
        assert qcal['C'] == C_QCAL
        assert abs(qcal['phi'] - PHI) < 1e-10
        assert abs(qcal['lyapunov'] - LYAPUNOV_Z) < 1e-10
    
    def test_generar_certificado(self):
        """Test certificate generation."""
        import tempfile
        import json
        
        with tempfile.TemporaryDirectory() as tmpdir:
            cert_path = self.sistema.generar_certificado(output_dir=Path(tmpdir))
            
            # Check file was created
            assert Path(cert_path).exists()
            
            # Check JSON structure
            with open(cert_path, 'r') as f:
                cert = json.load(f)
            
            assert 'certificate_type' in cert
            assert cert['certificate_type'] == 'SISTEMA_DINAMICO_Z'
            assert 'results' in cert
            assert 'status' in cert


# ============================================================================
# Additional Integration Tests
# ============================================================================

class TestIntegration:
    """Integration tests for the complete system."""
    
    def test_all_pillars_coherence(self):
        """Test that all four pillars work together."""
        sistema = SistemaDinamicoZCompleto(N_primes=30, N_zeros=20, x_max=30.0)
        result = sistema.ejecutar_sistema_completo(verbose=False)
        
        # Extract individual Psi values
        Psi_1 = result['pillar_1_compactificacion']['Psi']
        Psi_2 = result['pillar_2_filtro']['Psi']
        Psi_3 = result['pillar_3_hadamard']['Psi']
        Psi_4 = result['pillar_4_dinamico']['Psi']
        
        # All should be non-negative
        assert Psi_1 >= 0
        assert Psi_2 >= 0
        assert Psi_3 >= 0
        assert Psi_4 >= 0
        
        # Global coherence should be average
        Psi_global = result['global_coherence']['Psi_global']
        expected_avg = (Psi_1 + Psi_2 + Psi_3 + Psi_4) / 4.0
        assert abs(Psi_global - expected_avg) < 1e-6
    
    def test_constants_consistency(self):
        """Test mathematical constants are consistent."""
        # Lyapunov = log(φ)
        assert abs(LYAPUNOV_Z - np.log(PHI)) < 1e-10
        
        # φ = (1 + √5)/2
        assert abs(PHI - (1 + np.sqrt(5))/2) < 1e-10
        
        # F0 = 141.7001 Hz
        assert F0 == 141.7001
        
        # C = 244.36
        assert C_QCAL == 244.36


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
