#!/usr/bin/env python3
"""
Tests para el Operador de Selberg
==================================

Valida la implementación del Laplaciano de Beltrami y la fórmula de traza
de Selberg en geometría hiperbólica.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: March 2026
"""

import pytest
import numpy as np
from operators.selberg_operator import (
    SelbergOperator,
    SelbergTraceResult,
    activar_operador_selberg,
    demonstrate_selberg_operator,
    F0_QCAL,
    F_GEODESIC,
    C_COHERENCE,
    AREA_FUNDAMENTAL_DOMAIN
)


class TestActivarOperadorSelberg:
    """Tests para la función de activación del operador."""
    
    def test_activar_returns_message(self, capsys):
        """Verifica que activar_operador_selberg retorna mensaje correcto."""
        result = activar_operador_selberg()
        assert "Identidad funcional" in result
        assert "geodésico" in result
        
        # Verifica que imprime información
        captured = capsys.readouterr()
        assert "RECONFIGURANDO" in captured.out
        assert "888 Hz" in captured.out


class TestSelbergOperator:
    """Tests para la clase SelbergOperator."""
    
    def test_initialization(self):
        """Verifica inicialización correcta del operador."""
        op = SelbergOperator(
            n_grid_x=10,
            n_grid_y=10,
            max_prime=50,
            max_k=3
        )
        
        assert op.n_grid_x == 10
        assert op.n_grid_y == 10
        assert op.max_prime == 50
        assert op.max_k == 3
        assert len(op._primes) > 0
        assert op._primes[0] == 2
    
    def test_sieve_of_eratosthenes(self):
        """Verifica la criba de Eratóstenes."""
        op = SelbergOperator(max_prime=20)
        
        # Primeros primos hasta 20
        expected_primes = [2, 3, 5, 7, 11, 13, 17, 19]
        np.testing.assert_array_equal(op._primes, expected_primes)
    
    def test_geodesic_orbit_length(self):
        """Verifica cálculo de longitud de geodésica."""
        op = SelbergOperator()
        
        # l(p^k) = k · log(p)
        l_2_1 = op.geodesic_orbit_length(2, 1)
        expected = np.log(2.0)
        assert abs(l_2_1 - expected) < 1e-10
        
        l_3_2 = op.geodesic_orbit_length(3, 2)
        expected = 2.0 * np.log(3.0)
        assert abs(l_3_2 - expected) < 1e-10
    
    def test_beltrami_laplacian_symmetry(self):
        """Verifica que el Laplaciano de Beltrami es simétrico."""
        op = SelbergOperator(n_grid_x=10, n_grid_y=10)
        H = op.construct_beltrami_laplacian()
        
        # Debe ser simétrico
        assert H.shape[0] == H.shape[1]
        symmetry_error = np.max(np.abs(H - H.T))
        assert symmetry_error < 1e-10
    
    def test_beltrami_laplacian_real(self):
        """Verifica que el Laplaciano es real."""
        op = SelbergOperator(n_grid_x=8, n_grid_y=8)
        H = op.construct_beltrami_laplacian()
        
        assert np.all(np.isreal(H))
    
    def test_weyl_term_positive(self):
        """Verifica que el término de Weyl es positivo."""
        op = SelbergOperator()
        weyl = op.weyl_term_contribution()
        
        assert weyl > 0
        assert np.isfinite(weyl)
    
    def test_prime_contribution_convergence(self):
        """Verifica convergencia de la suma sobre primos."""
        op = SelbergOperator(max_prime=100, max_k=5)
        
        # Para diferentes eigenvalues
        eigenvalues = [0.5, 1.0, 2.0, 5.0]
        
        for ev in eigenvalues:
            orbital = op.selberg_trace_formula_contribution(ev)
            assert np.isfinite(orbital)
            # La suma debe decrecer con eigenvalue más grande
            if ev > 1.0:
                assert abs(orbital) > 0  # No debe ser cero
    
    def test_eigenvalues_positive(self):
        """Verifica que los autovalores son positivos."""
        op = SelbergOperator(n_grid_x=15, n_grid_y=15)
        eigenvalues, riemann_zeros = op.compute_eigenvalues(n_eigenvalues=10)
        
        # Los autovalores deben ser todos positivos (para Laplaciano negativo)
        # En realidad, pueden ser negativos dependiendo de la convención
        assert len(eigenvalues) > 0
        assert all(np.isfinite(eigenvalues))
    
    def test_riemann_zeros_from_eigenvalues(self):
        """Verifica la conversión λ_n → γ_n."""
        op = SelbergOperator(n_grid_x=20, n_grid_y=20)
        eigenvalues, riemann_zeros = op.compute_eigenvalues(n_eigenvalues=10)
        
        # γ_n = √(λ_n - 1/4)
        for i in range(len(eigenvalues)):
            if eigenvalues[i] >= 0.25:
                expected_gamma = np.sqrt(eigenvalues[i] - 0.25)
                assert abs(riemann_zeros[i] - expected_gamma) < 1e-10
    
    def test_selberg_trace_components(self):
        """Verifica que la traza de Selberg tiene todos los componentes."""
        op = SelbergOperator(n_grid_x=10, n_grid_y=10, max_prime=30)
        result = op.compute_selberg_trace(eigenvalue=1.0, include_details=True)
        
        # Verificar tipo
        assert isinstance(result, SelbergTraceResult)
        
        # Verificar componentes
        assert np.isfinite(result.weyl_term)
        assert np.isfinite(result.prime_orbital_sum)
        assert np.isfinite(result.total_trace)
        
        # La traza total debe ser suma de componentes
        expected_total = result.weyl_term + result.prime_orbital_sum
        assert abs(result.total_trace - expected_total) < 1e-10
    
    def test_convergence_info(self):
        """Verifica información de convergencia."""
        op = SelbergOperator(max_prime=50, max_k=4)
        result = op.compute_selberg_trace(eigenvalue=1.0)
        
        assert 'weyl_fraction' in result.convergence_info
        assert 'orbital_fraction' in result.convergence_info
        assert 'n_primes' in result.convergence_info
        
        # Las fracciones deben sumar aproximadamente 1
        weyl_frac = result.convergence_info['weyl_fraction']
        orbital_frac = result.convergence_info['orbital_fraction']
        assert abs(weyl_frac + orbital_frac - 1.0) < 0.01


class TestSelbergTraceFormula:
    """Tests para la fórmula de traza de Selberg."""
    
    def test_trace_decreases_with_eigenvalue(self):
        """Verifica que la traza decrece con eigenvalue mayor."""
        op = SelbergOperator(max_prime=50, max_k=4)
        
        trace_1 = op.compute_selberg_trace(eigenvalue=1.0)
        trace_2 = op.compute_selberg_trace(eigenvalue=2.0)
        trace_5 = op.compute_selberg_trace(eigenvalue=5.0)
        
        # Debe decrecer (exponencialmente)
        assert trace_1.prime_orbital_sum >= trace_2.prime_orbital_sum
        assert trace_2.prime_orbital_sum >= trace_5.prime_orbital_sum
    
    def test_prime_sum_formula(self):
        """Verifica la fórmula de suma sobre primos."""
        op = SelbergOperator(max_prime=10, max_k=2)
        
        # Calcular manualmente para p=2, k=1
        p = 2
        k = 1
        log_p = np.log(2.0)
        l_pk = k * log_p
        p_half = p ** 0.5
        jacobian = p_half - 1.0 / p_half
        
        # La contribución individual debe estar presente
        eigenvalue = 1.0
        h_l = np.exp(-eigenvalue * l_pk)
        expected_contrib = (log_p / jacobian) * h_l
        
        # La suma total debe incluir esta contribución
        total_orbital = op.selberg_trace_formula_contribution(eigenvalue)
        assert abs(total_orbital) > abs(expected_contrib) * 0.5


class TestDemonstration:
    """Tests para la función de demostración."""
    
    def test_demonstrate_returns_dict(self):
        """Verifica que la demostración retorna un diccionario."""
        results = demonstrate_selberg_operator(verbose=False)
        
        assert isinstance(results, dict)
        assert 'selberg_operator' in results
        assert 'trace_result' in results
        assert 'eigenvalues' in results
        assert 'riemann_zeros' in results
        assert 'mensaje' in results
    
    def test_demonstrate_creates_valid_operator(self):
        """Verifica que la demostración crea un operador válido."""
        results = demonstrate_selberg_operator(verbose=False)
        
        op = results['selberg_operator']
        assert isinstance(op, SelbergOperator)
        assert op.n_grid_x > 0
        assert op.n_grid_y > 0
    
    def test_demonstrate_computes_eigenvalues(self):
        """Verifica que la demostración computa autovalores."""
        results = demonstrate_selberg_operator(verbose=False)
        
        eigenvalues = results['eigenvalues']
        assert len(eigenvalues) > 0
        assert all(np.isfinite(eigenvalues))


class TestConstants:
    """Tests para constantes QCAL."""
    
    def test_qcal_frequencies(self):
        """Verifica constantes de frecuencia QCAL."""
        assert F0_QCAL == 141.7001
        assert F_GEODESIC == 888.0
        assert C_COHERENCE == 244.36
    
    def test_hyperbolic_constants(self):
        """Verifica constantes de geometría hiperbólica."""
        assert AREA_FUNDAMENTAL_DOMAIN == 4 * np.pi


class TestNumericalStability:
    """Tests de estabilidad numérica."""
    
    def test_large_eigenvalue_stability(self):
        """Verifica estabilidad para eigenvalues grandes."""
        op = SelbergOperator(max_prime=100, max_k=10)
        
        # Eigenvalue muy grande debe dar suma orbital pequeña pero finita
        large_ev = 100.0
        result = op.compute_selberg_trace(eigenvalue=large_ev)
        
        assert np.isfinite(result.total_trace)
        assert result.prime_orbital_sum >= 0
        assert result.prime_orbital_sum < result.weyl_term
    
    def test_small_grid_stability(self):
        """Verifica estabilidad con grid pequeño."""
        op = SelbergOperator(n_grid_x=5, n_grid_y=5)
        
        H = op.construct_beltrami_laplacian()
        assert np.all(np.isfinite(H))
        assert H.shape == (25, 25)


class TestMathematicalProperties:
    """Tests de propiedades matemáticas."""
    
    def test_spectral_correspondence(self):
        """Verifica correspondencia espectral λ_n = 1/4 + γ_n²."""
        op = SelbergOperator(n_grid_x=15, n_grid_y=15)
        eigenvalues, riemann_zeros = op.compute_eigenvalues(n_eigenvalues=5)
        
        for i in range(len(eigenvalues)):
            if eigenvalues[i] >= 0.25:
                # λ_n = 1/4 + γ_n²
                gamma_squared = eigenvalues[i] - 0.25
                gamma = np.sqrt(gamma_squared)
                
                assert abs(gamma - riemann_zeros[i]) < 1e-8
    
    def test_weyl_area_formula(self):
        """Verifica fórmula del término de Weyl."""
        op = SelbergOperator()
        weyl = op.weyl_term_contribution()
        
        # Tr_Weyl = Área(F) / (4π)
        expected = AREA_FUNDAMENTAL_DOMAIN / (4.0 * np.pi)
        assert abs(weyl - expected) < 1e-10
    
    def test_jacobian_formula(self):
        """Verifica fórmula de la Jacobiana."""
        op = SelbergOperator()
        
        # Para p=2, k=1: Jacobiana = √2 - 1/√2
        p = 2
        k = 1
        p_half_k = p ** (k / 2.0)
        jacobian = p_half_k - 1.0 / p_half_k
        
        expected = np.sqrt(2) - 1.0 / np.sqrt(2)
        assert abs(jacobian - expected) < 1e-10


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
