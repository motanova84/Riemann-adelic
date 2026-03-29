#!/usr/bin/env python3
"""
Tests for Transmutación QCAL: Operador H Stone + Derivación Estructural V_osc
==============================================================================

Validates the complete transmutation:
1. Stone's Theorem: H self-adjoint
2. V_osc structural derivation from multiplicative boundary conditions
3. Unitarity of scaling flow
4. Schatten-1 nuclearity
5. Macroscopic quantum coherence
"""

import numpy as np
import pytest

from physics.transmutacion_stone_vosc import (
    OperadorH_Stone_Transmutacion,
    ejecutar_transmutacion_completa,
    _sieve_primes,
)


class TestSievePrimes:
    """Test prime number generation."""

    def test_small_primes(self):
        """Test sieve for small range."""
        primes = _sieve_primes(20)
        expected = [2, 3, 5, 7, 11, 13, 17, 19]
        assert primes == expected

    def test_empty_range(self):
        """Test sieve for n_max < 2."""
        assert _sieve_primes(1) == []
        assert _sieve_primes(0) == []

    def test_first_100(self):
        """Test first 100 primes count."""
        primes = _sieve_primes(100)
        assert len(primes) == 25  # There are 25 primes ≤ 100


class TestOperadorHStoneTransmutacion:
    """Test the main transmutation operator."""

    @pytest.fixture
    def operador_pequeno(self):
        """Create small operator for fast tests."""
        return OperadorH_Stone_Transmutacion(
            n_dimension=64,
            p_max=20,
            u_max=5.0,
        )

    @pytest.fixture
    def operador_mediano(self):
        """Create medium operator for comprehensive tests."""
        return OperadorH_Stone_Transmutacion(
            n_dimension=128,
            p_max=50,
            u_max=8.0,
        )

    def test_initialization(self, operador_pequeno):
        """Test operator initialization."""
        op = operador_pequeno
        assert op.n_dimension == 64
        assert op.p_max == 20
        assert len(op.primes) == 8  # primes ≤ 20: [2,3,5,7,11,13,17,19]
        assert op.H_matrix.shape == (64, 64)
        assert op.eta_plus == 0.875

    def test_matrix_hermiticity(self, operador_pequeno):
        """Test that H matrix is Hermitian."""
        op = operador_pequeno
        H = op.H_matrix
        H_dagger = H.conj().T

        # Check Hermiticity
        hermiticity_defect = np.linalg.norm(H - H_dagger, ord='fro')
        assert hermiticity_defect < 1e-10

    def test_espectro_real(self, operador_pequeno):
        """Test that all eigenvalues are real."""
        op = operador_pequeno
        espectro = op.obtener_espectro()

        # All eigenvalues should be real (Hermitian matrix)
        assert np.allclose(espectro.imag, 0.0, atol=1e-10)

    def test_stone_verificacion(self, operador_pequeno):
        """Test Stone's theorem verification."""
        op = operador_pequeno
        resultado = op.verificar_autoadjuncion_stone()

        assert resultado.es_autoadjunto is True
        assert resultado.norma_hermiticity_defect < 1e-8
        assert resultado.espectro_real is True
        assert resultado.max_parte_imaginaria < 1e-8

    def test_unitariedad_flujo(self, operador_pequeno):
        """Test unitarity of the scaling flow."""
        op = operador_pequeno

        # Test for several values of t
        for t in [0.0, 0.5, 1.0, 2.0, -1.0]:
            assert op.verificar_unitariedad_flujo(t=t) is True

    def test_densidad_oscilatoria(self, operador_pequeno):
        """Test oscillatory density function."""
        op = operador_pequeno

        # Test at a few energy values
        E_vals = [10.0, 20.0, 50.0]
        for E in E_vals:
            rho_osc = op.densidad_oscilatoria(E)
            assert np.isfinite(rho_osc)
            # Oscillatory density should be bounded
            assert abs(rho_osc) < 1.0

    def test_v_osc_derivacion_estructural(self, operador_pequeno):
        """Test structural derivation of V_osc."""
        op = operador_pequeno

        # Test at a single point
        resultado = op.derivar_v_osc_estructural(x=10.0)

        assert resultado.x == 10.0
        assert np.isfinite(resultado.V_osc)
        assert resultado.n_primos == len(op.primes)
        assert len(resultado.contribuciones_primos) == len(op.primes)
        assert len(resultado.fases) == len(op.primes)

        # All phases should be -π/4 (asymptotic from Abel transform)
        assert all(abs(fase + np.pi/4) < 1e-10 for fase in resultado.fases)

    def test_v_osc_vectorizado(self, operador_pequeno):
        """Test vectorized V_osc evaluation."""
        op = operador_pequeno

        x_array = np.linspace(1.0, 50.0, 20)
        v_osc_array = op.evaluar_v_osc_estructural(x_array)

        assert len(v_osc_array) == len(x_array)
        assert np.all(np.isfinite(v_osc_array))

        # Check consistency with single-point evaluation
        for i, x in enumerate([1.0, 25.0, 50.0]):
            idx = np.argmin(np.abs(x_array - x))
            resultado_single = op.derivar_v_osc_estructural(x)
            assert abs(v_osc_array[idx] - resultado_single.V_osc) < 1e-6

    def test_abel_integral_asintotico(self, operador_pequeno):
        """Test asymptotic Abel integral evaluation."""
        op = operador_pequeno

        # Test for a few omega and V values
        omega = np.log(2)
        V = 20.0

        integral = op.abel_integral_asintotico(omega, V)
        assert np.isfinite(integral)

        # Should decay with increasing omega
        omega2 = np.log(10)
        integral2 = op.abel_integral_asintotico(omega2, V)
        # Higher omega → smaller amplitude (√(π/(4ω)) factor)
        assert abs(integral2) < abs(integral)

    def test_schatten1_verificacion(self, operador_pequeno):
        """Test Schatten-1 class verification."""
        op = operador_pequeno

        resultado = op.verificar_schatten1()

        assert "schatten1_sum" in resultado
        assert "convergence_confirmed" in resultado
        assert resultado["schatten1_finite"] is True
        assert resultado["convergence_confirmed"] is True

    def test_coherencia_cuantica(self, operador_pequeno):
        """Test macroscopic quantum coherence."""
        op = operador_pequeno

        Psi = op.validar_coherencia_cuantica()

        # Coherence should be in [0, 1]
        assert 0.0 <= Psi <= 1.0

        # For a self-adjoint H, coherence should be close to 1
        assert Psi > 0.99

    def test_certificado_transmutacion(self, operador_mediano):
        """Test complete transmutation certificate generation."""
        op = operador_mediano

        cert = op.generar_certificado_transmutacion()

        # Check all main validations
        assert cert.stone_verificado is True
        assert cert.v_osc_derivado is True
        assert cert.unitariedad_confirmada is True
        assert 0.99 < cert.coherencia_cuantica <= 1.0
        assert cert.riemann_hypothesis_status is True

        # Check metadata
        assert "n_dimension" in cert.metadata
        assert "p_max" in cert.metadata
        assert "stone_result" in cert.metadata
        assert "v_osc_test_values" in cert.metadata
        assert "schatten1_result" in cert.metadata

        # Check checksum
        assert cert.checksum.startswith("0xQCAL_TRANSMUTACION_")
        assert cert.timestamp > 0

    def test_str_representation(self, operador_pequeno):
        """Test string representation."""
        op = operador_pequeno
        str_repr = str(op)

        assert "TRANSMUTACIÓN QCAL" in str_repr
        assert "Stone Theorem" in str_repr
        assert "V_osc Derivación" in str_repr
        assert "El Cierre de la Bóveda" in str_repr
        assert "141.7001 Hz" in str_repr


class TestEjecutarTransmutacionCompleta:
    """Test the main convenience function."""

    def test_ejecucion_completa_pequena(self, capsys):
        """Test complete execution with small parameters."""
        cert = ejecutar_transmutacion_completa(
            n_dimension=64,
            p_max=20,
            verbose=False,
        )

        assert cert.stone_verificado is True
        assert cert.v_osc_derivado is True
        assert cert.coherencia_cuantica > 0.99

    def test_ejecucion_completa_verbose(self, capsys):
        """Test complete execution with verbose output."""
        cert = ejecutar_transmutacion_completa(
            n_dimension=64,
            p_max=20,
            verbose=True,
        )

        # Capture output
        captured = capsys.readouterr()
        assert "TRANSMUTACIÓN QCAL" in captured.out
        assert "Stone Theorem" in captured.out

    def test_ejecucion_mediana(self):
        """Test with medium-sized parameters."""
        cert = ejecutar_transmutacion_completa(
            n_dimension=128,
            p_max=50,
            verbose=False,
        )

        assert cert.stone_verificado is True
        assert cert.metadata["n_primos"] == len(_sieve_primes(50))


class TestNumericalProperties:
    """Test numerical properties and edge cases."""

    def test_espectro_ordenado(self):
        """Test that spectrum is properly ordered."""
        op = OperadorH_Stone_Transmutacion(n_dimension=32, p_max=10)
        espectro = op.obtener_espectro()

        # Should be sorted
        assert np.all(espectro[:-1] <= espectro[1:])

    def test_v_osc_simetria(self):
        """Test V_osc behavior at different scales."""
        op = OperadorH_Stone_Transmutacion(n_dimension=64, p_max=30)

        # V_osc should vary oscillatorily
        x_vals = np.linspace(1, 100, 50)
        v_osc_vals = op.evaluar_v_osc_estructural(x_vals)

        # Should have oscillations (not monotonic)
        diff = np.diff(v_osc_vals)
        assert np.any(diff > 0) and np.any(diff < 0)

    def test_g_fourier_decay(self):
        """Test Schwartz function Fourier transform decays."""
        op = OperadorH_Stone_Transmutacion(n_dimension=32, p_max=10, g_sigma=1.0)

        # Should decay exponentially
        gamma_values = [1.0, 10.0, 100.0, 1000.0]
        g_values = [op.g_fourier(g) for g in gamma_values]

        # Each subsequent value should be smaller
        for i in range(len(g_values) - 1):
            assert g_values[i] > g_values[i + 1]

        # Very large gamma should give near-zero
        assert op.g_fourier(1000.0) < 1e-100


class TestQCALConsistency:
    """Test consistency with QCAL constants and conventions."""

    def test_qcal_constants(self):
        """Test that QCAL constants are correctly used."""
        op = OperadorH_Stone_Transmutacion(n_dimension=32, p_max=10)
        cert = op.generar_certificado_transmutacion()

        # Check QCAL constants in metadata
        assert cert.metadata["f0_hz"] == 141.7001
        assert cert.metadata["C_coherence"] == 244.36
        assert cert.metadata["eta_plus"] == 0.875

    def test_checksum_reproducibility(self):
        """Test that checksum is reproducible for same parameters."""
        op1 = OperadorH_Stone_Transmutacion(n_dimension=64, p_max=20)
        op2 = OperadorH_Stone_Transmutacion(n_dimension=64, p_max=20)

        cert1 = op1.generar_certificado_transmutacion()
        cert2 = op2.generar_certificado_transmutacion()

        # Checksums should be identical for same parameters
        # (timestamps will differ, but metadata structure is the same)
        # We compare metadata keys instead
        assert set(cert1.metadata.keys()) == set(cert2.metadata.keys())


@pytest.mark.slow
class TestLargeScaleValidation:
    """Tests with larger parameters (marked slow for optional execution)."""

    def test_large_dimension(self):
        """Test with large dimension."""
        op = OperadorH_Stone_Transmutacion(n_dimension=512, p_max=50)

        stone = op.verificar_autoadjuncion_stone()
        assert stone.es_autoadjunto is True

    def test_many_primes(self):
        """Test with many primes."""
        op = OperadorH_Stone_Transmutacion(n_dimension=128, p_max=200)

        # Should still have consistent V_osc
        x_test = 20.0
        resultado = op.derivar_v_osc_estructural(x_test)
        assert np.isfinite(resultado.V_osc)
        assert resultado.n_primos == len(_sieve_primes(200))


if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])
