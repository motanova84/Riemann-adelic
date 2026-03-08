#!/usr/bin/env python3
"""
Tests for Riemann Cierre Omega Module
======================================

Suite de 80 pruebas que cubre las cuatro clases y la función pública:
- GeometriaPrimos (Lado A): 20 tests
- EspectroCeros (Lado B): 20 tests
- VinculoWeil: 20 tests
- CierreArquitectura: 15 tests
- cierre_rh_omega() function: 5 tests

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz
"""

import sys
import numpy as np
import pytest
from pathlib import Path

# Add operators directory to path
repo_root = Path(__file__).parent.parent
sys.path.insert(0, str(repo_root / "operators"))

from riemann_cierre_omega import (
    GeometriaPrimos,
    EspectroCeros,
    VinculoWeil,
    CierreArquitectura,
    cierre_rh_omega,
    GeometriaPrimosResult,
    EspectroCerosResult,
    VinculoWeilResult,
    CierreArquitecturaResult,
    F0_QCAL,
    OMEGA_0,
    C_COHERENCE,
    PHI,
    EULER_GAMMA
)


# =====================================================================
# TEST SUITE: GEOMETRIA PRIMOS (LADO A) - 20 TESTS
# =====================================================================

class TestGeometriaPrimos:
    """Test suite for GeometriaPrimos class (Side A)."""
    
    def test_init(self):
        """Test 1: GeometriaPrimos initialization."""
        geom = GeometriaPrimos(precision=30)
        assert geom.precision == 30
        print("✅ Test 1: Initialization PASSED")
    
    def test_generate_primes_empty(self):
        """Test 2: Generate primes with limit < 2 returns empty list."""
        geom = GeometriaPrimos()
        primes = geom.generate_primes(1)
        assert primes == []
        print("✅ Test 2: Empty primes PASSED")
    
    def test_generate_primes_small(self):
        """Test 3: Generate first 10 primes."""
        geom = GeometriaPrimos()
        primes = geom.generate_primes(30)
        expected = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
        assert primes == expected
        print("✅ Test 3: Small primes PASSED")
    
    def test_generate_primes_100(self):
        """Test 4: Generate primes up to 100."""
        geom = GeometriaPrimos()
        primes = geom.generate_primes(100)
        assert len(primes) == 25  # There are 25 primes below 100
        assert primes[0] == 2
        assert primes[-1] == 97
        print("✅ Test 4: Primes up to 100 PASSED")
    
    def test_chebyshev_psi_zero(self):
        """Test 5: Chebyshev ψ(1) = 0."""
        geom = GeometriaPrimos()
        primes = geom.generate_primes(10)
        psi = geom.chebyshev_psi(1, primes)
        assert psi == 0.0
        print("✅ Test 5: Chebyshev ψ(1) = 0 PASSED")
    
    def test_chebyshev_psi_at_2(self):
        """Test 6: Chebyshev ψ(2) = log(2)."""
        geom = GeometriaPrimos()
        primes = geom.generate_primes(10)
        psi = geom.chebyshev_psi(2, primes)
        expected = np.log(2)
        assert np.isclose(psi, expected, rtol=1e-6)
        print("✅ Test 6: Chebyshev ψ(2) PASSED")
    
    def test_chebyshev_psi_at_10(self):
        """Test 7: Chebyshev ψ(10) = log(2) + log(3) + log(5) + log(7) + log(2²)."""
        geom = GeometriaPrimos()
        primes = geom.generate_primes(10)
        psi = geom.chebyshev_psi(10, primes)
        # Primes and powers: 2, 3, 4(=2²), 5, 7, 8(=2³), 9(=3²)
        expected = 3*np.log(2) + 2*np.log(3) + np.log(5) + np.log(7)
        assert np.isclose(psi, expected, rtol=1e-5)
        print("✅ Test 7: Chebyshev ψ(10) PASSED")
    
    def test_chebyshev_psi_positive(self):
        """Test 8: Chebyshev ψ(x) is non-negative."""
        geom = GeometriaPrimos()
        primes = geom.generate_primes(100)
        psi = geom.chebyshev_psi(50, primes)
        assert psi >= 0
        print("✅ Test 8: Chebyshev ψ positive PASSED")
    
    def test_chebyshev_psi_monotonic(self):
        """Test 9: Chebyshev ψ(x) is monotonically increasing."""
        geom = GeometriaPrimos()
        primes = geom.generate_primes(100)
        psi_10 = geom.chebyshev_psi(10, primes)
        psi_20 = geom.chebyshev_psi(20, primes)
        psi_50 = geom.chebyshev_psi(50, primes)
        assert psi_10 <= psi_20 <= psi_50
        print("✅ Test 9: Chebyshev ψ monotonic PASSED")
    
    def test_N_smooth_zero(self):
        """Test 10: N_smooth(0) = 0."""
        geom = GeometriaPrimos()
        n_smooth = geom.N_smooth(0)
        assert n_smooth == 0.0
        print("✅ Test 10: N_smooth(0) = 0 PASSED")
    
    def test_N_smooth_negative(self):
        """Test 11: N_smooth(E<0) = 0."""
        geom = GeometriaPrimos()
        n_smooth = geom.N_smooth(-5)
        assert n_smooth == 0.0
        print("✅ Test 11: N_smooth negative PASSED")
    
    def test_N_smooth_positive(self):
        """Test 12: N_smooth(E) > 0 for E > 2π."""
        geom = GeometriaPrimos()
        n_smooth = geom.N_smooth(10 * np.pi)
        assert n_smooth > 0
        print("✅ Test 12: N_smooth positive PASSED")
    
    def test_N_smooth_asymptotic(self):
        """Test 13: N_smooth(E) ~ E/(2π) log(E) for large E."""
        geom = GeometriaPrimos()
        E = 1000.0
        n_smooth = geom.N_smooth(E)
        asymptotic = (E / (2 * np.pi)) * np.log(E / (2 * np.pi))
        # Should be close to asymptotic term (allow 30% deviation due to correction terms)
        assert np.abs(n_smooth - asymptotic) < asymptotic * 0.3
        print("✅ Test 13: N_smooth asymptotic PASSED")
    
    def test_N_oscillatory_zero_energy(self):
        """Test 14: N_osc(0) = 0."""
        geom = GeometriaPrimos()
        primes = geom.generate_primes(20)
        n_osc = geom.N_oscillatory(0, primes)
        assert n_osc == 0.0
        print("✅ Test 14: N_osc(0) = 0 PASSED")
    
    def test_N_oscillatory_small_energy(self):
        """Test 15: N_osc(E) is finite for small E."""
        geom = GeometriaPrimos()
        primes = geom.generate_primes(50)
        n_osc = geom.N_oscillatory(10, primes, N_terms=20)
        assert np.isfinite(n_osc)
        print("✅ Test 15: N_osc finite PASSED")
    
    def test_N_oscillatory_bounded(self):
        """Test 16: N_osc(E) is bounded for reasonable E."""
        geom = GeometriaPrimos()
        primes = geom.generate_primes(100)
        n_osc = geom.N_oscillatory(100, primes, N_terms=50)
        assert np.abs(n_osc) < 1000  # Should be bounded
        print("✅ Test 16: N_osc bounded PASSED")
    
    def test_analizar_structure(self):
        """Test 17: analizar() returns correct structure."""
        geom = GeometriaPrimos()
        result = geom.analizar(x=50, E=100, primes_upto=100)
        assert isinstance(result, GeometriaPrimosResult)
        assert result.x_value == 50
        assert result.E_value == 100
        assert len(result.primes_used) > 0
        print("✅ Test 17: analizar structure PASSED")
    
    def test_analizar_values_positive(self):
        """Test 18: analizar() returns positive values."""
        geom = GeometriaPrimos()
        result = geom.analizar(x=100, E=100, primes_upto=200)
        assert result.chebyshev_psi >= 0
        assert result.N_smooth >= 0
        assert result.materia_norm >= 0
        print("✅ Test 18: analizar positive values PASSED")
    
    def test_materia_norm_calculation(self):
        """Test 19: Materia norm ||A|| = √(ψ² + N_smooth²)."""
        geom = GeometriaPrimos()
        result = geom.analizar(x=50, E=100, primes_upto=100)
        expected_norm = np.sqrt(result.chebyshev_psi**2 + result.N_smooth**2)
        assert np.isclose(result.materia_norm, expected_norm, rtol=1e-6)
        print("✅ Test 19: Materia norm PASSED")
    
    def test_primes_list_valid(self):
        """Test 20: Primes list contains only primes."""
        geom = GeometriaPrimos()
        result = geom.analizar(x=50, E=100, primes_upto=50)
        # Check all are prime
        for p in result.primes_used:
            if p < 2:
                assert False, f"{p} is not prime"
            for d in range(2, int(np.sqrt(p)) + 1):
                assert p % d != 0, f"{p} is not prime (divisible by {d})"
        print("✅ Test 20: Valid primes list PASSED")


# =====================================================================
# TEST SUITE: ESPECTRO CEROS (LADO B) - 20 TESTS
# =====================================================================

class TestEspectroCeros:
    """Test suite for EspectroCeros class (Side B)."""
    
    def test_init(self):
        """Test 21: EspectroCeros initialization."""
        espectro = EspectroCeros(precision=30)
        assert espectro.precision == 30
        print("✅ Test 21: Initialization PASSED")
    
    def test_get_reference_zeros_count(self):
        """Test 22: Get correct number of reference zeros."""
        espectro = EspectroCeros()
        zeros = espectro.get_reference_zeros(10)
        assert len(zeros) == 10
        print("✅ Test 22: Reference zeros count PASSED")
    
    def test_get_reference_zeros_ordered(self):
        """Test 23: Reference zeros are ordered."""
        espectro = EspectroCeros()
        zeros = espectro.get_reference_zeros(20)
        assert np.all(np.diff(zeros) > 0)  # Strictly increasing
        print("✅ Test 23: Reference zeros ordered PASSED")
    
    def test_get_reference_zeros_positive(self):
        """Test 24: Reference zeros are positive."""
        espectro = EspectroCeros()
        zeros = espectro.get_reference_zeros(15)
        assert np.all(zeros > 0)
        print("✅ Test 24: Reference zeros positive PASSED")
    
    def test_first_zero_value(self):
        """Test 25: First zero ≈ 14.134725."""
        espectro = EspectroCeros()
        zeros = espectro.get_reference_zeros(1)
        expected = 14.134725141734693790
        assert np.isclose(zeros[0], expected, rtol=1e-8)
        print("✅ Test 25: First zero value PASSED")
    
    def test_compute_wu_sprung_eigenvalues_count(self):
        """Test 26: Correct number of eigenvalues."""
        espectro = EspectroCeros()
        eigenvalues = espectro.compute_wu_sprung_eigenvalues(10)
        assert len(eigenvalues) == 10
        print("✅ Test 26: Eigenvalues count PASSED")
    
    def test_wu_sprung_eigenvalues_formula(self):
        """Test 27: λ_n = 1/4 + t_n²."""
        espectro = EspectroCeros()
        zeros = espectro.get_reference_zeros(5)
        eigenvalues = espectro.compute_wu_sprung_eigenvalues(5)
        expected = 0.25 + zeros**2
        assert np.allclose(eigenvalues, expected, rtol=1e-10)
        print("✅ Test 27: Wu-Sprung formula PASSED")
    
    def test_wu_sprung_eigenvalues_positive(self):
        """Test 28: Eigenvalues are positive."""
        espectro = EspectroCeros()
        eigenvalues = espectro.compute_wu_sprung_eigenvalues(20)
        assert np.all(eigenvalues > 0)
        print("✅ Test 28: Eigenvalues positive PASSED")
    
    def test_wu_sprung_eigenvalues_ordered(self):
        """Test 29: Eigenvalues are ordered."""
        espectro = EspectroCeros()
        eigenvalues = espectro.compute_wu_sprung_eigenvalues(15)
        assert np.all(np.diff(eigenvalues) > 0)
        print("✅ Test 29: Eigenvalues ordered PASSED")
    
    def test_compute_MAE_zero_for_identical(self):
        """Test 30: MAE = 0 when eigenvalues match zeros perfectly."""
        espectro = EspectroCeros()
        zeros = np.array([10.0, 20.0, 30.0])
        eigenvalues = 0.25 + zeros**2
        mae = espectro.compute_MAE(eigenvalues, zeros)
        assert np.isclose(mae, 0.0, atol=1e-10)
        print("✅ Test 30: MAE zero for identical PASSED")
    
    def test_compute_MAE_positive(self):
        """Test 31: MAE > 0 for non-identical."""
        espectro = EspectroCeros()
        zeros = np.array([10.0, 20.0, 30.0])
        eigenvalues = 0.25 + (zeros + 1)**2  # Perturbed
        mae = espectro.compute_MAE(eigenvalues, zeros)
        assert mae > 0
        print("✅ Test 31: MAE positive PASSED")
    
    def test_compute_MAE_small(self):
        """Test 32: MAE is small for good approximation."""
        espectro = EspectroCeros()
        zeros = espectro.get_reference_zeros(10)
        eigenvalues = espectro.compute_wu_sprung_eigenvalues(10)
        mae = espectro.compute_MAE(eigenvalues, zeros)
        assert mae < 0.1  # Should be very small
        print("✅ Test 32: MAE small PASSED")
    
    def test_compute_GUE_statistics_returns_tuple(self):
        """Test 33: GUE statistics returns 3-tuple."""
        espectro = EspectroCeros()
        zeros = espectro.get_reference_zeros(20)
        result = espectro.compute_GUE_statistics(zeros)
        assert isinstance(result, tuple)
        assert len(result) == 3
        print("✅ Test 33: GUE statistics tuple PASSED")
    
    def test_compute_GUE_statistics_values_range(self):
        """Test 34: GUE statistics in valid range."""
        espectro = EspectroCeros()
        zeros = espectro.get_reference_zeros(20)
        ks_stat, p_value, mean_spacing = espectro.compute_GUE_statistics(zeros)
        assert 0 <= ks_stat <= 1
        assert 0 <= p_value <= 1
        assert mean_spacing > 0
        print("✅ Test 34: GUE statistics range PASSED")
    
    def test_compute_GUE_few_zeros(self):
        """Test 35: GUE with < 2 zeros returns defaults."""
        espectro = EspectroCeros()
        zeros = np.array([14.134725])
        ks_stat, p_value, mean_spacing = espectro.compute_GUE_statistics(zeros)
        assert ks_stat == 0.0
        assert p_value == 1.0
        assert mean_spacing == 0.0
        print("✅ Test 35: GUE few zeros PASSED")
    
    def test_analizar_structure(self):
        """Test 36: analizar() returns correct structure."""
        espectro = EspectroCeros()
        result = espectro.analizar(N_operator=20)
        assert isinstance(result, EspectroCerosResult)
        assert len(result.eigenvalues) == 20
        assert len(result.reference_zeros) == 20
        print("✅ Test 36: analizar structure PASSED")
    
    def test_coherence_psi_range(self):
        """Test 37: Coherence Ψ ∈ (0, 1]."""
        espectro = EspectroCeros()
        result = espectro.analizar(N_operator=50)
        assert 0 < result.coherence_psi <= 1
        print("✅ Test 37: Coherence Ψ range PASSED")
    
    def test_coherence_psi_formula(self):
        """Test 38: Ψ = exp(-MAE)."""
        espectro = EspectroCeros()
        result = espectro.analizar(N_operator=30)
        expected_psi = np.exp(-result.MAE)
        assert np.isclose(result.coherence_psi, expected_psi, rtol=1e-10)
        print("✅ Test 38: Coherence Ψ formula PASSED")
    
    def test_espiritu_norm_positive(self):
        """Test 39: Espíritu norm ||B|| > 0."""
        espectro = EspectroCeros()
        result = espectro.analizar(N_operator=25)
        assert result.espiritu_norm > 0
        print("✅ Test 39: Espíritu norm positive PASSED")
    
    def test_espiritu_norm_formula(self):
        """Test 40: ||B|| = √(∑ t_n²)."""
        espectro = EspectroCeros()
        result = espectro.analizar(N_operator=15)
        expected_norm = np.sqrt(np.sum(result.reference_zeros**2))
        assert np.isclose(result.espiritu_norm, expected_norm, rtol=1e-10)
        print("✅ Test 40: Espíritu norm formula PASSED")


# =====================================================================
# TEST SUITE: VINCULO WEIL - 20 TESTS
# =====================================================================

class TestVinculoWeil:
    """Test suite for VinculoWeil class."""
    
    def test_init(self):
        """Test 41: VinculoWeil initialization."""
        vinculo = VinculoWeil(f0=141.7001, sigma=10.0)
        assert vinculo.f0 == 141.7001
        assert vinculo.sigma == 10.0
        assert np.isclose(vinculo.omega_0, 2 * np.pi * 141.7001, rtol=1e-10)
        print("✅ Test 41: Initialization PASSED")
    
    def test_init_default_f0(self):
        """Test 42: Default f0 = 141.7001 Hz."""
        vinculo = VinculoWeil()
        assert np.isclose(vinculo.f0, F0_QCAL, rtol=1e-10)
        print("✅ Test 42: Default f0 PASSED")
    
    def test_test_function_h_at_omega0(self):
        """Test 43: h(ω₀) = 1."""
        vinculo = VinculoWeil()
        h_at_omega0 = vinculo.test_function_h(vinculo.omega_0)
        assert np.isclose(h_at_omega0, 1.0, rtol=1e-10)
        print("✅ Test 43: h(ω₀) = 1 PASSED")
    
    def test_test_function_h_gaussian_shape(self):
        """Test 44: h(t) decreases away from ω₀."""
        vinculo = VinculoWeil(sigma=10.0)
        h_center = vinculo.test_function_h(vinculo.omega_0)
        h_left = vinculo.test_function_h(vinculo.omega_0 - 20)
        h_right = vinculo.test_function_h(vinculo.omega_0 + 20)
        assert h_center > h_left
        assert h_center > h_right
        print("✅ Test 44: Gaussian shape PASSED")
    
    def test_test_function_h_positive(self):
        """Test 45: h(t) > 0 for all t (or very small for far from ω₀)."""
        vinculo = VinculoWeil()
        for t in [vinculo.omega_0 - 50, vinculo.omega_0, vinculo.omega_0 + 50]:
            assert vinculo.test_function_h(t) >= 0  # Non-negative
        # Check that at center it's positive
        assert vinculo.test_function_h(vinculo.omega_0) > 0.9
        print("✅ Test 45: h(t) positive PASSED")
    
    def test_test_function_h_fourier_positive(self):
        """Test 46: |ĥ(r)| ≥ 0 (non-negative)."""
        vinculo = VinculoWeil()
        for r in [0, 1, 5, 10]:
            h_val = vinculo.test_function_h_fourier(r)
            assert h_val >= 0  # Non-negative
        # Check positive at r=0
        assert vinculo.test_function_h_fourier(0) > 0
        print("✅ Test 46: |ĥ(r)| positive PASSED")
    
    def test_test_function_h_fourier_at_zero(self):
        """Test 47: |ĥ(0)| = σ√(2π)."""
        vinculo = VinculoWeil(sigma=5.0)
        h_fourier_0 = vinculo.test_function_h_fourier(0)
        expected = 5.0 * np.sqrt(2 * np.pi)
        assert np.isclose(h_fourier_0, expected, rtol=1e-10)
        print("✅ Test 47: |ĥ(0)| formula PASSED")
    
    def test_test_function_h_fourier_decreases(self):
        """Test 48: |ĥ(r)| decreases with |r|."""
        vinculo = VinculoWeil()
        h0 = vinculo.test_function_h_fourier(0)
        h1 = vinculo.test_function_h_fourier(1)
        h5 = vinculo.test_function_h_fourier(5)
        assert h0 > h1 > h5
        print("✅ Test 48: |ĥ(r)| decreases PASSED")
    
    def test_sum_over_zeros_empty(self):
        """Test 49: Sum over zeros with empty array = 0."""
        vinculo = VinculoWeil()
        zeros = np.array([])
        total = vinculo.sum_over_zeros(zeros)
        assert total == 0.0
        print("✅ Test 49: Empty zeros sum PASSED")
    
    def test_sum_over_zeros_positive(self):
        """Test 50: Sum over zeros >= 0 (sum of gaussians)."""
        vinculo = VinculoWeil()
        # Use zeros near omega_0 for non-zero sum
        zeros = np.array([vinculo.omega_0 - 20, vinculo.omega_0, vinculo.omega_0 + 20])
        total = vinculo.sum_over_zeros(zeros)
        assert total >= 0
        # Check it's actually positive when zeros are near omega_0
        assert total > 1.0  # Should be around 2-3
        print("✅ Test 50: Zeros sum positive PASSED")
    
    def test_sum_over_zeros_increases_with_count(self):
        """Test 51: Sum increases with more zeros."""
        vinculo = VinculoWeil()
        zeros_5 = np.linspace(800, 900, 5)
        zeros_10 = np.linspace(800, 900, 10)
        sum_5 = vinculo.sum_over_zeros(zeros_5)
        sum_10 = vinculo.sum_over_zeros(zeros_10)
        # More zeros near ω₀ should give larger sum
        assert sum_10 > sum_5
        print("✅ Test 51: Zeros sum increases PASSED")
    
    def test_sum_over_primes_empty(self):
        """Test 52: Sum over primes with empty list ≈ 0."""
        vinculo = VinculoWeil()
        primes = []
        total = vinculo.sum_over_primes(primes)
        assert total == 0.0
        print("✅ Test 52: Empty primes sum PASSED")
    
    def test_sum_over_primes_positive(self):
        """Test 53: Sum over primes > 0."""
        vinculo = VinculoWeil()
        primes = [2, 3, 5, 7, 11, 13]
        total = vinculo.sum_over_primes(primes, N_terms=20)
        assert total > 0
        print("✅ Test 53: Primes sum positive PASSED")
    
    def test_sum_over_primes_finite(self):
        """Test 54: Sum over primes is finite."""
        vinculo = VinculoWeil()
        primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
        total = vinculo.sum_over_primes(primes, N_terms=30)
        assert np.isfinite(total)
        print("✅ Test 54: Primes sum finite PASSED")
    
    def test_evaluar_structure(self):
        """Test 55: evaluar() returns correct structure."""
        vinculo = VinculoWeil()
        zeros = np.array([100, 200, 300])
        primes = [2, 3, 5, 7, 11]
        result = vinculo.evaluar(zeros, primes)
        assert isinstance(result, VinculoWeilResult)
        assert hasattr(result, 'zero_sum')
        assert hasattr(result, 'prime_sum')
        assert hasattr(result, 'delta_Weil')
        print("✅ Test 55: evaluar structure PASSED")
    
    def test_delta_Weil_positive(self):
        """Test 56: Δ_Weil ≥ 0."""
        vinculo = VinculoWeil()
        zeros = np.linspace(800, 900, 10)
        primes = [2, 3, 5, 7, 11, 13, 17, 19, 23]
        result = vinculo.evaluar(zeros, primes)
        assert result.delta_Weil >= 0
        print("✅ Test 56: Δ_Weil positive PASSED")
    
    def test_delta_normalized_range(self):
        """Test 57: δ_Weil normalized ≥ 0."""
        vinculo = VinculoWeil()
        zeros = np.linspace(850, 950, 15)
        primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
        result = vinculo.evaluar(zeros, primes)
        assert result.delta_normalized >= 0
        print("✅ Test 57: δ_Weil normalized PASSED")
    
    def test_omega_0_value(self):
        """Test 58: ω₀ = 2π·f₀."""
        vinculo = VinculoWeil(f0=141.7001)
        zeros = np.array([100])
        primes = [2]
        result = vinculo.evaluar(zeros, primes)
        expected_omega = 2 * np.pi * 141.7001
        assert np.isclose(result.omega_0, expected_omega, rtol=1e-10)
        print("✅ Test 58: ω₀ value PASSED")
    
    def test_f0_value_in_result(self):
        """Test 59: f₀ stored correctly in result."""
        vinculo = VinculoWeil(f0=141.7001)
        zeros = np.array([100])
        primes = [2]
        result = vinculo.evaluar(zeros, primes)
        assert np.isclose(result.f0, 141.7001, rtol=1e-10)
        print("✅ Test 59: f₀ in result PASSED")
    
    def test_test_function_norm(self):
        """Test 60: Test function norm = σ√(π/2)."""
        vinculo = VinculoWeil(sigma=8.0)
        zeros = np.array([100])
        primes = [2]
        result = vinculo.evaluar(zeros, primes)
        expected_norm = 8.0 * np.sqrt(np.pi / 2)
        assert np.isclose(result.test_function_norm, expected_norm, rtol=1e-10)
        print("✅ Test 60: Test function norm PASSED")


# =====================================================================
# TEST SUITE: CIERRE ARQUITECTURA - 15 TESTS
# =====================================================================

class TestCierreArquitectura:
    """Test suite for CierreArquitectura class."""
    
    def test_init(self):
        """Test 61: CierreArquitectura initialization."""
        cierre = CierreArquitectura(precision=30)
        assert cierre.precision == 30
        assert isinstance(cierre.geometria, GeometriaPrimos)
        assert isinstance(cierre.espectro, EspectroCeros)
        assert isinstance(cierre.vinculo, VinculoWeil)
        print("✅ Test 61: Initialization PASSED")
    
    def test_integrar_structure(self):
        """Test 62: integrar() returns correct structure."""
        cierre = CierreArquitectura()
        result = cierre.integrar(primes_upto=50, N_operator=20)
        assert isinstance(result, CierreArquitecturaResult)
        assert hasattr(result, 'lado_A')
        assert hasattr(result, 'lado_B')
        assert hasattr(result, 'vinculo_Weil')
        assert hasattr(result, 'psi_global')
        print("✅ Test 62: integrar structure PASSED")
    
    def test_integrar_lado_A_present(self):
        """Test 63: Lado A results present."""
        cierre = CierreArquitectura()
        result = cierre.integrar(primes_upto=50, N_operator=20)
        assert isinstance(result.lado_A, GeometriaPrimosResult)
        assert result.lado_A.x_value > 0
        print("✅ Test 63: Lado A present PASSED")
    
    def test_integrar_lado_B_present(self):
        """Test 64: Lado B results present."""
        cierre = CierreArquitectura()
        result = cierre.integrar(primes_upto=50, N_operator=20)
        assert isinstance(result.lado_B, EspectroCerosResult)
        assert len(result.lado_B.eigenvalues) > 0
        print("✅ Test 64: Lado B present PASSED")
    
    def test_integrar_vinculo_Weil_present(self):
        """Test 65: Vínculo Weil results present."""
        cierre = CierreArquitectura()
        result = cierre.integrar(primes_upto=50, N_operator=20)
        assert isinstance(result.vinculo_Weil, VinculoWeilResult)
        assert result.vinculo_Weil.f0 > 0
        print("✅ Test 65: Vínculo Weil present PASSED")
    
    def test_psi_global_range(self):
        """Test 66: Ψ_global ∈ [0, 1]."""
        cierre = CierreArquitectura()
        result = cierre.integrar(primes_upto=100, N_operator=50)
        assert 0 <= result.psi_global <= 1
        print("✅ Test 66: Ψ_global range PASSED")
    
    def test_psi_global_formula(self):
        """Test 67: Ψ_global = min(Ψ_B, 1 - δ_Weil/2)."""
        cierre = CierreArquitectura()
        result = cierre.integrar(primes_upto=80, N_operator=30)
        psi_B = result.lado_B.coherence_psi
        psi_Weil = max(0.0, 1.0 - result.vinculo_Weil.delta_normalized / 2.0)
        expected_psi_global = min(psi_B, psi_Weil)
        assert np.isclose(result.psi_global, expected_psi_global, rtol=1e-10)
        print("✅ Test 67: Ψ_global formula PASSED")
    
    def test_verificacion_completa_logic(self):
        """Test 68: Verificación completa when Ψ_global > 0.5."""
        cierre = CierreArquitectura()
        result = cierre.integrar(primes_upto=200, N_operator=100)
        if result.psi_global > 0.5:
            assert result.verificacion_completa
        else:
            assert not result.verificacion_completa
        print("✅ Test 68: Verificación logic PASSED")
    
    def test_mensaje_when_complete(self):
        """Test 69: Correct message when verification complete."""
        cierre = CierreArquitectura()
        result = cierre.integrar(primes_upto=200, N_operator=150)
        if result.verificacion_completa:
            expected_msg = 'HECHO ESTÁ: La RH no es una duda, es una Constante de Existencia.'
            assert result.mensaje == expected_msg
        print("✅ Test 69: Complete message PASSED")
    
    def test_mensaje_when_partial(self):
        """Test 70: Correct message when verification partial."""
        cierre = CierreArquitectura()
        # Use small values to potentially get partial verification
        result = cierre.integrar(primes_upto=10, N_operator=5)
        if not result.verificacion_completa:
            assert 'Verificación parcial' in result.mensaje
            assert 'Ψ' in result.mensaje
        print("✅ Test 70: Partial message PASSED")
    
    def test_default_x_eval(self):
        """Test 71: Default x_eval = primes_upto."""
        cierre = CierreArquitectura()
        result = cierre.integrar(primes_upto=75, N_operator=20)
        assert result.lado_A.x_value == 75.0
        print("✅ Test 71: Default x_eval PASSED")
    
    def test_default_E_eval(self):
        """Test 72: Default E_eval = 100."""
        cierre = CierreArquitectura()
        result = cierre.integrar(primes_upto=50, N_operator=20)
        assert result.lado_A.E_value == 100.0
        print("✅ Test 72: Default E_eval PASSED")
    
    def test_custom_x_eval(self):
        """Test 73: Custom x_eval works."""
        cierre = CierreArquitectura()
        result = cierre.integrar(primes_upto=100, N_operator=20, x_eval=50.0)
        assert result.lado_A.x_value == 50.0
        print("✅ Test 73: Custom x_eval PASSED")
    
    def test_custom_E_eval(self):
        """Test 74: Custom E_eval works."""
        cierre = CierreArquitectura()
        result = cierre.integrar(primes_upto=100, N_operator=20, E_eval=200.0)
        assert result.lado_A.E_value == 200.0
        print("✅ Test 74: Custom E_eval PASSED")
    
    def test_reproducibility(self):
        """Test 75: Same inputs give same results."""
        cierre1 = CierreArquitectura(precision=30)
        cierre2 = CierreArquitectura(precision=30)
        
        result1 = cierre1.integrar(primes_upto=50, N_operator=20)
        result2 = cierre2.integrar(primes_upto=50, N_operator=20)
        
        assert np.isclose(result1.psi_global, result2.psi_global, rtol=1e-10)
        assert result1.verificacion_completa == result2.verificacion_completa
        print("✅ Test 75: Reproducibility PASSED")


# =====================================================================
# TEST SUITE: PUBLIC FUNCTION cierre_rh_omega() - 5 TESTS
# =====================================================================

class TestCierreRhOmegaFunction:
    """Test suite for cierre_rh_omega() public function."""
    
    def test_returns_string(self):
        """Test 76: cierre_rh_omega() returns a string."""
        msg = cierre_rh_omega(primes_upto=50, N_operator=20, verbose=False)
        assert isinstance(msg, str)
        print("✅ Test 76: Returns string PASSED")
    
    def test_returns_expected_message(self):
        """Test 77: Returns expected message format."""
        msg = cierre_rh_omega(primes_upto=200, N_operator=100, verbose=False)
        # Should be one of the two messages
        valid_messages = [
            'HECHO ESTÁ: La RH no es una duda, es una Constante de Existencia.',
            'Verificación parcial'
        ]
        assert any(valid_msg in msg for valid_msg in valid_messages)
        print("✅ Test 77: Expected message PASSED")
    
    def test_verbose_false_no_print(self, capsys):
        """Test 78: verbose=False doesn't print."""
        msg = cierre_rh_omega(primes_upto=30, N_operator=10, verbose=False)
        captured = capsys.readouterr()
        assert captured.out == ""  # No output
        print("✅ Test 78: No print when verbose=False PASSED")
    
    def test_verbose_true_prints(self, capsys):
        """Test 79: verbose=True prints output."""
        msg = cierre_rh_omega(primes_upto=30, N_operator=10, verbose=True)
        captured = capsys.readouterr()
        assert len(captured.out) > 0  # Some output
        assert "∴𓂀Ω∞³Φ" in captured.out
        assert "SISTEMA: VERIFICACIÓN DE CIERRE" in captured.out
        print("✅ Test 79: Print when verbose=True PASSED")
    
    def test_integration_with_defaults(self):
        """Test 80: Works with default parameters."""
        msg = cierre_rh_omega(verbose=False)
        assert isinstance(msg, str)
        assert len(msg) > 0
        print("✅ Test 80: Default parameters PASSED")


# =====================================================================
# RUN ALL TESTS
# =====================================================================

if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])
