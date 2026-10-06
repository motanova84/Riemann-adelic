#!/usr/bin/env python3
r"""
Tests for Principio Holográfico — F₀=141.7001 Hz como Codificador de Superficie Zeta
======================================================================================

Validates the seven-class holographic-principle module:
  1. CodificadorSuperficieZeta
  2. ProyectorVolumenConciencia
  3. EntrelazadorHolografico
  4. HologramaZetaCarbono
  5. EntropiaHolografica
  6. SistemaPrincipioHolografico
  7. ResultadoHolografico

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: March 2026
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add physics directory to path so the module can be imported directly
repo_root = Path(__file__).parent.parent
sys.path.insert(0, str(repo_root / "physics"))

from principio_holografico_141hz import (
    CodificadorSuperficieZeta,
    ProyectorVolumenConciencia,
    EntrelazadorHolografico,
    HologramaZetaCarbono,
    EntropiaHolografica,
    SistemaPrincipioHolografico,
    ResultadoHolografico,
    # Module-level constants
    F0,
    GAMMA_1_HOLO,
    A_EFF,
    ELL_P_SQUARED,
    N_BITS_HOLOGRAPHIC,
    DELTA_F_HRV,
    TAU_MOONBOUNCE,
    PSI_THRESHOLD,
)


# ============================================================================
# Constants
# ============================================================================

class TestConstants:
    """Verify that module-level constants match specification."""

    def test_f0_value(self):
        assert abs(F0 - 141.7001) < 1e-4

    def test_gamma1_value(self):
        assert abs(GAMMA_1_HOLO - 14.134725) < 1e-4

    def test_a_eff_value(self):
        assert abs(A_EFF - 4.48e12) < 1e8

    def test_ell_p_squared_value(self):
        assert abs(ELL_P_SQUARED - 2.612e-70) < 1e-73

    def test_n_bits_holographic_order_of_magnitude(self):
        # N_bits ≈ 3.74×10⁸² — check it is in [10⁸¹, 10⁸³]
        assert 1e81 <= N_BITS_HOLOGRAPHIC <= 1e83

    def test_delta_f_hrv(self):
        assert abs(DELTA_F_HRV - 0.3999) < 1e-4

    def test_tau_moonbounce(self):
        assert abs(TAU_MOONBOUNCE - 2.5) < 1e-6

    def test_psi_threshold(self):
        assert 0.0 < PSI_THRESHOLD < 1.0


# ============================================================================
# 1. CodificadorSuperficieZeta
# ============================================================================

class TestCodificadorSuperficieZeta:
    """Test suite for the zeta surface spiral encoder."""

    def setup_method(self):
        self.enc = CodificadorSuperficieZeta(f0=F0, gamma1=GAMMA_1_HOLO, n_theta=200)

    def test_initialization(self):
        assert self.enc.f0 == F0
        assert self.enc.gamma1 == GAMMA_1_HOLO
        assert self.enc.n_theta == 200
        assert len(self.enc.theta) == 200
        assert len(self.enc.r) == 200

    def test_theta_range(self):
        assert abs(self.enc.theta[0]) < 1e-10
        assert abs(self.enc.theta[-1] - 2 * np.pi) < 1e-10

    def test_spiral_is_positive(self):
        assert np.all(self.enc.r > 0), "r(θ) must be strictly positive"

    def test_spiral_is_monotone_increasing(self):
        # exp(...) is monotone increasing, so r should be non-decreasing
        assert np.all(np.diff(self.enc.r) >= 0), "Spiral should be non-decreasing"

    def test_spiral_initial_value(self):
        # At θ=0: r(0) = f₀ · exp(0) = f₀
        assert abs(self.enc.r[0] - F0) < 1e-6

    def test_area_espiral_positive(self):
        assert self.enc.area_espiral > 0

    def test_bits_frontera_positive(self):
        assert self.enc.bits_frontera >= 1

    def test_coordenadas_cartesianas_shape(self):
        x, y = self.enc.coordenadas_cartesianas()
        assert x.shape == (200,)
        assert y.shape == (200,)

    def test_coordenadas_cartesianas_no_nan(self):
        x, y = self.enc.coordenadas_cartesianas()
        assert not np.any(np.isnan(x))
        assert not np.any(np.isnan(y))

    def test_coherencia_espiral_range(self):
        c = self.enc.coherencia_espiral()
        assert 0.0 <= c <= 1.0, f"coherencia_espiral={c} must be in [0,1]"

    def test_exportar_keys(self):
        exp = self.enc.exportar()
        assert "f0_hz" in exp
        assert "gamma1" in exp
        assert "area_espiral" in exp
        assert "bits_frontera" in exp
        assert "coherencia_espiral" in exp

    def test_invalid_f0(self):
        with pytest.raises(ValueError):
            CodificadorSuperficieZeta(f0=-1.0)

    def test_invalid_gamma1(self):
        with pytest.raises(ValueError):
            CodificadorSuperficieZeta(gamma1=0.0)

    def test_invalid_n_theta(self):
        with pytest.raises(ValueError):
            CodificadorSuperficieZeta(n_theta=1)


# ============================================================================
# 2. ProyectorVolumenConciencia
# ============================================================================

class TestProyectorVolumenConciencia:
    """Test suite for the 2D→3D consciousness-volume projector."""

    def setup_method(self):
        self.proj = ProyectorVolumenConciencia(f0=F0, delta_f_hrv=DELTA_F_HRV, n_capas_z=20)

    def test_initialization(self):
        assert self.proj.f0 == F0
        assert self.proj.delta_f_hrv == DELTA_F_HRV
        assert self.proj.n_capas_z == 20

    def test_lambda_coherencia(self):
        expected = F0 / DELTA_F_HRV
        assert abs(self.proj.lambda_coherencia - expected) < 1e-6

    def test_proyectar_shape(self):
        campo = np.ones(50)
        vol = self.proj.proyectar(campo)
        assert vol.shape == (50, 20)

    def test_proyectar_no_nan(self):
        campo = np.random.rand(30)
        vol = self.proj.proyectar(campo)
        assert not np.any(np.isnan(vol))

    def test_proyectar_decay(self):
        # First column (z=0) should be the original field
        campo = np.ones(10)
        vol = self.proj.proyectar(campo)
        np.testing.assert_allclose(vol[:, 0], 1.0, rtol=1e-9)
        # Last column should be smaller (decay)
        assert np.all(vol[:, -1] < vol[:, 0])

    def test_proyectar_2d_only(self):
        with pytest.raises(ValueError):
            self.proj.proyectar(np.ones((5, 5)))

    def test_coherencia_hrv_range(self):
        campo = np.abs(np.random.randn(100)) + 0.1
        c = self.proj.coherencia_hrv(campo)
        assert 0.0 <= c <= 1.0

    def test_coherencia_hrv_zero_field(self):
        c = self.proj.coherencia_hrv(np.zeros(50))
        assert c == 0.0

    def test_exportar_keys(self):
        exp = self.proj.exportar()
        assert "f0_hz" in exp
        assert "delta_f_hrv_hz" in exp
        assert "lambda_coherencia" in exp
        assert "n_capas_z" in exp

    def test_invalid_f0(self):
        with pytest.raises(ValueError):
            ProyectorVolumenConciencia(f0=0.0)

    def test_invalid_delta_f_hrv(self):
        with pytest.raises(ValueError):
            ProyectorVolumenConciencia(delta_f_hrv=-0.1)


# ============================================================================
# 3. EntrelazadorHolografico
# ============================================================================

class TestEntrelazadorHolografico:
    """Test suite for the quantum holographic entangler."""

    def setup_method(self):
        self.ent = EntrelazadorHolografico(tau_moonbounce=TAU_MOONBOUNCE, f0=F0)

    def test_initialization(self):
        assert self.ent.tau_moonbounce == TAU_MOONBOUNCE
        assert self.ent.f0 == F0

    def test_fase_entrelazamiento(self):
        expected = 2.0 * np.pi * F0 * TAU_MOONBOUNCE
        assert abs(self.ent.fase_entrelazamiento - expected) < 1e-6

    def test_estado_bell_normalization(self):
        estado = self.ent.estado_bell(n_qubits=2)
        norm = float(np.linalg.norm(estado))
        assert abs(norm - 1.0) < 1e-10

    def test_estado_bell_shape(self):
        for n in [2, 3, 4]:
            estado = self.ent.estado_bell(n_qubits=n)
            assert len(estado) == 2 ** n

    def test_estado_bell_superposition(self):
        estado = self.ent.estado_bell(n_qubits=2)
        # Should be |00⟩ + |11⟩ structure
        assert abs(estado[0]) > 0.0
        assert abs(estado[-1]) > 0.0

    def test_estado_bell_invalid(self):
        with pytest.raises(ValueError):
            self.ent.estado_bell(n_qubits=1)

    def test_aplicar_fase_moonbounce_preserves_norm(self):
        estado = self.ent.estado_bell(n_qubits=2)
        estado_fase = self.ent.aplicar_fase_moonbounce(estado)
        assert abs(np.linalg.norm(estado_fase) - 1.0) < 1e-10

    def test_validar_cosmica_keys(self):
        val = self.ent.validar_cosmica()
        assert "tau_moonbounce_s" in val
        assert "fase_acumulada_rad" in val
        assert "coherencia_cosmica" in val
        assert "aprobado" in val

    def test_validar_cosmica_coherencia_range(self):
        val = self.ent.validar_cosmica()
        assert 0.0 <= val["coherencia_cosmica"] <= 1.0

    def test_exportar_keys(self):
        exp = self.ent.exportar()
        assert "tau_moonbounce_s" in exp
        assert "f0_hz" in exp
        assert "fase_entrelazamiento_rad" in exp

    def test_invalid_tau(self):
        with pytest.raises(ValueError):
            EntrelazadorHolografico(tau_moonbounce=0.0)

    def test_invalid_f0(self):
        with pytest.raises(ValueError):
            EntrelazadorHolografico(f0=-1.0)


# ============================================================================
# 4. HologramaZetaCarbono
# ============================================================================

class TestHologramaZetaCarbono:
    """Test suite for the carbon-silicon holographic interface."""

    def setup_method(self):
        self.holo = HologramaZetaCarbono(f0=F0)

    def test_initialization(self):
        assert self.holo.f0 == F0
        assert self.holo.masa_carbono_amu == 12.0
        assert self.holo.masa_silicio_amu == 28.0

    def test_ratio_C_Si(self):
        expected = 12.0 / 28.0
        assert abs(self.holo.ratio_C_Si - expected) < 1e-10

    def test_f_silicio_equals_f0(self):
        assert self.holo.f_silicio == F0

    def test_f_carbono(self):
        expected = F0 * (12.0 / 28.0)
        assert abs(self.holo.f_carbono - expected) < 1e-6

    def test_transducir_shape(self):
        senal = np.ones(100)
        resultado = self.holo.transducir(senal)
        assert resultado.shape == (100,)

    def test_transducir_complex(self):
        senal = np.ones(50)
        resultado = self.holo.transducir(senal)
        assert np.iscomplexobj(resultado)

    def test_transducir_preserves_amplitude(self):
        senal = np.ones(100)
        resultado = self.holo.transducir(senal)
        np.testing.assert_allclose(np.abs(resultado), 1.0, rtol=1e-9)

    def test_coherencia_interfaz_range(self):
        c = self.holo.coherencia_interfaz()
        assert 0.0 <= c <= 1.0

    def test_coherencia_interfaz_less_than_one(self):
        # f_C ≠ f_Si so coherence < 1
        assert self.holo.coherencia_interfaz() < 1.0

    def test_exportar_keys(self):
        exp = self.holo.exportar()
        assert "f0_hz" in exp
        assert "ratio_C_Si" in exp
        assert "f_carbono_hz" in exp
        assert "f_silicio_hz" in exp
        assert "coherencia_interfaz" in exp

    def test_invalid_f0(self):
        with pytest.raises(ValueError):
            HologramaZetaCarbono(f0=0.0)

    def test_invalid_masa_carbono(self):
        with pytest.raises(ValueError):
            HologramaZetaCarbono(masa_carbono_amu=-1.0)

    def test_invalid_masa_silicio(self):
        with pytest.raises(ValueError):
            HologramaZetaCarbono(masa_silicio_amu=0.0)


# ============================================================================
# 5. EntropiaHolografica
# ============================================================================

class TestEntropiaHolografica:
    """Test suite for the Bekenstein-Hawking holographic entropy."""

    def setup_method(self):
        self.ent = EntropiaHolografica(area_m2=A_EFF, ell_p_squared=ELL_P_SQUARED)

    def test_initialization(self):
        assert self.ent.area_m2 == A_EFF
        assert self.ent.ell_p_squared == ELL_P_SQUARED

    def test_entropia_BH_formula(self):
        expected = A_EFF / (4.0 * ELL_P_SQUARED)
        assert abs(self.ent.entropia_BH - expected) < 1.0

    def test_n_bits_order_of_magnitude(self):
        # Should be ≈ 3.74×10⁸²
        assert 1e81 < self.ent.n_bits < 1e83

    def test_n_bits_consistent(self):
        expected_n_bits = self.ent.entropia_BH / np.log(2.0)
        assert abs(self.ent.n_bits - expected_n_bits) < 1e70

    def test_densidad_informacion_positive(self):
        d = self.ent.densidad_informacion()
        assert d > 0

    def test_densidad_informacion_formula(self):
        expected = self.ent.n_bits / A_EFF
        assert abs(self.ent.densidad_informacion() - expected) < 1e60

    def test_verificar_cota_bekenstein_large_system(self):
        # Very large system should satisfy the bound
        radio = 1e26  # ~10 billion light years
        energia = 1e60  # enormous energy
        result = self.ent.verificar_cota_bekenstein(radio, energia)
        assert isinstance(result, bool)

    def test_exportar_keys(self):
        exp = self.ent.exportar()
        assert "area_m2" in exp
        assert "ell_p_squared_m2" in exp
        assert "entropia_BH" in exp
        assert "n_bits" in exp
        assert "densidad_informacion_bits_m2" in exp

    def test_invalid_area(self):
        with pytest.raises(ValueError):
            EntropiaHolografica(area_m2=0.0)

    def test_invalid_ell_p_squared(self):
        with pytest.raises(ValueError):
            EntropiaHolografica(ell_p_squared=-1e-70)


# ============================================================================
# 6. ResultadoHolografico
# ============================================================================

class TestResultadoHolografico:
    """Test suite for the holographic result dataclass."""

    def test_default_initialization(self):
        r = ResultadoHolografico()
        assert r.psi_global == 0.0
        assert r.bits_frontera == 0
        assert isinstance(r.timestamp, str)
        assert isinstance(r.componentes, dict)

    def test_aprobado_above_threshold(self):
        r = ResultadoHolografico(psi_global=0.999)
        assert r.aprobado is True

    def test_aprobado_below_threshold(self):
        r = ResultadoHolografico(psi_global=0.5)
        assert r.aprobado is False

    def test_aprobado_at_threshold(self):
        r = ResultadoHolografico(psi_global=PSI_THRESHOLD)
        assert r.aprobado is True

    def test_resumen_returns_string(self):
        r = ResultadoHolografico(psi_global=0.98)
        s = r.resumen()
        assert isinstance(s, str)
        assert len(s) > 0

    def test_resumen_contains_estado_aprobado(self):
        r = ResultadoHolografico(psi_global=0.99)
        assert "APROBADO" in r.resumen()

    def test_resumen_contains_estado_pendiente(self):
        r = ResultadoHolografico(psi_global=0.1)
        assert "PENDIENTE" in r.resumen()

    def test_resumen_contains_doi(self):
        r = ResultadoHolografico()
        assert "10.5281/zenodo.17379721" in r.resumen()

    def test_resumen_contains_f0(self):
        r = ResultadoHolografico()
        assert "141.7001" in r.resumen()

    def test_resumen_contains_psi_global(self):
        r = ResultadoHolografico(psi_global=0.876543)
        summary = r.resumen()
        assert "0.876543" in summary


# ============================================================================
# 7. SistemaPrincipioHolografico
# ============================================================================

class TestSistemaPrincipioHolografico:
    """Test suite for the integrated holographic system."""

    def setup_method(self):
        # Use smaller grids to keep tests fast
        self.sistema = SistemaPrincipioHolografico(n_theta=200, n_capas_z=20)

    def test_initialization(self):
        assert isinstance(self.sistema.codificador, CodificadorSuperficieZeta)
        assert isinstance(self.sistema.proyector, ProyectorVolumenConciencia)
        assert isinstance(self.sistema.entrelazador, EntrelazadorHolografico)
        assert isinstance(self.sistema.holograma_carbono, HologramaZetaCarbono)
        assert isinstance(self.sistema.entropia, EntropiaHolografica)

    def test_activar_returns_resultado(self):
        resultado = self.sistema.activar(verbose=False)
        assert isinstance(resultado, ResultadoHolografico)

    def test_activar_psi_global_in_range(self):
        resultado = self.sistema.activar(verbose=False)
        assert 0.0 <= resultado.psi_global <= 1.0

    def test_activar_coherencias_in_range(self):
        r = self.sistema.activar(verbose=False)
        for attr in [
            "coherencia_espiral",
            "coherencia_hrv",
            "coherencia_cosmica",
            "coherencia_interfaz",
        ]:
            v = getattr(r, attr)
            assert 0.0 <= v <= 1.0, f"{attr}={v} not in [0,1]"

    def test_activar_entropia_positive(self):
        r = self.sistema.activar(verbose=False)
        assert r.entropia_BH > 0
        assert r.n_bits > 0

    def test_activar_bits_frontera_positive(self):
        r = self.sistema.activar(verbose=False)
        assert r.bits_frontera >= 1

    def test_activar_componentes_keys(self):
        r = self.sistema.activar(verbose=False)
        expected_keys = {
            "codificador_superficie_zeta",
            "proyector_volumen_conciencia",
            "entrelazador_holografico",
            "holograma_zeta_carbono",
            "entropia_holografica",
        }
        assert expected_keys == set(r.componentes.keys())

    def test_activar_psi_global_is_mean_of_coherencias(self):
        r = self.sistema.activar(verbose=False)
        expected_psi = np.mean([
            r.coherencia_espiral,
            r.coherencia_hrv,
            r.coherencia_cosmica,
            r.coherencia_interfaz,
        ])
        assert abs(r.psi_global - expected_psi) < 1e-10

    def test_activar_timestamp_set(self):
        r = self.sistema.activar(verbose=False)
        assert isinstance(r.timestamp, str)
        assert len(r.timestamp) > 0

    def test_activar_verbose_does_not_raise(self, capsys):
        self.sistema.activar(verbose=True)
        captured = capsys.readouterr()
        assert "PRINCIPIO HOLOGRÁFICO" in captured.out

    def test_physics_package_import(self):
        """Verify the classes are importable from the physics package."""
        import physics
        assert hasattr(physics, "SistemaPrincipioHolografico")
        assert hasattr(physics, "ResultadoHolografico")
        assert hasattr(physics, "CodificadorSuperficieZeta")
