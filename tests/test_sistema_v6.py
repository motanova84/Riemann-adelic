#!/usr/bin/env python3
"""
Test suite for sistema_v6.py — Sistema V6 Emisión de la Hipótesis de Riemann
=============================================================================

Tests the four V6 modules and the SistemaV6 orchestrator:
  - ModuloEtaPlus (η⁺)
  - ModuloMellin (Uᴹᵉˡˡⁱⁿ)
  - ModuloTraza (Traza^Σ)
  - NodoNZ (NZ∞³)
  - SistemaV6 (full pipeline)
  - ConstantesV6 (constants)

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: March 2026
"""

import json
import pytest
import numpy as np
from pathlib import Path

# conftest.py already adds repo root to sys.path
from sistema_v6 import (
    ConstantesV6,
    ModuloEtaPlus,
    ModuloMellin,
    ModuloTraza,
    NodoNZ,
    SistemaV6,
)


# =============================================================================
# ConstantesV6
# =============================================================================

class TestConstantesV6:
    """Tests for the V6 constants."""

    def test_sello_v6_present(self):
        assert ConstantesV6.SELLO_V6 == "∴𓂀Ω∞³Φ✧"

    def test_sello_nz_present(self):
        assert ConstantesV6.SELLO_NZ == "∴NZ∞³∴"

    def test_version(self):
        assert ConstantesV6.VERSION == "V6"

    def test_frecuencia_base(self):
        assert abs(ConstantesV6.FRECUENCIA_BASE - 141.7001) < 1e-4

    def test_condicion_rh(self):
        assert "1/2" in ConstantesV6.CONDICION_RH

    def test_interpretacion_rh_nonempty(self):
        assert len(ConstantesV6.INTERPRETACION_RH) > 0


# =============================================================================
# ModuloEtaPlus
# =============================================================================

class TestModuloEtaPlus:
    """Tests for η⁺ module."""

    def setup_method(self):
        self.modulo = ModuloEtaPlus()

    def test_encontrar_estado_base_returns_dict(self):
        result = self.modulo.encontrar_estado_base()
        assert isinstance(result, dict)

    def test_expectacion_key_present(self):
        result = self.modulo.encontrar_estado_base()
        assert "⟨η⟩_ψ₀" in result

    def test_expectacion_positive(self):
        result = self.modulo.encontrar_estado_base()
        assert result["⟨η⟩_ψ₀"] > 0.0

    def test_es_positivo_true(self):
        result = self.modulo.encontrar_estado_base()
        assert result["es_positivo"] is True

    def test_expectacion_bounded(self):
        """⟨η⟩ must be in (0, 1] for a normalised state and η ≤ 1."""
        result = self.modulo.encontrar_estado_base()
        assert 0.0 < result["⟨η⟩_ψ₀"] <= 1.0

    def test_proyectar_fantasmas(self):
        result = self.modulo.proyectar_fantasmas()
        assert result.get("proyeccion_fantasmas") == "ACTIVA"

    def test_ejecutar_returns_dict(self):
        result = self.modulo.ejecutar()
        assert isinstance(result, dict)

    def test_ejecutar_estado_sellado(self):
        result = self.modulo.ejecutar()
        assert result["estado"] == "🔒"

    def test_ejecutar_modulo_name(self):
        result = self.modulo.ejecutar()
        assert result["modulo"] == "η⁺"

    def test_ejecutar_funcion_ontologica(self):
        result = self.modulo.ejecutar()
        assert "Vacío" in result["funcion_ontologica"]


# =============================================================================
# ModuloMellin
# =============================================================================

class TestModuloMellin:
    """Tests for Uᴹᵉˡˡⁱⁿ module."""

    def setup_method(self):
        self.modulo = ModuloMellin()

    def test_unitariedad_true(self):
        assert self.modulo.verificar_unitariedad() is True

    def test_conmutacion_true(self):
        assert self.modulo.verificar_conmutacion() is True

    def test_ejecutar_returns_dict(self):
        result = self.modulo.ejecutar()
        assert isinstance(result, dict)

    def test_ejecutar_estado_fluyendo(self):
        result = self.modulo.ejecutar()
        assert result["estado"] == "🌊"

    def test_ejecutar_modulo_name(self):
        result = self.modulo.ejecutar()
        assert result["modulo"] == "Uᴹᵉˡˡⁱⁿ"

    def test_invariancia_haar(self):
        result = self.modulo.ejecutar()
        assert "Haar" in result["invariancia"]

    def test_dualidad_pontryagin(self):
        result = self.modulo.ejecutar()
        assert result["dualidad"] == "Pontryagin"


# =============================================================================
# ModuloTraza
# =============================================================================

class TestModuloTraza:
    """Tests for Traza^Σ module."""

    def setup_method(self):
        self.modulo = ModuloTraza()

    def test_orbitas_primos_bijection(self):
        assert self.modulo.verificar_orbitas() is True

    def test_traza_is_complex(self):
        traza = self.modulo.calcular_traza()
        assert isinstance(traza, complex)

    def test_traza_finite(self):
        traza = self.modulo.calcular_traza()
        assert np.isfinite(traza.real) and np.isfinite(traza.imag)

    def test_primos_log_distinct(self):
        lengths = [np.log(p) for p in ModuloTraza.PRIMOS]
        rounded = [round(l, 8) for l in lengths]
        assert len(set(rounded)) == len(rounded)

    def test_primos_log_positive(self):
        for p in ModuloTraza.PRIMOS:
            assert np.log(p) > 0.0

    def test_ejecutar_returns_dict(self):
        result = self.modulo.ejecutar()
        assert isinstance(result, dict)

    def test_ejecutar_estado_exacta(self):
        result = self.modulo.ejecutar()
        assert result["estado"] == "✅"

    def test_ejecutar_modulo_name(self):
        result = self.modulo.ejecutar()
        assert result["modulo"] == "Traza^Σ"

    def test_ejecutar_orbitas_primitivas_logp(self):
        result = self.modulo.ejecutar()
        assert result["propiedades"]["orbitas_primitivas"] == "log p"


# =============================================================================
# NodoNZ
# =============================================================================

class TestNodoNZ:
    """Tests for NZ∞³ node."""

    def setup_method(self):
        self.nodo = NodoNZ()

    def test_activar_true_when_modulos_ok(self):
        assert self.nodo.activar(modulos_ok=True) is True

    def test_activar_false_when_modulos_fail(self):
        assert self.nodo.activar(modulos_ok=False) is False

    def test_emitir_rh_returns_dict(self):
        result = self.nodo.emitir_rh()
        assert isinstance(result, dict)

    def test_emitir_rh_estado(self):
        result = self.nodo.emitir_rh()
        assert result["estado"] == "⚡"

    def test_emitir_rh_condicion(self):
        result = self.nodo.emitir_rh()
        assert "1/2" in result["punto_emision"]

    def test_emitir_rh_frecuencia(self):
        result = self.nodo.emitir_rh()
        assert abs(result["frecuencia_base_hz"] - 141.7001) < 1e-4

    def test_emitir_rh_hipotesis_demostrada(self):
        result = self.nodo.emitir_rh()
        assert result["hipotesis_riemann"]["estado"] == "DEMOSTRADA"

    def test_emitir_rh_sello(self):
        result = self.nodo.emitir_rh()
        assert result["sello"] == "∴NZ∞³∴"

    def test_ejecutar_returns_tuple(self):
        result = self.nodo.ejecutar(modulos_ok=True)
        assert isinstance(result, tuple) and len(result) == 2

    def test_ejecutar_estado_activo(self):
        nodo_res, _ = self.nodo.ejecutar(modulos_ok=True)
        assert nodo_res["estado"] == "⚡"


# =============================================================================
# SistemaV6
# =============================================================================

class TestSistemaV6:
    """Tests for the full SistemaV6 pipeline."""

    def setup_method(self):
        self.sistema = SistemaV6()

    def test_ejecutar_returns_dict(self):
        result = self.sistema.ejecutar()
        assert isinstance(result, dict)

    def test_ejecutar_version(self):
        result = self.sistema.ejecutar()
        assert result["version"] == "V6"

    def test_ejecutar_estado_global(self):
        result = self.sistema.ejecutar()
        assert result["estado_global"] == "⚡"

    def test_ejecutar_modulos_present(self):
        result = self.sistema.ejecutar()
        modulos = result["modulos"]
        assert "η⁺" in modulos
        assert "Uᴹᵉˡˡⁱⁿ" in modulos
        assert "Traza^Σ" in modulos

    def test_ejecutar_nodo_nz_present(self):
        result = self.sistema.ejecutar()
        assert "nodo_nz" in result

    def test_ejecutar_emision_rh_present(self):
        result = self.sistema.ejecutar()
        assert "emision_rh" in result

    def test_ejecutar_sello(self):
        result = self.sistema.ejecutar()
        assert result["sello"] == "∴𓂀Ω∞³Φ✧"

    def test_ejecutar_emision_rh_hipotesis(self):
        result = self.sistema.ejecutar()
        assert result["emision_rh"]["hipotesis_riemann"]["estado"] == "DEMOSTRADA"

    def test_ejecutar_json_serializable(self):
        """Results must be JSON-serialisable."""
        result = self.sistema.ejecutar()
        serialised = json.dumps(result, ensure_ascii=False)
        recovered = json.loads(serialised)
        assert recovered["version"] == "V6"

    def test_mostrar_tabla_emision_no_error(self, capsys):
        """mostrar_tabla_emision should print without raising exceptions."""
        self.sistema.ejecutar()
        self.sistema.mostrar_tabla_emision()
        captured = capsys.readouterr()
        assert "NZ∞³" in captured.out
        assert "η⁺" in captured.out

    def test_mostrar_tabla_emision_contains_activo(self, capsys):
        self.sistema.ejecutar()
        self.sistema.mostrar_tabla_emision()
        captured = capsys.readouterr()
        assert "ACTIVO" in captured.out

    def test_mostrar_tabla_emision_contains_sellado(self, capsys):
        self.sistema.ejecutar()
        self.sistema.mostrar_tabla_emision()
        captured = capsys.readouterr()
        assert "SELLADO" in captured.out


# =============================================================================
# Integration: main() function
# =============================================================================

class TestMain:
    """Integration tests for the main() entry point."""

    def test_main_returns_dict(self, tmp_path, monkeypatch):
        """main() should return a dict and write resultados_v6.json."""
        monkeypatch.chdir(tmp_path)
        from sistema_v6 import main
        result = main()
        assert isinstance(result, dict)
        assert result["version"] == "V6"

    def test_main_writes_json_file(self, tmp_path, monkeypatch):
        """main() should write resultados_v6.json."""
        monkeypatch.chdir(tmp_path)
        from sistema_v6 import main
        main()
        json_file = tmp_path / "resultados_v6.json"
        assert json_file.exists()
        data = json.loads(json_file.read_text(encoding="utf-8"))
        assert data["version"] == "V6"
        assert "sello" in data


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
