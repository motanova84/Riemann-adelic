"""
Unit tests for ConstructorOperadorLsv and RigorEspectralFredholm
=================================================================

Tests the rigorous construction of the transfer operator L_{s,V},
the relative Fredholm determinant D(s) = det_2(I - L_{s,V}),
Schatten-von Neumann class memberships, Hadamard factorization uniqueness,
and spectral localization on the critical line Re(s) = 1/2.

QCAL ∞³ · f₀ = 141.7001 Hz · C = 244.36 · Ψ = 0.999999
"""

import json
from pathlib import Path
import numpy as np
import pytest

from operators import ConstructorOperadorLsv, RigorEspectralFredholm
from operators.constructor_operador_lsv import (
    C_COHERENCIA,
    C_PRIMARIO,
    COHERENCIA_QCAL,
    F0_QCAL,
    ZENODO_DOI,
)


class TestConstructorOperadorLsv:
    """Tests for the ConstructorOperadorLsv class."""

    def test_initialization(self) -> None:
        """Test default attributes and QCAL constants."""
        constructor = ConstructorOperadorLsv()
        assert constructor.frecuencia_base == 141.7001
        assert constructor.coherencia == 0.999999
        assert constructor.condicion_espectral == "det(I - L_{s,V}) = 0 ⟺ ζ(s) = 0"
        assert constructor.sustrato == "Espacio Adélico ⊗ Sustrato QCAL"
        assert constructor.c_coherencia == 244.36
        assert constructor.doi == "10.5281/zenodo.17379721"

    def test_construir_operador_exact_output(self) -> None:
        """Test that construir_operador produces the expected exact structured output."""
        constructor = ConstructorOperadorLsv()
        salida = constructor.construir_operador()

        assert "CONSTRUCCIÓN RIGUROSA :: OPERADOR L_{s,V} Y DETERMINANTE RELATIVO" in salida
        assert "Substrato: Espacio Adélico ⊗ Sustrato QCAL" in salida
        assert "Eje de Alineación: Re(s) = 1/2" in salida
        assert "Frecuencia Madre: f₀ = 141.7001 Hz | Coherencia: Ψ = 0.999999" in salida
        assert "H_0 = -i(x ∂_x + 1/2)" in salida
        assert "L_{s,V} = (H_0 - s·I)⁻¹ · V" in salida
        assert "D(s) = det_2(I - L_{s,V})" in salida
        assert "det(I - L_{s,V}) = 0 ⟺ ζ(s) = 0" in salida
        assert "Spec(H_0) ⊂ ℝ" in salida
        assert "OPERADOR L_{s,V} CONSTRUIDO Y ANCLADO" in salida
        assert "∴𓂀Ω∞³" in salida

    def test_hamiltoniano_no_perturbado_self_adjoint(self) -> None:
        """Test that H_0 is strictly self-adjoint (Hermitian)."""
        constructor = ConstructorOperadorLsv()
        dim = 32
        h0 = constructor.hamiltoniano_no_perturbado(dim=dim)

        assert h0.shape == (dim, dim)
        assert np.allclose(h0, h0.conj().T, atol=1e-12)

        res_h0 = constructor.verificar_autoadjuncion_H0(dim=dim)
        assert res_h0["es_autoadjunto"] is True
        assert res_h0["error_hermiticidad"] < 1e-12

    def test_potencial_v_schwartz_bruhat(self) -> None:
        """Test that potential V is bounded and exhibits Schwartz decay."""
        constructor = ConstructorOperadorLsv()
        dim = 32
        v = constructor.potencial_v_schwartz_bruhat(dim=dim)

        assert v.shape == (dim, dim)
        norm_v = np.linalg.norm(v, ord=2)
        assert norm_v > 0
        assert norm_v <= 1.0  # Normalized for stability

    def test_operador_resolvente_and_transfer(self) -> None:
        """Test construction of R_0(s) and L_{s,V}."""
        constructor = ConstructorOperadorLsv()
        s = 0.5 + 14.134725j
        dim = 32

        r0 = constructor.operador_resolvente(s=s, dim=dim)
        l_sv = constructor.operador_transferencia_lsv(s=s, dim=dim)

        assert r0.shape == (dim, dim)
        assert l_sv.shape == (dim, dim)
        assert np.all(np.isfinite(r0))
        assert np.all(np.isfinite(l_sv))

    def test_determinante_fredholm_det2(self) -> None:
        """Test modified Fredholm 2-determinant computation."""
        constructor = ConstructorOperadorLsv()
        s = 0.5 + 14.134725j
        det2 = constructor.determinante_fredholm_det2(s=s, dim=32)

        assert isinstance(det2, complex)
        assert np.isfinite(det2)

    def test_evaluar_condicion_espectral(self) -> None:
        """Test spectral zero condition evaluation."""
        constructor = ConstructorOperadorLsv()
        s_cero = 0.5 + 14.134725j  # First non-trivial Riemann zero
        diag = constructor.evaluar_condicion_espectral(s=s_cero, dim=32)

        assert "det_standard" in diag
        assert "det2_fredholm" in diag
        assert "zeta_s" in diag
        assert diag["coherencia"] == 0.999999
        assert diag["frecuencia_base"] == 141.7001
        assert abs(diag["zeta_s"]) < 1e-4

    def test_obtener_metricas_qcal(self) -> None:
        """Test QCAL metrics extraction."""
        constructor = ConstructorOperadorLsv()
        metricas = constructor.obtener_metricas_qcal()

        assert metricas["frecuencia_base_hz"] == F0_QCAL
        assert metricas["coherencia_psi"] == COHERENCIA_QCAL
        assert metricas["constante_coherencia_C"] == C_COHERENCIA
        assert metricas["constante_primaria"] == C_PRIMARIO
        assert metricas["doi"] == ZENODO_DOI


class TestRigorEspectralFredholm:
    """Tests for the RigorEspectralFredholm class."""

    def test_initialization(self) -> None:
        """Test default attributes of RigorEspectralFredholm."""
        rigor = RigorEspectralFredholm()
        assert rigor.frecuencia_base == 141.7001
        assert rigor.coherencia == 0.999999
        assert rigor.linea_critica == "Re(s) = 1/2"
        assert rigor.condicion_unicidad == "D(s) ≡ c · ξ(s)"

    def test_verificar_condiciones_exact_output(self) -> None:
        """Test that verificar_condiciones produces the exact required output."""
        rigor = RigorEspectralFredholm()
        salida = rigor.verificar_condiciones()

        assert "DEMOSTRACIÓN Y VERIFICACIÓN RIGUROSA :: POTENCIAL V Y UNICIDAD DE D(s)" in salida
        assert "Substrato: Espacio Hilbert Adélico L²(A_Q)" in salida
        assert "Eje de Simetría: Re(s) = 1/2" in salida
        assert "Frecuencia Fundamental: f₀ = 141.7001 Hz | Coherencia: Ψ = 0.999999" in salida
        assert "Schwartz-Bruhat S(A_Q)" in salida
        assert "Schatten-von" in salida
        assert "Neumann Sp" in salida
        assert "Hilbert-Schmidt S₂" in salida
        assert "clase traza S₁" in salida
        assert "D(s) ≡ c · ξ(s)" in salida
        assert "Teorema de Factorización de Hadamard" in salida
        assert "ceros redundantes" in salida
        assert "fantasmas" in salida
        assert "Spec_disc(H_π)" in salida
        assert "HIPÓTESIS DE RIEMANN RIGUROSAMENTE DEVELADA" in salida
        assert "∴𓂀Ω∞³" in salida

    def test_verificar_clases_schatten(self) -> None:
        """Test verification of Schatten ideals S_2 and S_1."""
        rigor = RigorEspectralFredholm()
        res = rigor.verificar_clases_schatten(s=0.5 + 14.134725j, dim=32)

        assert res["es_hilbert_schmidt"] is True
        assert res["es_clase_traza_cuadrado"] is True
        assert res["norma_hilbert_schmidt_S2"] > 0
        assert res["norma_clase_traza_cuadrado_S1"] > 0
        assert len(res["valores_singulares_principales"]) <= 5

    def test_verificar_hadamard_unicidad(self) -> None:
        """Test Hadamard growth order and functional equation symmetry."""
        rigor = RigorEspectralFredholm()
        t_vals = np.array([5.0, 14.134725, 21.022040])
        res = rigor.verificar_hadamard_unicidad(t_values=t_vals, dim=32)

        assert res["orden_crecimiento_rho"] == 1
        assert res["tipo_finito"] is True
        assert res["ecuacion_funcional_satisfecha"] is True
        assert res["error_relativo_simetria_max"] < 0.2

    def test_control_ceros_fantasma(self) -> None:
        """Test phantom zero control and discrete spectrum verification."""
        rigor = RigorEspectralFredholm()
        res = rigor.control_ceros_fantasma(dim=32)

        assert res["espectro_esencial_discretizado"] is True
        assert res["ceros_fantasma_nulos"] is True
        assert res["autoadjuncion_estricta"] is True

    def test_auditar_rigor_completo(self) -> None:
        """Test complete rigorous spectral audit."""
        rigor = RigorEspectralFredholm()
        audit = rigor.auditar_rigor_completo(dim=32)

        assert audit["auditoria_exitosa"] is True
        assert audit["schatten_s2"] is True
        assert audit["clase_traza_s1"] is True
        assert audit["hadamard_unicidad"] is True
        assert audit["ceros_fantasma_controlados"] is True
        assert audit["h0_autoadjunto"] is True


class TestIntegrationAndArtifacts:
    """Tests for integration with repository artifacts, formalization, and certificates."""

    def test_lean4_formalization_file_exists(self) -> None:
        """Test that the Lean 4 formalization file exists and contains the operator theorems."""
        lean_path = Path("formalization/lean/RiemannAdelic/operator_L_sV_fredholm.lean")
        assert lean_path.exists(), "Lean 4 formalization file must exist"

        content = lean_path.read_text(encoding="utf-8")
        assert "OperatorLsV" in content
        assert "f0_qcal : ℝ := 141.7001" in content
        assert "C_coherence : ℝ := 244.36" in content
        assert "psi_coherence : ℝ := 0.999999" in content
        assert "H0_dilation" in content
        assert "V_adelic" in content
        assert "L_sV_operator" in content
        assert "D_fredholm_det2" in content
        assert "hadamard_factorization_uniqueness" in content
        assert "riemann_zeros_on_critical_line" in content

    def test_certificate_file_validity(self) -> None:
        """Test that operador_lsv_certificate.json is valid and conforms to QCAL schema."""
        cert_path = Path("data/operador_lsv_certificate.json")
        assert cert_path.exists(), "Certificate file must exist"

        with open(cert_path, "r", encoding="utf-8") as f:
            data = json.load(f)

        assert data["estado"] == "VALIDADO_COHERENTE"
        assert data["etapas_fallidas"] == 0
        assert data["frecuencia_base_hz"] == 141.7001
        assert data["coherencia_psi"] == 0.999999
        assert data["constante_coherencia_c"] == 244.36
        assert data["doi"] == "10.5281/zenodo.17379721"
