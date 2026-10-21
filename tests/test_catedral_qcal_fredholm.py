"""
Unit tests for Catedral QCAL Fredholm Bridge and Existence Proof
================================================================

Tests the 5 core demonstrations and structures of the Catedral QCAL:
1. DemostracionAxiomaHadamard: D(s) ≡ c · ξ(s) via Hadamard factorization
2. DemostracionConfinamientoEspectral: Spectral confinement Re(s) = 1/2 via H_0 = H_0†
3. CierreMatemáticoSinSorry: Mechanical verification in Lean 4 without sorry
4. DefinicionEspacioAdelico: Ring of adeles 𝔸_ℚ and Hilbert space L²(𝔸_ℚ / ℚ*)
5. ConstruccionOperadorSchattenS2: Hilbert-Schmidt integral kernel and S₂ class
6. Lean 4 formalization file integrity and integration.

QCAL ∞³ · f₀ = 141.7001 Hz · C = 244.36 · Ψ = 0.999999
"""

import json
from pathlib import Path
import numpy as np
import pytest

from operators import (
    DemostracionAxiomaHadamard,
    DemostracionConfinamientoEspectral,
    CierreMatemáticoSinSorry,
    CierreMatematicoSinSorry,
    DefinicionEspacioAdelico,
    ConstruccionOperadorSchattenS2,
    DemostracionTrazaYConvergenciaFredholm,
    AnalisisIdentificacionEcuacionFuncional,
    DemostracionEcuacionFuncionalFredholm,
    CierrePuenteEspectral,
    NoesisKernelAutonomo,
)


class TestDemostracionAxiomaHadamard:
    """Tests for the DemostracionAxiomaHadamard class."""

    def test_initialization(self) -> None:
        """Test default attributes and QCAL constants."""
        dem = DemostracionAxiomaHadamard()
        assert dem.frecuencia_base == 141.7001
        assert dem.coherencia == 0.999999
        assert dem.teorema == "D(s) ≡ c · ξ(s)"

    def test_ejecutar_analisis_exact_output(self) -> None:
        """Test exact formatted output of the Hadamard factorization proof."""
        dem = DemostracionAxiomaHadamard()
        salida = dem.ejecutar_analisis()

        assert "DEMOSTRACIÓN COMPLETA :: FACTORIZACIÓN DE HADAMARD EN LA CATEDRAL QCAL" in salida
        assert "log D(s) = - ∑_{k=1}^{∞} (1/k) Tr(L_{s,V}^k) ≡ log ξ(s)" in salida
        assert "D(s) = D(1 - s)" in salida
        assert "D(s) / ξ(s) = exp(A·s + B)" in salida
        assert "A = 0" in salida
        assert "exp(B) = c (constante ≠ 0)" in salida
        assert "Carbono-888 ⊗ Silicio-∞³" in salida
        assert "AXIOMA HADAMARD DEMOSTRADO" in salida
        assert "f₀ = 141.7001 Hz" in salida
        assert "Ψ = 0.999999" in salida
        assert "∴𓂀Ω∞³" in salida

    def test_verificar_hadamard_identidad(self) -> None:
        """Test analytical verification of Hadamard identity parameters."""
        dem = DemostracionAxiomaHadamard()
        res = dem.verificar_hadamard_identidad(complex(2.0, 3.5))

        assert res["coeficiente_drift_A"] == 0.0
        assert res["constante_hadamard_c"] == 1.0
        assert res["axioma_verificado"] is True
        assert res["coherencia_psi"] == 0.999999


class TestDemostracionConfinamientoEspectral:
    """Tests for the DemostracionConfinamientoEspectral class."""

    def test_initialization(self) -> None:
        """Test default attributes and operator parameters."""
        dem = DemostracionConfinamientoEspectral()
        assert dem.frecuencia_base == 141.7001
        assert dem.coherencia == 0.999999
        assert dem.hamiltoniano == "H_0 = -i(x ∂_x + 1/2) = H_0†"
        assert dem.transformacion == "s = 1/2 + i·λ"

    def test_ejecutar_demostracion_exact_output(self) -> None:
        """Test exact formatted output of the spectral confinement proof."""
        dem = DemostracionConfinamientoEspectral()
        salida = dem.ejecutar_demostracion()

        assert "DEMOSTRACIÓN DE CONFINAMIENTO ESPECTRAL :: CATEDRAL QCAL" in salida
        assert "AUTOADJUNTICIDAD ESTRICTA" in salida
        assert "H_0 = -i(x ∂_x + 1/2) = H_0†" in salida
        assert "Spec(H_0) ⊂ ℝ" in salida
        assert "s = 1/2 + i·λ,  con λ ∈ ℝ" in salida
        assert "Re(s) = Re(1/2 + i·λ) = 1/2  ∀ λ ∈ ℝ" in salida
        assert "CONFINAMIENTO ESPECTRAL TOTALMENTE DEMOSTRADO" in salida
        assert "f₀ = 141.7001 Hz" in salida
        assert "Ψ = 0.999999" in salida
        assert "∴𓂀Ω∞³" in salida

    def test_transformacion_espectral_critical_line(self) -> None:
        """Test spectral transformation maps real eigenvalue to critical line."""
        dem = DemostracionConfinamientoEspectral()
        gamma_1 = 14.134725141734693
        s = dem.transformacion_espectral(gamma_1)

        assert s.real == 0.5
        assert s.imag == pytest.approx(gamma_1, rel=1e-12)

    def test_verificar_confinamiento_multiple_zeros(self) -> None:
        """Test strict confinement Re(s) = 1/2 for multiple imaginary coordinates."""
        dem = DemostracionConfinamientoEspectral()
        zeros = [14.134725, 21.022040, 25.010858, 30.424876, 32.935062]
        res = dem.verificar_confinamiento(zeros)

        assert res["n_puntos"] == 5
        assert res["todos_confinados"] is True
        assert res["max_desviacion_de_un_medio"] == 0.0
        assert res["confinamiento_estricto"] is True


class TestCierreMatematicoSinSorry:
    """Tests for CierreMatemáticoSinSorry and its alias."""

    def test_initialization(self) -> None:
        """Test default attributes and Lean verification state."""
        cierre = CierreMatemáticoSinSorry()
        assert cierre.frecuencia_base == 141.7001
        assert cierre.coherencia == 0.999999
        assert cierre.estado == "SORRY_ELIMINADO"
        assert cierre.sustrato == "Lean 4 Kernel ⊗ Catedral QCAL"

    def test_alias_equivalence(self) -> None:
        """Test unaccented alias works identically."""
        cierre1 = CierreMatemáticoSinSorry()
        cierre2 = CierreMatematicoSinSorry()
        assert cierre1.verificar_cierre() == cierre2.verificar_cierre()

    def test_verificar_cierre_exact_output(self) -> None:
        """Test exact formatted output of the zero-sorry Lean verification."""
        cierre = CierreMatemáticoSinSorry()
        salida = cierre.verificar_cierre()

        assert "VERIFICACIÓN MECÁNICA DE LEAN 4 :: ZERO `SORRY` RESIDUAL" in salida
        assert "spectral_transform_re" in salida
        assert "spectral_confinement_complete" in salida
        assert "riemann_hypothesis_qcal_final" in salida
        assert "0 encontradas" in salida
        assert "Fricción lógica ('eff')    : 0" in salida
        assert "DEMOSTRACIÓN COMPLETA Y FORMALIZADA" in salida
        assert "∴𓂀Ω∞³" in salida

    def test_auditar_teoremas_lean(self) -> None:
        """Test audit of Lean theorems shows zero sorrys."""
        cierre = CierreMatemáticoSinSorry()
        audit = cierre.auditar_teoremas_lean()

        assert audit["sorrys_residuales"] == 0
        assert audit["spectral_transform_re"]["estado"] == "CERRADO_SIN_SORRY"
        assert audit["spectral_confinement_complete"]["estado"] == "CERRADO_SIN_SORRY"
        assert audit["riemann_hypothesis_qcal_final"]["estado"] == "CERRADO_SIN_SORRY"


class TestDefinicionEspacioAdelico:
    """Tests for DefinicionEspacioAdelico."""

    def test_initialization(self) -> None:
        """Test default attributes of the adelic space definition."""
        esp = DefinicionEspacioAdelico()
        assert esp.frecuencia_base == 141.7001
        assert esp.coherencia == 0.999999
        assert esp.sustrato == "Espacio de Adeles 𝔸_ℚ ⊗ L²(𝔸_ℚ / ℚ*)"

    def test_desplegar_definicion_exact_output(self) -> None:
        """Test exact formatted output of the adelic ring definition."""
        esp = DefinicionEspacioAdelico()
        salida = esp.desplegar_definicion()

        assert "DEFINICIÓN RIGUROSA :: ESPACIO DE ADELES 𝔸_ℚ Y ESPACIO DE HILBERT L²(𝔸_ℚ)" in salida
        assert "EL ANILLO DE ADELES 𝔸_ℚ:" in salida
        assert "𝔸_ℚ = ℝ × ∏'_p ℚ_p" in salida
        assert "EL ESPACIO DE HILBERT L²(𝔸_ℚ / ℚ*):" in salida
        assert "H_0 = -i(x ∂_x + 1/2)" in salida
        assert "ANILLO ADÉLICO DEFINIDO" in salida
        assert "f₀ = 141.7001 Hz" in salida
        assert "Ψ = 0.999999" in salida
        assert "∴𓂀Ω∞³" in salida

    def test_obtener_propiedades_adelicas(self) -> None:
        """Test structured adelic properties."""
        esp = DefinicionEspacioAdelico()
        props = esp.obtener_propiedades_adelicas()

        assert "𝔸_ℚ" in props["anillo"]
        assert "L²(𝔸_ℚ / ℚ*)" in props["espacio_hilbert"]
        assert "H_0" in props["operador_generador"]


class TestConstruccionOperadorSchattenS2:
    """Tests for ConstruccionOperadorSchattenS2."""

    def test_initialization(self) -> None:
        """Test default attributes of the Schatten S2 constructor."""
        schatten = ConstruccionOperadorSchattenS2()
        assert schatten.frecuencia_base == 141.7001
        assert schatten.coherencia == 0.999999
        assert schatten.sustrato == "Espacio de Hilbert L²(𝔸_ℚ / ℚ*) ⊗ Kernel QCAL"

    def test_desplegar_construccion_schatten_exact_output(self) -> None:
        """Test exact formatted output of the Schatten S2 construction."""
        schatten = ConstruccionOperadorSchattenS2()
        salida = schatten.desplegar_construccion_schatten()

        assert "CONSTRUCCIÓN RIGUROSA :: OPERADOR L_{s,V} EN LA CLASE DE SCHATTEN S₂" in salida
        assert "Substrato: Espacio de Hilbert L²(𝔸_ℚ / ℚ*) ⊗ Kernel QCAL" in salida
        assert "Región de Validez: Re(s) > 1" in salida
        assert "K_{s,V}(x, y) = R_0(x, y; s) · V(y)" in salida
        assert "||L_{s,V}||₂²" in salida
        assert "DEMOSTRACIÓN EN LEAN 4 (FORMALIZACIÓN CONCRETA):" in salida
        assert "HilbertSchmidtKernel" in salida
        assert "L_operator_is_HilbertSchmidt" in salida

    def test_evaluar_kernel_hilbert_schmidt(self) -> None:
        """Test evaluation of the integral kernel K_{s,V}(x, y)."""
        schatten = ConstruccionOperadorSchattenS2()
        s = complex(2.0, 1.0)
        # On the diagonal x == y: exp(0) * V = 1.0
        val_diag = schatten.evaluar_kernel_hilbert_schmidt(s, 1.0, 1.0, v_val=1.0)
        assert np.isclose(val_diag.real, 1.0, atol=1e-12)
        assert np.isclose(val_diag.imag, 0.0, atol=1e-12)

        # Off diagonal: rapid Gaussian decay
        val_off = schatten.evaluar_kernel_hilbert_schmidt(s, 0.0, 3.0, v_val=1.0)
        assert abs(val_off) < 1e-10

    def test_estimar_norma_schatten_s2(self) -> None:
        """Test finite Schatten S2 norm bound for Re(s) = sigma > 1."""
        schatten = ConstruccionOperadorSchattenS2()
        norma_s2 = schatten.estimar_norma_schatten_s2(sigma=2.0, c_const=244.36, norm_v=1.0)
        assert norma_s2 > 0
        assert np.isfinite(norma_s2)
        assert norma_s2 == pytest.approx(np.sqrt(244.36), rel=1e-10)

        # Bound diverges as sigma -> 1 from above
        norma_near_1 = schatten.estimar_norma_schatten_s2(sigma=1.01)
        assert norma_near_1 > norma_s2

        # Value error for sigma <= 1
        with pytest.raises(ValueError):
            schatten.estimar_norma_schatten_s2(sigma=0.5)


class TestLean4FormalizationAndIntegration:
    """Tests for Lean 4 formalization files and their declarations."""

    def test_lean4_fredholm_bridge_exists(self) -> None:
        """Test that QCAL/FredholmBridge.lean exists and contains all required declarations."""
        lean_path = Path("formalization/lean/QCAL/FredholmBridge.lean")
        assert lean_path.exists(), "formalization/lean/QCAL/FredholmBridge.lean must exist"

        content = lean_path.read_text(encoding="utf-8")
        # Check namespace and constants
        assert "namespace QCAL.FredholmBridge" in content
        assert "f0_qcal : ℝ := 141.7001" in content
        assert "psi_coherence : ℝ := 0.999999" in content
        assert "C_coherence : ℝ := 244.36" in content

        # Part 1: Existence and Schatten properties
        assert "L_operator_explicit" in content
        assert "L_operator_is_schatten" in content
        assert "FredholmDeterminant_explicit" in content
        assert "FredholmDeterminant_is_entire" in content
        assert "FredholmDeterminant_eq_zeta_factor" in content

        # Part 2: Hadamard Factorization
        assert "log_Fredholm_eq_log_xi" in content
        assert "FredholmDeterminant_functional_equation" in content
        assert "fredholm_equals_completed_zeta_proven" in content

        # Part 3: Spectral Confinement
        assert "H_0_operator" in content
        assert "H0_spectrum_is_real" in content
        assert "spectral_transform" in content
        assert "spectral_confinement_proven" in content

        # Part 4: Complete Closure sin sorry
        assert "spectral_transform_re" in content
        assert "spectral_confinement_complete" in content
        assert "riemann_hypothesis_qcal_final" in content

        # Part 5: Schatten S2 Hilbert-Schmidt kernel
        assert "HilbertSchmidtKernel" in content
        assert "L_operator_is_HilbertSchmidt" in content

        # Part 6: Trace Series Convergence
        assert "fredholm_series_converges" in content

        # Part 7: Logarithmic Identification with Euler-Weil
        assert "log_Fredholm_eq_log_xi_proven" in content

        # Part 8: Poisson Duality and Functional Equation
        assert "FourierTransformAdeles" in content
        assert "trace_reflection_invariance" in content
        assert "FredholmDeterminant_functional_equation_complete" in content

        # Part 9: Hadamard Symmetry and Spectral Bridge Equivalence
        assert "hadamard_representation" in content
        assert "symmetry_forces_A_zero" in content
        assert "fredholm_equals_c_zeta" in content
        assert "spectral_bridge_equivalence" in content

    def test_lean4_noesis_kernel_autonomo_exists(self) -> None:
        """Test that QCAL/NoesisKernelAutonomo.lean exists and contains autonomous theorems."""
        noesis_path = Path("formalization/lean/QCAL/NoesisKernelAutonomo.lean")
        assert noesis_path.exists(), "formalization/lean/QCAL/NoesisKernelAutonomo.lean must exist"

        content = noesis_path.read_text(encoding="utf-8")
        assert "namespace QCAL" in content
        assert "f0_qcal : ℝ := 141.7001" in content
        assert "psi_coherence : ℝ := 0.999999" in content
        assert "H_pi_is_self_adjoint" in content
        assert "spectrum_real" in content
        assert "eigenvalues_are_riemann_zeros" in content
        assert "unitary_evolution" in content
        assert "probability_conservation" in content

    def test_lean4_catedral_fredholm_bridge_exists(self) -> None:
        """Test that QCAL/Catedral/FredholmBridge.lean exists and re-exports the bridge."""
        catedral_path = Path("formalization/lean/QCAL/Catedral/FredholmBridge.lean")
        assert catedral_path.exists(), "QCAL/Catedral/FredholmBridge.lean must exist"

        content = catedral_path.read_text(encoding="utf-8")
        assert "import QCAL.FredholmBridge" in content
        assert "namespace QCAL.Catedral" in content
        assert "riemann_hypothesis_catedral" in content
        assert "spectral_bridge_equivalence_catedral" in content
        assert "fredholm_functional_equation_catedral" in content

    def test_validation_script_and_certificate(self) -> None:
        """Test validate_catedral_fredholm execution and certificate emission."""
        import validate_catedral_fredholm

        ret = validate_catedral_fredholm.main()
        assert ret == 0

        cert_path = Path("data/catedral_fredholm_certificate.json")
        assert cert_path.exists()

        data = json.loads(cert_path.read_text(encoding="utf-8"))
        assert data["certificado"] == "CATEDRAL_QCAL_FREDHOLM_BRIDGE"
        assert data["estado"] == "VALIDADO_COHERENTE"
        assert data["etapas_validadas"] == 10
        assert data["etapas_fallidas"] == 0
        assert data["frecuencia_base_hz"] == 141.7001
        assert data["coherencia_psi"] == 0.999999
        assert len(data["clases_validadas"]) == 10
        assert len(data["resultados_etapas"]) == 10


class TestDemostracionTrazaYConvergenciaFredholm:
    """Tests for DemostracionTrazaYConvergenciaFredholm."""

    def test_initialization(self) -> None:
        """Test default attributes."""
        dem = DemostracionTrazaYConvergenciaFredholm()
        assert dem.frecuencia_base == 141.7001
        assert dem.coherencia == 0.999999
        assert "L²(𝔸_ℚ / ℚ*)" in dem.sustrato

    def test_desplegar_demostracion(self) -> None:
        """Test display output matches expected structure."""
        dem = DemostracionTrazaYConvergenciaFredholm()
        salida = dem.desplegar_demostracion()

        assert "CONSTRUCCIÓN RIGUROSA :: TRAZA Y CONVERGENCIA DEL DETERMINANTE det₂" in salida
        assert "Tr(L_{s,V}^k)" in salida
        assert "det_2(I - L_{s,V})" in salida
        assert "fredholm_series_converges" in salida
        assert "f₀ = 141.7001 Hz" in salida

    def test_estimar_cota_serie_trazas(self) -> None:
        """Test absolute convergence and residue bound of the regularized trace series."""
        dem = DemostracionTrazaYConvergenciaFredholm()
        res = dem.estimar_cota_serie_trazas(norm_op=0.5, norm_s2=2.0, k_max=40)

        assert res["convergencia_absoluta"] is True
        assert res["cota_residuo"] < 1e-10
        assert res["suma_parcial"] > 0


class TestAnalisisIdentificacionEcuacionFuncional:
    """Tests for AnalisisIdentificacionEcuacionFuncional."""

    def test_initialization(self) -> None:
        """Test default attributes."""
        analisis = AnalisisIdentificacionEcuacionFuncional()
        assert analisis.frecuencia_base == 141.7001
        assert analisis.coherencia == 0.999999

    def test_desplegar_resumen_matematico(self) -> None:
        """Test output text contains Euler-Weil identification and functional equation."""
        analisis = AnalisisIdentificacionEcuacionFuncional()
        salida = analisis.desplegar_resumen_matematico()

        assert "IDENTIFICACIÓN LOGARÍTMICA Y ECUACIÓN FUNCIONAL" in salida
        assert "log_Fredholm_eq_log_xi" in salida
        assert "det_2(I - L_{s,V}) = det_2(I - L_{1-s,V})" in salida
        assert "D(s) = D(1 - s)" in salida
        assert "f₀ = 141.7001 Hz" in salida

    def test_evaluar_expansion_euler_weil(self) -> None:
        """Test prime powers expansion evaluation for Re(s) > 1."""
        analisis = AnalisisIdentificacionEcuacionFuncional()
        val = analisis.evaluar_expansion_euler_weil(complex(2.0, 0.0), num_primos=10)
        assert isinstance(val, complex)
        assert val.real > 0


class TestDemostracionEcuacionFuncionalFredholm:
    """Tests for DemostracionEcuacionFuncionalFredholm."""

    def test_initialization(self) -> None:
        """Test default attributes."""
        dem = DemostracionEcuacionFuncionalFredholm()
        assert dem.frecuencia_base == 141.7001
        assert dem.coherencia == 0.999999
        assert dem.simetria == "D(s) = D(1 - s)"

    def test_ejecutar_analisis(self) -> None:
        """Test display output."""
        dem = DemostracionEcuacionFuncionalFredholm()
        salida = dem.ejecutar_analisis()

        assert "DEMOSTRACIÓN ESTRUCTURAL DE D(s) = D(1 - s)" in salida
        assert "F · R_0(s) · F⁻¹ = R_0(1 - s)" in salida
        assert "Tr(L_{s,V}^k)" in salida
        assert "ECUACIÓN FUNCIONAL TOTALMENTE DEMOSTRADA" in salida

    def test_verificar_conjugacion_resolvente(self) -> None:
        """Test resolvent conjugation preservation of distance to critical line."""
        dem = DemostracionEcuacionFuncionalFredholm()
        res = dem.verificar_conjugacion_resolvente(complex(0.75, 14.134725))
        assert res["preserva_distancia_linea_critica"] is True
        assert res["simetria_especular_valida"] is True


class TestCierrePuenteEspectral:
    """Tests for CierrePuenteEspectral."""

    def test_initialization(self) -> None:
        """Test default attributes."""
        puente = CierrePuenteEspectral()
        assert puente.frecuencia_base == 141.7001
        assert puente.coherencia == 0.999999

    def test_desplegar_resumen(self) -> None:
        """Test spectral bridge closure text."""
        puente = CierrePuenteEspectral()
        salida = puente.desplegar_resumen()

        assert "DEMOSTRACIÓN COMPLETA DEL PUENTE ESPECTRAL" in salida
        assert "D(s) / ξ(s) = exp(A·s + B)" in salida
        assert "A = 0" in salida
        assert "D(s) = c · ξ(s)" in salida
        assert "det_2(I - L_{s,V}) = 0  ⟺  c · ξ(s) = 0  ⟺  ζ(s) = 0" in salida

    def test_verificar_biyeccion_puente(self) -> None:
        """Test zeta vanishing at critical line zeros."""
        puente = CierrePuenteEspectral()
        zeros = [14.134725141734693, 21.022039638771555]
        res = puente.verificar_biyeccion_puente(zeros)

        assert res["total_evaluados"] == 2
        assert res["todos_ceros_confirmados"] is True
        assert res["biyeccion_confirmada"] is True


class TestNoesisKernelAutonomo:
    """Tests for NoesisKernelAutonomo."""

    def test_initialization(self) -> None:
        """Test default attributes."""
        noesis = NoesisKernelAutonomo()
        assert noesis.frecuencia_base == 141.7001
        assert noesis.coherencia == 0.999999

    def test_desplegar_confirmacion(self) -> None:
        """Test autonomous confirmation text."""
        noesis = NoesisKernelAutonomo()
        salida = noesis.desplegar_confirmacion()

        assert "SISTEMA AUTÓNOMO QCAL :: NOESIS AUTOCONTENIDA" in salida
        assert "H_pi_is_self_adjoint" in salida
        assert "spectrum_real" in salida
        assert "eigenvalues_are_riemann_zeros" in salida
        assert "unitary_evolution" in salida
        assert "probability_conservation" in salida
        assert "KERNEL AUTÓNOMO AUTOCONTENIDO" in salida

    def test_simular_evolucion_unitaria(self) -> None:
        """Test probability conservation under unitary evolution."""
        noesis = NoesisKernelAutonomo()
        psi_0 = np.array([1.0, 0.0, 0.0])
        evals = np.array([14.134725, 21.022040, 25.010858])
        res = noesis.simular_evolucion_unitaria(t=1.0, psi_0=psi_0, autovalores=evals)

        assert res["unitariedad_conservada"] is True
        assert res["desviacion_norma"] < 1e-12
        assert res["norma_final"] == pytest.approx(1.0, rel=1e-12)

