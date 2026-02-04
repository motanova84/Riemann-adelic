#!/usr/bin/env python3
"""
Tests para el Modelo de Flujo Citoplasmático
============================================

Valida que el modelo biofísico funcione correctamente y mantenga
coherencia con QCAL ∞³ y f₀ = 141.7001 Hz.

Autor: José Manuel Mota Burruezo Ψ ✧ ∞³
Fecha: 2026-01-31
"""

import sys
from pathlib import Path
import numpy as np

# Añadir el directorio del módulo al path
sys.path.insert(0, str(Path(__file__).parent.parent / "teoria_principal"))

from cytoplasmic_flow_model import (
    CytoplasmicFlowModel,
    F0_HZ,
    C_COHERENCE,
    DELTA_ZETA
)


class TestCytoplasmicFlowModel:
    """Suite de tests para el modelo de flujo citoplasmático."""
    
    def test_reynolds_number_stokes_regime(self):
        """
        Test: El número de Reynolds debe ser Re ≪ 1 (régimen Stokes).
        """
        model = CytoplasmicFlowModel()
        Re = model.calculate_reynolds_number()
        
        # Verificar que Re < 1e-3 (régimen Stokes)
        assert Re < 1e-3, f"Reynolds number {Re} no está en régimen Stokes"
        
        # Verificar que Re ~ 10⁻⁸ como esperado
        assert 1e-10 < Re < 1e-5, f"Reynolds number {Re} fuera del rango esperado"
        
        print(f"✅ Test Reynolds: Re = {Re:.2e} → Régimen Stokes verificado")
    
    def test_stokes_regime_verification(self):
        """
        Test: El método verify_stokes_regime debe retornar True.
        """
        model = CytoplasmicFlowModel()
        is_stokes = model.verify_stokes_regime()
        
        assert is_stokes is True, "Régimen Stokes no verificado"
        
        print("✅ Test Stokes: Régimen verificado correctamente")
    
    def test_hermitian_operator_hermiticity(self):
        """
        Test: El operador H = -ν∇² debe ser hermítico.
        
        Verifica que <φ|H|ψ> = <ψ|H|φ>*
        """
        model = CytoplasmicFlowModel()
        is_hermitian, error = model.verify_hermiticity()
        
        assert is_hermitian == True, f"Operador no hermítico (error={error})"
        assert error < 1e-6, f"Error de hermiticidad demasiado grande: {error}"
        
        print(f"✅ Test Hermiticidad: Operador hermítico (error={error:.2e})")
    
    def test_resonance_frequencies(self):
        """
        Test: Las frecuencias resonantes deben ser fₙ = n · f₀.
        """
        model = CytoplasmicFlowModel()
        frequencies = model.calculate_resonance_frequencies(5)
        
        # Verificar que hay 5 frecuencias
        assert len(frequencies) == 5, f"Esperadas 5 frecuencias, obtenidas {len(frequencies)}"
        
        # Verificar que cada frecuencia es n * f₀
        for i, freq in enumerate(frequencies, start=1):
            expected = i * F0_HZ
            assert abs(freq - expected) < 1e-6, f"f{i}={freq} ≠ {expected}"
        
        print(f"✅ Test Frecuencias: f₁={frequencies[0]:.4f} Hz, ..., f₅={frequencies[4]:.4f} Hz")
    
    def test_coherence_psi_calculation(self):
        """
        Test: El cálculo de coherencia Ψ debe dar valores válidos.
        """
        model = CytoplasmicFlowModel()
        
        # Test con parámetros perfectos
        psi = model.calculate_coherence_psi(I=1.0, A_eff=1.0)
        assert 0.0 <= psi <= 1.0, f"Coherencia {psi} fuera de rango [0,1]"
        
        # Para parámetros normalizados, esperamos Ψ ≈ 1.0
        assert psi > 0.9, f"Coherencia {psi} demasiado baja"
        
        print(f"✅ Test Coherencia: Ψ = {psi:.6f} → Máxima coherencia")
    
    def test_hermitian_operator_1d(self):
        """
        Test: El operador hermítico debe funcionar en 1D.
        """
        model = CytoplasmicFlowModel()
        
        # Función de onda de prueba (onda sinusoidal)
        n = 100
        x = np.linspace(0, 2*np.pi, n)
        psi = np.sin(x)
        
        # Aplicar operador
        H_psi = model.hermitian_operator(psi, dx=2*np.pi/n)
        
        # Verificar que el resultado tiene la forma correcta
        assert H_psi.shape == psi.shape, "Forma incorrecta del resultado"
        
        # Verificar que no hay NaN o Inf
        assert not np.any(np.isnan(H_psi)), "Resultado contiene NaN"
        assert not np.any(np.isinf(H_psi)), "Resultado contiene Inf"
        
        print("✅ Test Operador 1D: Funciona correctamente")
    
    def test_hermitian_operator_2d(self):
        """
        Test: El operador hermítico debe funcionar en 2D.
        """
        model = CytoplasmicFlowModel()
        
        # Función de onda de prueba 2D
        n = 50
        x = np.linspace(0, 2*np.pi, n)
        y = np.linspace(0, 2*np.pi, n)
        X, Y = np.meshgrid(x, y)
        psi = np.sin(X) * np.sin(Y)
        
        # Aplicar operador
        H_psi = model.hermitian_operator(psi, dx=2*np.pi/n)
        
        # Verificar forma
        assert H_psi.shape == psi.shape, "Forma incorrecta del resultado 2D"
        
        # Verificar que no hay NaN o Inf
        assert not np.any(np.isnan(H_psi)), "Resultado 2D contiene NaN"
        assert not np.any(np.isinf(H_psi)), "Resultado 2D contiene Inf"
        
        print("✅ Test Operador 2D: Funciona correctamente")
    
    def test_hermitian_operator_3d(self):
        """
        Test: El operador hermítico debe funcionar en 3D.
        """
        model = CytoplasmicFlowModel()
        
        # Función de onda de prueba 3D (más pequeña para eficiencia)
        n = 20
        x = np.linspace(0, 2*np.pi, n)
        y = np.linspace(0, 2*np.pi, n)
        z = np.linspace(0, 2*np.pi, n)
        X, Y, Z = np.meshgrid(x, y, z, indexing='ij')
        psi = np.sin(X) * np.sin(Y) * np.sin(Z)
        
        # Aplicar operador
        H_psi = model.hermitian_operator(psi, dx=2*np.pi/n)
        
        # Verificar forma
        assert H_psi.shape == psi.shape, "Forma incorrecta del resultado 3D"
        
        # Verificar que no hay NaN o Inf
        assert not np.any(np.isnan(H_psi)), "Resultado 3D contiene NaN"
        assert not np.any(np.isinf(H_psi)), "Resultado 3D contiene Inf"
        
        print("✅ Test Operador 3D: Funciona correctamente")
    
    def test_validation_report_generation(self):
        """
        Test: El reporte de validación debe generarse correctamente.
        """
        model = CytoplasmicFlowModel()
        report = model.generate_validation_report()
        
        # Verificar estructura del reporte
        assert "titulo" in report, "Falta título en reporte"
        assert "regimen_flujo" in report, "Falta régimen_flujo en reporte"
        assert "operador_hermitico" in report, "Falta operador_hermitico en reporte"
        assert "conexion_riemann" in report, "Falta conexion_riemann en reporte"
        assert "frecuencias_resonantes_Hz" in report, "Falta frecuencias_resonantes_Hz en reporte"
        assert "estado_vibracional" in report, "Falta estado_vibracional en reporte"
        assert "resultado" in report, "Falta resultado en reporte"
        
        # Verificar contenido clave
        assert report["regimen_flujo"]["stokes_verified"] is True
        assert report["operador_hermitico"]["hermiticidad_verificada"] is True
        assert report["conexion_riemann"]["verificada"] is True
        assert report["resultado"]["resonancia_celular_confirmada"] is True
        assert report["resultado"]["citoplasma_es_resonador_riemann"] is True
        
        print("✅ Test Reporte: Generado correctamente con todos los campos")
    
    def test_qcal_constants_integration(self):
        """
        Test: Verificar que las constantes QCAL estén correctamente integradas.
        """
        model = CytoplasmicFlowModel()
        
        # Verificar f₀
        assert model.f0 == F0_HZ, f"f₀ incorrecta: {model.f0} ≠ {F0_HZ}"
        assert abs(F0_HZ - 141.7001) < 1e-6, f"F0_HZ incorrecta: {F0_HZ}"
        
        # Verificar δζ
        assert abs(DELTA_ZETA - 0.2787437) < 1e-7, f"δζ incorrecta: {DELTA_ZETA}"
        
        # Verificar C
        assert abs(C_COHERENCE - 244.36) < 1e-2, f"C incorrecta: {C_COHERENCE}"
        
        print(f"✅ Test QCAL: f₀={F0_HZ} Hz, δζ={DELTA_ZETA}, C={C_COHERENCE}")
    
    def test_biological_parameters_realistic(self):
        """
        Test: Los parámetros biológicos deben estar en rangos realistas.
        """
        model = CytoplasmicFlowModel()
        
        # Verificar viscosidad (citoplasma: ~1-100 mPa·s)
        assert 1e-4 < model.nu < 0.1, f"Viscosidad {model.nu} fuera de rango biológico"
        
        # Verificar densidad (células: ~1000-1100 kg/m³)
        assert 1000 < model.rho < 1200, f"Densidad {model.rho} fuera de rango biológico"
        
        # Verificar tamaño celular (típico: 5-50 μm)
        assert 1e-6 < model.L < 100e-6, f"Radio celular {model.L} fuera de rango biológico"
        
        # Verificar velocidad (flujo citoplasmático: ~0.1-10 μm/s)
        assert 1e-10 < model.V < 1e-5, f"Velocidad {model.V} fuera de rango biológico"
        
        print("✅ Test Parámetros Biológicos: Todos en rangos realistas")


def run_all_tests():
    """Ejecuta todos los tests y muestra un resumen."""
    print("=" * 70)
    print("🧪 SUITE DE TESTS – MODELO DE FLUJO CITOPLASMÁTICO")
    print("=" * 70)
    print()
    
    # Crear suite de tests
    test_suite = TestCytoplasmicFlowModel()
    
    # Lista de métodos de test
    test_methods = [
        method for method in dir(test_suite)
        if method.startswith('test_') and callable(getattr(test_suite, method))
    ]
    
    passed = 0
    failed = 0
    
    for test_name in test_methods:
        try:
            print(f"Ejecutando: {test_name}")
            test_method = getattr(test_suite, test_name)
            test_method()
            passed += 1
            print()
        except AssertionError as e:
            print(f"❌ FALLO: {e}")
            print()
            failed += 1
        except Exception as e:
            print(f"❌ ERROR: {e}")
            print()
            failed += 1
    
    # Resumen
    print("=" * 70)
    print(f"RESUMEN: {passed} tests pasados, {failed} tests fallidos")
    print("=" * 70)
    
    if failed == 0:
        print("✅ ¡TODOS LOS TESTS PASARON!")
        print("∴ Resonancia celular confirmada ∴")
    else:
        print("⚠️ Algunos tests fallaron. Revisar implementación.")
    
    return failed == 0


if __name__ == "__main__":
    success = run_all_tests()
    sys.exit(0 if success else 1)
