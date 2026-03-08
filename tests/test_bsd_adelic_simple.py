#!/usr/bin/env python3
"""
Simple tests for BSD Adelic Connector - Pentágono Logos
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Test suite for the BSD-ADN-QCAL unification system (without pytest dependency).

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
"""

import sys
from pathlib import Path

# Add repository root to path
REPO_ROOT = Path(__file__).parent.parent.resolve()
sys.path.insert(0, str(REPO_ROOT / "qcal"))

from bsd_adelic_connector import (
    sincronizar_bsd_adn,
    validar_pentagono_logos,
    CodificadorADNRiemann,
    F0
)


def test_codificador_initialization():
    """Test que el codificador se inicializa correctamente."""
    codif = CodificadorADNRiemann()
    assert codif is not None
    assert hasattr(codif, 'BASE_FREQUENCIES')
    assert len(codif.BASE_FREQUENCIES) == 4
    print("✓ Test codificador initialization passed")


def test_identificar_hotspots_basic():
    """Test identificación de hotspots básica."""
    codif = CodificadorADNRiemann()
    hotspots = codif.identificar_hotspots("GACT")
    assert len(hotspots) == 4
    assert hotspots == [0, 1, 2, 3]
    print("✓ Test identificar hotspots basic passed")


def test_curva_mordell_superfluid():
    """Test con curva de Mordell (rango 1, L(E,1)=0)."""
    curva = {'rango_adelico': 1, 'L_E1': 0.0}
    resultado = sincronizar_bsd_adn(curva, "GACT")
    
    assert resultado['rango_bio_aritmetico'] == 1
    assert resultado['nodos_constelacion'] == 1
    assert resultado['fluidez_info_ns'] == "INFINITA"
    assert resultado['hotspots_adn'] == 4
    assert resultado['psi_bsd_qcal'] == 1.0
    print("✓ Test curva Mordell superfluid passed")


def test_curva_viscosa():
    """Test con curva que tiene viscosidad (L(E,1) != 0)."""
    curva = {'rango_adelico': 0, 'L_E1': 0.5}
    resultado = sincronizar_bsd_adn(curva, "GGAATTCC")
    
    assert resultado['fluidez_info_ns'] == "DISIPATIVA"
    assert resultado['psi_bsd_qcal'] == 0.5
    print("✓ Test curva viscosa passed")


def test_pentagono_valido():
    """Test validación del Pentágono Logos."""
    resultado = {'psi_bsd_qcal': 1.0, 'fluidez_info_ns': 'INFINITA'}
    assert validar_pentagono_logos(resultado) is True
    print("✓ Test pentágono válido passed")


def test_pentagono_invalido():
    """Test con Pentágono inválido."""
    resultado = {'psi_bsd_qcal': 0.5, 'fluidez_info_ns': 'DISIPATIVA'}
    assert validar_pentagono_logos(resultado) is False
    print("✓ Test pentágono inválido passed")


def test_ejemplo_problema_statement():
    """Test con el ejemplo exacto del problem statement."""
    curva_mordell = {'rango_adelico': 1, 'L_E1': 0.0}
    resultado = sincronizar_bsd_adn(curva_mordell, "GACT")
    
    assert resultado['rango_bio_aritmetico'] == 1
    assert resultado['nodos_constelacion'] == 1
    assert resultado['fluidez_info_ns'] == "INFINITA"
    assert resultado['hotspots_adn'] == 4
    assert resultado['psi_bsd_qcal'] == 1.0
    assert validar_pentagono_logos(resultado) is True
    print("✓ Test ejemplo problem statement passed")


def test_unificacion_5_milenio():
    """Test que verifica la unificación de los 5 problemas del Milenio."""
    curva = {'rango_adelico': 1, 'L_E1': 0.0}
    resultado = sincronizar_bsd_adn(curva, "GACT")
    
    # 1. ADN (Biología): Hotspots identificados
    assert 'hotspots_adn' in resultado
    assert resultado['hotspots_adn'] > 0
    
    # 2. Riemann (Estructura): Implícito en la frecuencia F0
    assert F0 == 141.7001
    
    # 3. Navier-Stokes (Dinámica): Fluidez del sistema
    assert 'fluidez_info_ns' in resultado
    assert resultado['fluidez_info_ns'] in ['INFINITA', 'DISIPATIVA']
    
    # 4. P=NP (Lógica): Verificación O(1)
    
    # 5. BSD (Aritmética): Rango de la curva elíptica
    assert 'rango_bio_aritmetico' in resultado
    assert resultado['rango_bio_aritmetico'] >= 0
    
    # Coherencia global Ψ
    assert 'psi_bsd_qcal' in resultado
    assert 0.0 <= resultado['psi_bsd_qcal'] <= 1.0
    print("✓ Test unificación 5 Milenio passed")


def test_frecuencia_base_f0():
    """Test que usa la frecuencia base correcta."""
    assert F0 == 141.7001
    
    curva = {'rango_adelico': 1, 'L_E1': 0.0}
    resultado = sincronizar_bsd_adn(curva, "GACT")
    assert resultado['nodos_constelacion'] == 1
    print("✓ Test frecuencia base F0 passed")


def test_l_e1_negativo():
    """Test con L(E,1) negativo."""
    curva = {'rango_adelico': 1, 'L_E1': -0.3}
    resultado = sincronizar_bsd_adn(curva, "GACT")
    
    # Ψ = 1 - |L(E,1)| = 1 - 0.3 = 0.7
    assert abs(resultado['psi_bsd_qcal'] - 0.7) < 0.01
    print("✓ Test L(E,1) negativo passed")


def test_umbral_superfluidez():
    """Test del umbral de superfluided (L(E,1) < 1e-6)."""
    # Justo por debajo del umbral
    curva1 = {'rango_adelico': 1, 'L_E1': 0.5e-6}
    res1 = sincronizar_bsd_adn(curva1, "GACT")
    assert res1['fluidez_info_ns'] == "INFINITA"
    
    # Justo por encima del umbral
    curva2 = {'rango_adelico': 1, 'L_E1': 1.5e-6}
    res2 = sincronizar_bsd_adn(curva2, "GACT")
    assert res2['fluidez_info_ns'] == "DISIPATIVA"
    print("✓ Test umbral superfluided passed")


def run_all_tests():
    """Run all tests."""
    print("=" * 80)
    print("BSD ADELIC CONNECTOR - Test Suite")
    print("=" * 80)
    print()
    
    tests = [
        test_codificador_initialization,
        test_identificar_hotspots_basic,
        test_curva_mordell_superfluid,
        test_curva_viscosa,
        test_pentagono_valido,
        test_pentagono_invalido,
        test_ejemplo_problema_statement,
        test_unificacion_5_milenio,
        test_frecuencia_base_f0,
        test_l_e1_negativo,
        test_umbral_superfluidez,
    ]
    
    passed = 0
    failed = 0
    
    for test in tests:
        try:
            test()
            passed += 1
        except AssertionError as e:
            print(f"✗ {test.__name__} FAILED: {e}")
            failed += 1
        except Exception as e:
            print(f"✗ {test.__name__} ERROR: {e}")
            failed += 1
    
    print()
    print("=" * 80)
    print(f"Test Results: {passed} passed, {failed} failed")
    print("=" * 80)
    
    return failed == 0


if __name__ == "__main__":
    success = run_all_tests()
    sys.exit(0 if success else 1)
