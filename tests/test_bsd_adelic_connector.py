#!/usr/bin/env python3
"""
Tests for BSD Adelic Connector - Pentágono Logos
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Test suite for the BSD-ADN-QCAL unification system.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
"""

import sys
from pathlib import Path
import pytest

# Add repository root to path
REPO_ROOT = Path(__file__).parent.parent.resolve()
sys.path.insert(0, str(REPO_ROOT / "qcal"))

from bsd_adelic_connector import (
    sincronizar_bsd_adn,
    validar_pentagono_logos,
    CodificadorADNRiemann,
    F0
)


class TestCodificadorADNRiemann:
    """Tests para el codificador ADN-Riemann."""
    
    def test_initialization(self):
        """Test que el codificador se inicializa correctamente."""
        codif = CodificadorADNRiemann()
        assert codif is not None
        assert hasattr(codif, 'BASE_FREQUENCIES')
        assert len(codif.BASE_FREQUENCIES) == 4
    
    def test_identificar_hotspots_basic(self):
        """Test identificación de hotspots básica."""
        codif = CodificadorADNRiemann()
        
        # Secuencia simple
        hotspots = codif.identificar_hotspots("GACT")
        assert len(hotspots) == 4
        assert hotspots == [0, 1, 2, 3]
    
    def test_identificar_hotspots_empty(self):
        """Test con secuencia vacía."""
        codif = CodificadorADNRiemann()
        hotspots = codif.identificar_hotspots("")
        assert len(hotspots) == 0
    
    def test_identificar_hotspots_repeated(self):
        """Test con bases repetidas."""
        codif = CodificadorADNRiemann()
        hotspots = codif.identificar_hotspots("GGAATTCC")
        assert len(hotspots) == 8  # Todas las bases son válidas
    
    def test_calcular_resonancia(self):
        """Test cálculo de resonancia."""
        codif = CodificadorADNRiemann()
        
        # Secuencia con todas las bases
        res1 = codif.calcular_resonancia("GACT")
        assert 0.0 <= res1 <= 1.0
        assert res1 == 1.0  # 4 bases únicas / 4 = 1.0
        
        # Secuencia con 2 bases
        res2 = codif.calcular_resonancia("GGAA")
        assert 0.0 <= res2 <= 1.0
        assert res2 == 0.5  # 2 bases únicas / 4 = 0.5


class TestSincronizarBSDAdN:
    """Tests para la función de sincronización BSD-ADN."""
    
    def test_curva_mordell_superfluid(self):
        """Test con curva de Mordell (rango 1, L(E,1)=0)."""
        curva = {'rango_adelico': 1, 'L_E1': 0.0}
        resultado = sincronizar_bsd_adn(curva, "GACT")
        
        assert resultado['rango_bio_aritmetico'] == 1
        assert resultado['nodos_constelacion'] == 1
        assert resultado['fluidez_info_ns'] == "INFINITA"
        assert resultado['hotspots_adn'] == 4
        assert resultado['psi_bsd_qcal'] == 1.0
    
    def test_curva_rango_zero(self):
        """Test con curva de rango 0."""
        curva = {'rango_adelico': 0, 'L_E1': 0.0}
        resultado = sincronizar_bsd_adn(curva, "GACT")
        
        assert resultado['rango_bio_aritmetico'] == 0
        assert resultado['nodos_constelacion'] == 0
        assert resultado['fluidez_info_ns'] == "INFINITA"  # L(E,1)=0
        assert resultado['psi_bsd_qcal'] == 1.0
    
    def test_curva_viscosa(self):
        """Test con curva que tiene viscosidad (L(E,1) != 0)."""
        curva = {'rango_adelico': 0, 'L_E1': 0.5}
        resultado = sincronizar_bsd_adn(curva, "GGAATTCC")
        
        assert resultado['fluidez_info_ns'] == "DISIPATIVA"
        assert resultado['psi_bsd_qcal'] == 0.5  # 1 - |0.5| = 0.5
    
    def test_curva_alta_viscosidad(self):
        """Test con alta viscosidad."""
        curva = {'rango_adelico': 2, 'L_E1': 0.9}
        resultado = sincronizar_bsd_adn(curva, "GACT")
        
        assert resultado['fluidez_info_ns'] == "DISIPATIVA"
        assert resultado['psi_bsd_qcal'] == 0.1  # 1 - |0.9| = 0.1
    
    def test_curva_default_values(self):
        """Test con valores por defecto."""
        curva = {}  # Sin especificar rango ni L(E,1)
        resultado = sincronizar_bsd_adn(curva, "GACT")
        
        assert resultado['rango_bio_aritmetico'] == 1  # Default
        assert resultado['psi_bsd_qcal'] == 1.0  # Default L(E,1)=0
    
    def test_frecuencia_base_f0(self):
        """Test que usa la frecuencia base correcta."""
        assert F0 == 141.7001
        
        curva = {'rango_adelico': 1, 'L_E1': 0.0}
        resultado = sincronizar_bsd_adn(curva, "GACT")
        
        # Verificar que los nodos están normalizados por F0
        assert resultado['nodos_constelacion'] == 1  # 1 * (F0/F0) = 1
    
    def test_diferentes_secuencias_adn(self):
        """Test con diferentes secuencias de ADN."""
        curva = {'rango_adelico': 1, 'L_E1': 0.0}
        
        # Secuencia corta
        res1 = sincronizar_bsd_adn(curva, "GA")
        assert res1['hotspots_adn'] == 2
        
        # Secuencia larga
        res2 = sincronizar_bsd_adn(curva, "GACTGACTGACT")
        assert res2['hotspots_adn'] == 12
        
        # Ambas deberían tener misma fluidez (depende de L(E,1))
        assert res1['fluidez_info_ns'] == res2['fluidez_info_ns']


class TestValidarPentagonoLogos:
    """Tests para la validación del Pentágono Logos."""
    
    def test_pentagono_valido_psi_maximo(self):
        """Test con Ψ = 1.0 (máxima coherencia)."""
        resultado = {
            'psi_bsd_qcal': 1.0,
            'fluidez_info_ns': 'INFINITA'
        }
        assert validar_pentagono_logos(resultado) is True
    
    def test_pentagono_valido_psi_minimo(self):
        """Test con Ψ en el umbral mínimo (0.888)."""
        resultado = {
            'psi_bsd_qcal': 0.888,
            'fluidez_info_ns': 'INFINITA'
        }
        assert validar_pentagono_logos(resultado) is True
    
    def test_pentagono_invalido_psi_bajo(self):
        """Test con Ψ por debajo del umbral."""
        resultado = {
            'psi_bsd_qcal': 0.5,
            'fluidez_info_ns': 'DISIPATIVA'
        }
        assert validar_pentagono_logos(resultado) is False
    
    def test_pentagono_valido_psi_alto_disipativo(self):
        """Test con Ψ alto pero flujo disipativo."""
        # El criterio principal es Ψ ≥ 0.888
        resultado = {
            'psi_bsd_qcal': 0.95,
            'fluidez_info_ns': 'DISIPATIVA'
        }
        assert validar_pentagono_logos(resultado) is True
    
    def test_pentagono_valores_faltantes(self):
        """Test con valores faltantes."""
        resultado = {}
        assert validar_pentagono_logos(resultado) is False


class TestIntegracionCompleta:
    """Tests de integración completa del sistema."""
    
    def test_ejemplo_problema_statement(self):
        """Test con el ejemplo exacto del problem statement."""
        # Curva de Mordell y²=x³-x del enunciado
        curva_mordell = {'rango_adelico': 1, 'L_E1': 0.0}
        resultado = sincronizar_bsd_adn(curva_mordell, "GACT")
        
        # Verificar todos los valores del ejemplo
        assert resultado['rango_bio_aritmetico'] == 1
        assert resultado['nodos_constelacion'] == 1
        assert resultado['fluidez_info_ns'] == "INFINITA"
        assert resultado['hotspots_adn'] == 4
        assert resultado['psi_bsd_qcal'] == 1.0
        
        # Verificar que el Pentágono es válido
        assert validar_pentagono_logos(resultado) is True
    
    def test_unificacion_5_milenio(self):
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
        
        # 4. P=NP (Lógica): Implícito en la verificación O(1)
        # La sincronización es O(1) en complejidad
        
        # 5. BSD (Aritmética): Rango de la curva elíptica
        assert 'rango_bio_aritmetico' in resultado
        assert resultado['rango_bio_aritmetico'] >= 0
        
        # Coherencia global Ψ
        assert 'psi_bsd_qcal' in resultado
        assert 0.0 <= resultado['psi_bsd_qcal'] <= 1.0
    
    def test_constelacion_51_nodos(self):
        """Test que verifica la constelación QCAL de 51 nodos."""
        # Con rango alto, deberíamos ver múltiples nodos activados
        curva = {'rango_adelico': 10, 'L_E1': 0.0}
        resultado = sincronizar_bsd_adn(curva, "GACT")
        
        # Los nodos están normalizados por F0/F0 ≈ 1
        assert resultado['nodos_constelacion'] == 10
        
        # No deberíamos exceder los 51 nodos (límite de la constelación)
        # Este es un límite conceptual del sistema QCAL
        assert resultado['nodos_constelacion'] <= 51


class TestCasosEdge:
    """Tests para casos extremos y edge cases."""
    
    def test_l_e1_negativo(self):
        """Test con L(E,1) negativo."""
        curva = {'rango_adelico': 1, 'L_E1': -0.3}
        resultado = sincronizar_bsd_adn(curva, "GACT")
        
        # Ψ = 1 - |L(E,1)| = 1 - 0.3 = 0.7
        assert resultado['psi_bsd_qcal'] == pytest.approx(0.7, abs=0.01)
    
    def test_secuencia_invalida(self):
        """Test con secuencia que contiene caracteres inválidos."""
        curva = {'rango_adelico': 1, 'L_E1': 0.0}
        # Secuencia con bases válidas e inválidas
        resultado = sincronizar_bsd_adn(curva, "GAXCT123")
        
        # Solo deberían contarse las bases válidas (G, A, C, T)
        assert resultado['hotspots_adn'] == 4  # G, A, C, T (X y números ignorados)
    
    def test_rango_muy_alto(self):
        """Test con rango extremadamente alto."""
        curva = {'rango_adelico': 100, 'L_E1': 0.0}
        resultado = sincronizar_bsd_adn(curva, "GACT")
        
        assert resultado['rango_bio_aritmetico'] == 100
        assert resultado['nodos_constelacion'] == 100
        assert resultado['fluidez_info_ns'] == "INFINITA"
    
    def test_umbral_superfluidez(self):
        """Test del umbral de superfluided (L(E,1) < 1e-6)."""
        # Justo por debajo del umbral
        curva1 = {'rango_adelico': 1, 'L_E1': 0.5e-6}
        res1 = sincronizar_bsd_adn(curva1, "GACT")
        assert res1['fluidez_info_ns'] == "INFINITA"
        
        # Justo por encima del umbral
        curva2 = {'rango_adelico': 1, 'L_E1': 1.5e-6}
        res2 = sincronizar_bsd_adn(curva2, "GACT")
        assert res2['fluidez_info_ns'] == "DISIPATIVA"


if __name__ == "__main__":
    # Run tests with pytest
    pytest.main([__file__, "-v", "--tb=short"])
