#!/usr/bin/env python3
"""
Simple Test Runner for Coherencia Descendente (without pytest dependency)
==========================================================================

Runs all tests for the five phenomena explained by the paradigm.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: 2026-02-12
Institution: Instituto de Conciencia Cuántica (ICQ)
"""

import sys
from pathlib import Path
import traceback

# Add utils to path
repo_root = Path(__file__).parent
sys.path.insert(0, str(repo_root / "utils"))

from coherencia_descendente import (
    complejidad_irreducible,
    AntenaBiologica,
    ConcienciaEncarnada,
    correlacion_no_local,
    transicion_evolutiva,
    ParadigmaCoherenciaDescendente,
    F0_QCAL,
    PSI_THRESHOLD,
    PSI_SYSTEM,
    KAPPA_PI,
    COHERENCE_C
)


class TestRunner:
    """Simple test runner."""
    
    def __init__(self):
        self.tests_run = 0
        self.tests_passed = 0
        self.tests_failed = 0
        self.failures = []
    
    def run_test(self, test_func, test_name):
        """Run a single test function."""
        self.tests_run += 1
        try:
            test_func()
            self.tests_passed += 1
            print(f"  ✓ {test_name}")
        except AssertionError as e:
            self.tests_failed += 1
            self.failures.append((test_name, str(e)))
            print(f"  ✗ {test_name}: {e}")
        except Exception as e:
            self.tests_failed += 1
            self.failures.append((test_name, traceback.format_exc()))
            print(f"  ✗ {test_name}: EXCEPTION: {e}")
    
    def print_summary(self):
        """Print test summary."""
        print()
        print("=" * 80)
        print(f"Test Summary: {self.tests_run} tests run")
        print(f"  ✓ Passed: {self.tests_passed}")
        print(f"  ✗ Failed: {self.tests_failed}")
        print("=" * 80)
        
        if self.failures:
            print()
            print("Failed Tests:")
            for name, error in self.failures:
                print(f"  - {name}")
                print(f"    {error}")
        
        return self.tests_failed == 0


# ═══════════════════════════════════════════════════════════════════════════════
# Test Functions
# ═══════════════════════════════════════════════════════════════════════════════

def test_complejidad_sobre_umbral():
    """Test complete synchronization when Ψ ≥ 0.888."""
    estado = complejidad_irreducible(partes=40, coherencia_psi=0.95)
    assert estado.estado == "ESTRUCTURA_COMPLETA"
    assert estado.tiempo == "INSTANTÁNEO"
    assert estado.mecanismo == "SINCRONIZACIÓN_RESONANTE"


def test_complejidad_bajo_umbral():
    """Test no synchronization below threshold."""
    estado = complejidad_irreducible(partes=40, coherencia_psi=0.75)
    assert estado.estado == "NO_SINCRONIZADO"
    assert estado.tiempo == "∞ (never by chance)"


def test_cerebro_humano_consciente():
    """Test human brain couples to consciousness field."""
    cerebro = AntenaBiologica(complejidad=86e9)
    estado = cerebro.sintonizar()
    assert cerebro.conciencia is True
    assert estado == "ACOPLADO - CONSCIENCIA ACTIVA"


def test_sistema_simple_pre_consciencia():
    """Test primitive brain in pre-consciousness state."""
    # Very simple system: single neuron or minimal connectivity
    sistema_simple = AntenaBiologica(complejidad=1)
    estado = sistema_simple.sintonizar()
    assert sistema_simple.conciencia is False
    assert estado == "SINTONIZANDO - PRE-CONSCIENCIA"


def test_frecuencia_qcal():
    """Test antenna couples to QCAL f₀ = 141.7001 Hz."""
    cerebro = AntenaBiologica(complejidad=86e9)
    estado_dict = cerebro.get_state()
    assert abs(estado_dict['field_frequency'] - 141.7001) < 1e-4


def test_ecm_alta_intensidad():
    """Test NDE at high intensity."""
    conciencia = ConcienciaEncarnada()
    experiencia = conciencia.ECM(intensidad=0.98)
    assert experiencia['conciencia'] is True  # Still conscious!
    assert experiencia['localizacion'] == "CAMPO_UNIFICADO"
    assert experiencia['antena_activa'] is False


def test_ecm_estado_normal():
    """Test normal state without trauma."""
    conciencia = ConcienciaEncarnada()
    estado = conciencia.ECM(intensidad=0.5)
    assert estado['conciencia'] is True
    assert estado['localizacion'] == "CUERPO"
    assert estado['antena_activa'] is True


def test_reanimacion_conserva_memoria():
    """Test resuscitation preserves memory."""
    conciencia = ConcienciaEncarnada()
    experiencia = conciencia.ECM(intensidad=0.98)
    resultado = conciencia.reanimacion()
    assert resultado == "MEMORIA DE LA NO-LOCALIDAD CONSERVADA"
    assert conciencia.localizacion == "CUERPO"


def test_no_localidad_alta_coherencia():
    """Test perfect correlation in high coherence."""
    resultado = correlacion_no_local(distancia=1e10, coherencia_psi=0.95)
    assert resultado['correlacion'] == 1.0
    assert resultado['tiempo'] == "INSTANTÁNEO"


def test_no_localidad_baja_coherencia():
    """Test correlation decays with decoherence."""
    resultado = correlacion_no_local(distancia=1000, coherencia_psi=0.5)
    assert resultado['correlacion'] == 0.25  # Ψ²
    assert resultado['tiempo'] == "LIMITADO POR c"


def test_evolucion_humana_actual():
    """Test current human evolutionary state."""
    resultado = transicion_evolutiva(coherencia_actual=PSI_SYSTEM)
    assert resultado['estado_actual'] == "CEREBRO_HUMANO"
    assert resultado['coherencia'] == PSI_SYSTEM


def test_evolucion_escalera_ordenada():
    """Test coherence staircase is ordered."""
    resultado = transicion_evolutiva(coherencia_actual=0.85)
    thresholds = [stage['threshold'] for stage in resultado['stages']]
    assert thresholds == sorted(thresholds)


def test_paradigma_creacion():
    """Test paradigm creation with correct constants."""
    paradigma = ParadigmaCoherenciaDescendente()
    assert paradigma.f0 == F0_QCAL
    assert paradigma.coherence_C == COHERENCE_C
    assert paradigma.kappa_pi == KAPPA_PI


def test_paradigma_fenomenos():
    """Test all five phenomena can be verified."""
    paradigma = ParadigmaCoherenciaDescendente()
    fenomenos = ["complejidad", "conciencia", "ecm", "no_localidad", "evolucion"]
    for fenomeno in fenomenos:
        resultado = paradigma.verificar_fenomeno(fenomeno)
        assert isinstance(resultado, dict)
        assert len(resultado) > 0


def test_paradigma_reporte_completo():
    """Test complete paradigm report."""
    paradigma = ParadigmaCoherenciaDescendente()
    reporte = paradigma.generar_reporte_completo()
    assert 'paradigma' in reporte
    assert 'fenomenos' in reporte
    assert len(reporte['fenomenos']) == 5


def test_constantes_qcal():
    """Test QCAL fundamental constants."""
    assert abs(F0_QCAL - 141.7001) < 1e-6
    assert abs(PSI_THRESHOLD - 0.888) < 1e-6
    assert abs(PSI_SYSTEM - 0.8991) < 1e-6
    assert abs(KAPPA_PI - 2.578208) < 1e-6
    assert abs(COHERENCE_C - 244.36) < 1e-6


def test_distancia_irrelevante_coherencia():
    """Test distance irrelevant at high coherence."""
    coherencia = 0.92
    distancias = [1, 1e3, 1e6, 1e10]
    correlaciones = [
        correlacion_no_local(d, coherencia)['correlacion']
        for d in distancias
    ]
    assert all(c == 1.0 for c in correlaciones)


def test_umbral_exacto():
    """Test behavior exactly at threshold."""
    estado = complejidad_irreducible(partes=25, coherencia_psi=PSI_THRESHOLD)
    assert estado.estado == "ESTRUCTURA_COMPLETA"


def test_campo_invariante_ecm():
    """Test field remains invariant during NDE."""
    conciencia = ConcienciaEncarnada()
    campo_antes = conciencia.campo
    experiencia = conciencia.ECM(intensidad=0.99)
    assert conciencia.campo == campo_antes


def test_evolucion_proporcion_aurea():
    """Test eucaryote threshold is golden ratio."""
    import numpy as np
    resultado = transicion_evolutiva(coherencia_actual=0.70)
    eucariota = next(s for s in resultado['stages'] if s['stage'] == 'EUCARIOTA')
    phi = (1 + np.sqrt(5)) / 2 - 1  # φ - 1 ≈ 0.618
    assert abs(eucariota['threshold'] - phi) < 0.01


# ═══════════════════════════════════════════════════════════════════════════════
# Main Test Execution
# ═══════════════════════════════════════════════════════════════════════════════

def main():
    """Run all tests."""
    print("=" * 80)
    print("  Test Suite: Paradigma de la Coherencia Descendente")
    print("=" * 80)
    print()
    
    runner = TestRunner()
    
    # Group 1: Irreducible Complexity
    print("1. Complejidad Irreducible:")
    runner.run_test(test_complejidad_sobre_umbral, "Synchronization above threshold")
    runner.run_test(test_complejidad_bajo_umbral, "No synchronization below threshold")
    runner.run_test(test_umbral_exacto, "Behavior at exact threshold")
    
    # Group 2: Consciousness Appearance
    print()
    print("2. Aparición de Conciencia:")
    runner.run_test(test_cerebro_humano_consciente, "Human brain consciousness")
    runner.run_test(test_sistema_simple_pre_consciencia, "Simple system pre-consciousness")
    runner.run_test(test_frecuencia_qcal, "QCAL frequency coupling")
    
    # Group 3: Near-Death Experiences
    print()
    print("3. Experiencias Cercanas a la Muerte:")
    runner.run_test(test_ecm_alta_intensidad, "NDE at high intensity")
    runner.run_test(test_ecm_estado_normal, "Normal state")
    runner.run_test(test_reanimacion_conserva_memoria, "Memory conservation")
    runner.run_test(test_campo_invariante_ecm, "Field invariance during NDE")
    
    # Group 4: Non-locality
    print()
    print("4. No-localidad:")
    runner.run_test(test_no_localidad_alta_coherencia, "Perfect correlation at high coherence")
    runner.run_test(test_no_localidad_baja_coherencia, "Correlation decay at low coherence")
    runner.run_test(test_distancia_irrelevante_coherencia, "Distance irrelevant at high coherence")
    
    # Group 5: Punctuated Evolution
    print()
    print("5. Evolución Puntuada:")
    runner.run_test(test_evolucion_humana_actual, "Current human state")
    runner.run_test(test_evolucion_escalera_ordenada, "Ordered coherence staircase")
    runner.run_test(test_evolucion_proporcion_aurea, "Golden ratio eucaryote")
    
    # Group 6: Unified Paradigm
    print()
    print("6. Paradigma Unificado:")
    runner.run_test(test_paradigma_creacion, "Paradigm creation")
    runner.run_test(test_paradigma_fenomenos, "All phenomena verification")
    runner.run_test(test_paradigma_reporte_completo, "Complete report")
    
    # Group 7: Constants
    print()
    print("7. Constantes QCAL:")
    runner.run_test(test_constantes_qcal, "Fundamental constants")
    
    # Print summary
    success = runner.print_summary()
    
    return 0 if success else 1


if __name__ == "__main__":
    sys.exit(main())
