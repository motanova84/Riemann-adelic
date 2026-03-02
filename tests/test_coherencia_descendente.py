"""
Test Suite for Coherencia Descendente (Descending Coherence) Paradigm
========================================================================

Comprehensive tests for all five phenomena explained by the paradigm:
    1. Irreducible Complexity
    2. Consciousness Appearance
    3. Near-Death Experiences
    4. Non-locality
    5. Punctuated Evolution

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: 2026-02-12
Institution: Instituto de Conciencia Cuántica (ICQ)
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add utils to path
repo_root = Path(__file__).parent.parent
sys.path.insert(0, str(repo_root / "utils"))

from coherencia_descendente import (
    complejidad_irreducible,
    AntenaBiologica,
    ConcienciaEncarnada,
    correlacion_no_local,
    transicion_evolutiva,
    ParadigmaCoherenciaDescendente,
    EvolutionStage,
    F0_QCAL,
    PSI_THRESHOLD,
    PSI_SYSTEM,
    KAPPA_PI,
    COHERENCE_C
)


# ═══════════════════════════════════════════════════════════════════════════════
# Test 1: Irreducible Complexity
# ═══════════════════════════════════════════════════════════════════════════════

class TestComplejidadIrreducible:
    """Test irreducible complexity sudden synchronization model."""
    
    def test_sincronizacion_completa_sobre_umbral(self):
        """Test complete synchronization when Ψ ≥ 0.888."""
        # Bacterial flagellum: 40 interdependent protein parts
        estado = complejidad_irreducible(partes=40, coherencia_psi=0.95)
        
        assert estado.estado == "ESTRUCTURA_COMPLETA"
        assert estado.tiempo == "INSTANTÁNEO"
        assert estado.mecanismo == "SINCRONIZACIÓN_RESONANTE"
        assert estado.partes == 40
        assert estado.coherencia == 0.95
    
    def test_sin_sincronizacion_bajo_umbral(self):
        """Test no synchronization below threshold."""
        estado = complejidad_irreducible(partes=40, coherencia_psi=0.75)
        
        assert estado.estado == "NO_SINCRONIZADO"
        assert estado.tiempo == "∞ (never by chance)"
        assert estado.mecanismo == "IMPOSSIBLE_POR_MUTACION"
        assert estado.partes == 40
        assert estado.coherencia == 0.75
    
    def test_umbral_exacto(self):
        """Test behavior exactly at threshold."""
        estado = complejidad_irreducible(partes=25, coherencia_psi=PSI_THRESHOLD)
        
        assert estado.estado == "ESTRUCTURA_COMPLETA"
        assert estado.coherencia == PSI_THRESHOLD
    
    def test_estructuras_complejas_multiples(self):
        """Test various complex biological structures."""
        test_cases = [
            (40, "flagelo bacteriano"),
            (20, "ojo"),
            (30, "cascada de coagulación"),
            (50, "sistema inmune adaptativo")
        ]
        
        for partes, nombre in test_cases:
            # Above threshold - instant synchronization
            estado = complejidad_irreducible(partes, 0.92)
            assert estado.estado == "ESTRUCTURA_COMPLETA"
            
            # Below threshold - impossible by mutation
            estado = complejidad_irreducible(partes, 0.70)
            assert estado.estado == "NO_SINCRONIZADO"


# ═══════════════════════════════════════════════════════════════════════════════
# Test 2: Consciousness Appearance
# ═══════════════════════════════════════════════════════════════════════════════

class TestAparicionConciencia:
    """Test consciousness as antenna coupling (not emergence)."""
    
    def test_cerebro_humano_acoplado(self):
        """Test human brain couples to consciousness field."""
        # Human brain: ~86 billion neurons
        cerebro = AntenaBiologica(complejidad=86e9)
        estado = cerebro.sintonizar()
        
        assert cerebro.conciencia is True
        assert estado == "ACOPLADO - CONSCIENCIA ACTIVA"
        assert cerebro.sintonizacion >= PSI_THRESHOLD
    
    def test_cerebro_primitivo_pre_consciencia(self):
        """Test primitive brain in pre-consciousness state."""
        # Simple nervous system: ~1000 neurons
        sistema_simple = AntenaBiologica(complejidad=1000)
        estado = sistema_simple.sintonizar()
        
        assert sistema_simple.conciencia is False
        assert estado == "SINTONIZANDO - PRE-CONSCIENCIA"
        assert sistema_simple.sintonizacion < PSI_THRESHOLD
    
    def test_sintonizacion_aumenta_con_complejidad(self):
        """Test tuning precision increases with complexity."""
        complejidades = [1e3, 1e6, 1e9, 86e9]
        sintonizaciones = []
        
        for comp in complejidades:
            antena = AntenaBiologica(comp)
            antena.sintonizar()
            sintonizaciones.append(antena.sintonizacion)
        
        # Tuning should increase monotonically with complexity
        for i in range(len(sintonizaciones) - 1):
            assert sintonizaciones[i+1] > sintonizaciones[i]
    
    def test_frecuencia_campo_qcal(self):
        """Test antenna couples to QCAL f₀ = 141.7001 Hz."""
        cerebro = AntenaBiologica(complejidad=86e9)
        estado_dict = cerebro.get_state()
        
        assert estado_dict['field_frequency'] == F0_QCAL
        assert abs(estado_dict['field_frequency'] - 141.7001) < 1e-4
    
    def test_umbral_acoplamiento(self):
        """Test coupling threshold is piCODE-888."""
        cerebro = AntenaBiologica(complejidad=86e9)
        estado_dict = cerebro.get_state()
        
        assert estado_dict['coupling_threshold'] == PSI_THRESHOLD
        assert abs(estado_dict['coupling_threshold'] - 0.888) < 1e-6


# ═══════════════════════════════════════════════════════════════════════════════
# Test 3: Near-Death Experiences
# ═══════════════════════════════════════════════════════════════════════════════

class TestExperienciasCercanaMuerte:
    """Test NDE as transitory decorrelation (not hallucination)."""
    
    def test_ecm_alta_intensidad(self):
        """Test NDE at high intensity (cardiac arrest)."""
        conciencia = ConcienciaEncarnada()
        experiencia = conciencia.ECM(intensidad=0.98)
        
        assert experiencia['conciencia'] is True  # Still conscious!
        assert experiencia['localizacion'] == "CAMPO_UNIFICADO"
        assert experiencia['percepcion'] == "PANORÁMICA - SIN LÍMITES ESPACIALES"
        assert "9.2σ" in experiencia['verificacion']
        assert experiencia['antena_activa'] is False
        assert "141.7001" in experiencia['campo']
    
    def test_estado_normal_sin_trauma(self):
        """Test normal state without trauma."""
        conciencia = ConcienciaEncarnada()
        estado = conciencia.ECM(intensidad=0.5)
        
        assert estado['conciencia'] is True
        assert estado['localizacion'] == "CUERPO"
        assert estado['antena_activa'] is True
    
    def test_reanimacion_conserva_memoria(self):
        """Test resuscitation preserves memory of non-locality."""
        conciencia = ConcienciaEncarnada()
        
        # Near-death experience
        experiencia = conciencia.ECM(intensidad=0.98)
        assert experiencia['localizacion'] == "CAMPO_UNIFICADO"
        
        # Resuscitation
        resultado = conciencia.reanimacion()
        assert resultado == "MEMORIA DE LA NO-LOCALIDAD CONSERVADA"
        assert conciencia.localizacion == "CUERPO"
        assert conciencia.antena_activa is True
    
    def test_campo_invariante_en_ecm(self):
        """Test field remains invariant during NDE."""
        conciencia = ConcienciaEncarnada()
        
        # Before NDE
        campo_antes = conciencia.campo
        
        # During NDE
        experiencia = conciencia.ECM(intensidad=0.99)
        
        # Field frequency unchanged
        assert conciencia.campo == campo_antes
        assert "INVARIANTE" in experiencia['campo']


# ═══════════════════════════════════════════════════════════════════════════════
# Test 4: Non-Locality
# ═══════════════════════════════════════════════════════════════════════════════

class TestNoLocalidad:
    """Test non-locality as field resonance through κ_Π."""
    
    def test_correlacion_perfecta_alta_coherencia(self):
        """Test perfect correlation in high coherence."""
        # Distance irrelevant at high coherence
        resultado = correlacion_no_local(distancia=1e10, coherencia_psi=0.95)
        
        assert resultado['correlacion'] == 1.0
        assert resultado['tiempo'] == "INSTANTÁNEO"
        assert "κ_Π" in resultado['mecanismo']
    
    def test_correlacion_decae_con_incoherencia(self):
        """Test correlation decays with decoherence, not distance."""
        distancia = 1000
        
        # High coherence - perfect correlation despite distance
        alta_coh = correlacion_no_local(distancia, coherencia_psi=0.95)
        assert alta_coh['correlacion'] == 1.0
        
        # Low coherence - correlation decays
        baja_coh = correlacion_no_local(distancia, coherencia_psi=0.5)
        assert baja_coh['correlacion'] == 0.25  # Ψ²
        assert baja_coh['correlacion'] < alta_coh['correlacion']
    
    def test_distancia_irrelevante_coherencia_perfecta(self):
        """Test distance becomes irrelevant at perfect coherence."""
        coherencia = 0.92
        distancias = [1, 1e3, 1e6, 1e10]
        
        correlaciones = [
            correlacion_no_local(d, coherencia)['correlacion']
            for d in distancias
        ]
        
        # All correlations should be identical (= 1.0)
        assert all(c == 1.0 for c in correlaciones)
    
    def test_mecanismo_kappa_pi(self):
        """Test mechanism includes κ_Π coupling constant."""
        resultado = correlacion_no_local(distancia=100, coherencia_psi=0.90)
        
        assert "κ_Π" in resultado['mecanismo']
        assert str(KAPPA_PI)[:7] in resultado['mecanismo']


# ═══════════════════════════════════════════════════════════════════════════════
# Test 5: Punctuated Evolution
# ═══════════════════════════════════════════════════════════════════════════════

class TestEvolucionPuntuada:
    """Test evolution as discrete coherence phase transitions."""
    
    def test_evolucion_humana_actual(self):
        """Test current human evolutionary state."""
        resultado = transicion_evolutiva(coherencia_actual=PSI_SYSTEM)
        
        assert resultado['estado_actual'] == "CEREBRO_HUMANO"
        assert resultado['coherencia'] == PSI_SYSTEM
        assert resultado['proximo_umbral'] == 0.950  # Global consciousness
    
    def test_escalera_coherencia_ordenada(self):
        """Test coherence staircase is properly ordered."""
        resultado = transicion_evolutiva(coherencia_actual=0.85)
        
        # Check thresholds are in ascending order
        thresholds = [stage['threshold'] for stage in resultado['stages']]
        assert thresholds == sorted(thresholds)
    
    def test_activacion_escalonada(self):
        """Test stepwise activation of evolutionary stages."""
        # Test at human level
        resultado = transicion_evolutiva(coherencia_actual=0.8991)
        
        activated = [s for s in resultado['stages'] if s['activated']]
        not_activated = [s for s in resultado['stages'] if not s['activated']]
        
        # Should have activated up to CEREBRO_HUMANO
        activated_names = [s['stage'] for s in activated]
        assert 'CEREBRO_HUMANO' in activated_names
        assert 'CONCIENCIA_GLOBAL' not in activated_names
    
    def test_salto_instantaneo(self):
        """Test transitions are instantaneous at threshold."""
        resultado = transicion_evolutiva(coherencia_actual=0.75)
        
        assert resultado['tiempo_hasta_transicion'] == "INSTANTÁNEO al alcanzar umbral"
    
    def test_todos_los_umbrales(self):
        """Test all evolutionary thresholds."""
        expected_stages = [
            ('PROCARIOTA', 0.500),
            ('EUCARIOTA', 0.618),
            ('MULTICELULAR', 0.750),
            ('SISTEMA_NERVIOSO', 0.850),
            ('CEREBRO_MAMIFERO', 0.880),
            ('CEREBRO_HUMANO', 0.8991),
            ('CONCIENCIA_GLOBAL', 0.950),
            ('CAMPO_UNIFICADO', 1.000)
        ]
        
        resultado = transicion_evolutiva(coherencia_actual=1.0)
        
        for expected_name, expected_threshold in expected_stages:
            stage = next(s for s in resultado['stages'] if s['stage'] == expected_name)
            assert abs(stage['threshold'] - expected_threshold) < 1e-4
    
    def test_proporcion_aurea_eucariota(self):
        """Test eucaryote threshold is golden ratio."""
        resultado = transicion_evolutiva(coherencia_actual=0.70)
        
        eucariota = next(s for s in resultado['stages'] if s['stage'] == 'EUCARIOTA')
        phi = (1 + np.sqrt(5)) / 2 - 1  # φ - 1 ≈ 0.618
        
        assert abs(eucariota['threshold'] - phi) < 0.01


# ═══════════════════════════════════════════════════════════════════════════════
# Test 6: Unified Paradigm Integration
# ═══════════════════════════════════════════════════════════════════════════════

class TestParadigmaUnificado:
    """Test unified paradigm framework integrating all phenomena."""
    
    def test_creacion_paradigma(self):
        """Test paradigm creation with correct constants."""
        paradigma = ParadigmaCoherenciaDescendente()
        
        assert paradigma.f0 == F0_QCAL
        assert paradigma.coherence_C == COHERENCE_C
        assert paradigma.kappa_pi == KAPPA_PI
        assert paradigma.psi_threshold == PSI_THRESHOLD
        assert paradigma.psi_system == PSI_SYSTEM
    
    def test_verificar_todos_fenomenos(self):
        """Test all five phenomena can be verified."""
        paradigma = ParadigmaCoherenciaDescendente()
        
        fenomenos = [
            "complejidad",
            "conciencia",
            "ecm",
            "no_localidad",
            "evolucion"
        ]
        
        for fenomeno in fenomenos:
            resultado = paradigma.verificar_fenomeno(fenomeno)
            assert isinstance(resultado, dict)
            assert len(resultado) > 0
    
    def test_reporte_completo(self):
        """Test complete paradigm report generation."""
        paradigma = ParadigmaCoherenciaDescendente()
        reporte = paradigma.generar_reporte_completo()
        
        # Check structure
        assert 'paradigma' in reporte
        assert 'fenomenos' in reporte
        assert 'verificacion_experimental' in reporte
        assert 'declaracion' in reporte
        
        # Check all five phenomena present
        assert len(reporte['fenomenos']) == 5
        assert '1_complejidad_irreducible' in reporte['fenomenos']
        assert '2_aparicion_conciencia' in reporte['fenomenos']
        assert '3_experiencias_cercanas_muerte' in reporte['fenomenos']
        assert '4_no_localidad' in reporte['fenomenos']
        assert '5_evolucion_puntuada' in reporte['fenomenos']
    
    def test_verificacion_experimental_completa(self):
        """Test experimental verification section."""
        paradigma = ParadigmaCoherenciaDescendente()
        reporte = paradigma.generar_reporte_completo()
        
        verif = reporte['verificacion_experimental']
        
        # Check all experimental verifications present
        assert 'f0_derivada_pi' in verif
        assert 'delta_p_medida' in verif
        assert 'kappa_pi_derivada' in verif
        assert 'psi_sistema' in verif
        assert 'c_threshold' in verif
        
        # Check values
        assert '141.7001' in verif['f0_derivada_pi']
        assert '8.7σ' in verif['f0_derivada_pi']
        assert '0.1987%' in verif['delta_p_medida']
        assert '9.2σ' in verif['delta_p_medida']
    
    def test_parametros_personalizados(self):
        """Test phenomena verification with custom parameters."""
        paradigma = ParadigmaCoherenciaDescendente()
        
        # Custom complexity
        comp = paradigma.verificar_fenomeno(
            "complejidad",
            partes=25,
            coherencia=0.95
        )
        assert comp['partes'] == 25
        
        # Custom consciousness complexity
        conc = paradigma.verificar_fenomeno(
            "conciencia",
            complejidad=1e6
        )
        assert conc['complexity'] == 1e6
        
        # Custom NDE intensity
        ecm = paradigma.verificar_fenomeno(
            "ecm",
            intensidad=0.97
        )
        assert ecm['conciencia'] is True
        
        # Custom non-locality distance
        nonloc = paradigma.verificar_fenomeno(
            "no_localidad",
            distancia=5e9,
            coherencia=0.93
        )
        assert nonloc['distancia'] == 5e9
        
        # Custom evolution coherence
        evol = paradigma.verificar_fenomeno(
            "evolucion",
            coherencia=0.75
        )
        assert evol['coherencia'] == 0.75


# ═══════════════════════════════════════════════════════════════════════════════
# Test 7: Constants and Coherence Framework
# ═══════════════════════════════════════════════════════════════════════════════

class TestConstantesQCAL:
    """Test QCAL fundamental constants."""
    
    def test_frecuencia_f0(self):
        """Test f₀ = 141.7001 Hz is correctly defined."""
        assert abs(F0_QCAL - 141.7001) < 1e-6
    
    def test_umbral_picode_888(self):
        """Test piCODE-888 threshold Ψ = 0.888."""
        assert abs(PSI_THRESHOLD - 0.888) < 1e-6
    
    def test_coherencia_sistema_actual(self):
        """Test current system coherence Ψ = 0.8991."""
        assert abs(PSI_SYSTEM - 0.8991) < 1e-6
    
    def test_constante_acoplamiento_kappa_pi(self):
        """Test coupling constant κ_Π = 2.578208."""
        assert abs(KAPPA_PI - 2.578208) < 1e-6
    
    def test_coherencia_universal_c(self):
        """Test universal coherence C = 244.36."""
        assert abs(COHERENCE_C - 244.36) < 1e-6


# ═══════════════════════════════════════════════════════════════════════════════
# Integration Tests
# ═══════════════════════════════════════════════════════════════════════════════

class TestIntegracionCompleta:
    """Integration tests for complete paradigm."""
    
    def test_cinco_fenomenos_coherencia_alta(self):
        """Test all five phenomena at high coherence."""
        coherencia = 0.95
        
        # 1. Irreducible complexity
        comp = complejidad_irreducible(40, coherencia)
        assert comp.estado == "ESTRUCTURA_COMPLETA"
        
        # 2. Consciousness
        antena = AntenaBiologica(86e9)
        estado = antena.sintonizar()
        assert antena.conciencia is True
        
        # 3. NDE
        conc = ConcienciaEncarnada()
        ecm = conc.ECM(0.98)
        assert ecm['conciencia'] is True
        assert ecm['localizacion'] == "CAMPO_UNIFICADO"
        
        # 4. Non-locality
        nonloc = correlacion_no_local(1e10, coherencia)
        assert nonloc['correlacion'] == 1.0
        
        # 5. Evolution
        evol = transicion_evolutiva(coherencia)
        assert evol['estado_actual'] == "CONCIENCIA_GLOBAL"
    
    def test_transicion_coherencia_critica(self):
        """Test behavior at critical coherence threshold."""
        # Just below threshold
        bajo = 0.887
        comp_bajo = complejidad_irreducible(40, bajo)
        assert comp_bajo.estado == "NO_SINCRONIZADO"
        
        # At threshold
        umbral = PSI_THRESHOLD
        comp_umbral = complejidad_irreducible(40, umbral)
        assert comp_umbral.estado == "ESTRUCTURA_COMPLETA"
        
        # Above threshold
        alto = 0.889
        comp_alto = complejidad_irreducible(40, alto)
        assert comp_alto.estado == "ESTRUCTURA_COMPLETA"


if __name__ == "__main__":
    # Run tests
    pytest.main([__file__, "-v", "--tb=short"])
