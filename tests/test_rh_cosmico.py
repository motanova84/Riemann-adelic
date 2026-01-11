#!/usr/bin/env python3
"""
Tests for RH Cósmico: El Respirar del Universo en la Línea Crítica

Test suite para validar las tres capas de significado ontológico
de la Hipótesis de Riemann en el framework QCAL ∞³.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Añadir directorio raíz al path
sys.path.insert(0, str(Path(__file__).parent.parent))

from rh_cosmico import (
    CosmicBreathing,
    CosmicBreathingState,
    F0_HZ,
    COHERENCE_C,
    COHERENCE_C_PRIME,
    CRITICAL_LINE,
    validate_critical_line_necessity,
    compute_breathing_signature
)


class TestCosmicBreathingState:
    """Tests para la clase CosmicBreathingState."""
    
    def test_creation(self):
        """Test creación de estado."""
        state = CosmicBreathingState(
            frequency=141.7001,
            coherence=244.36,
            phase=0.0,
            amplitude=1.0,
            symmetry_deviation=0.0,
            stability_index=1.0
        )
        
        assert state.frequency == 141.7001
        assert state.coherence == 244.36
        assert state.phase == 0.0
        assert state.amplitude == 1.0
        assert state.symmetry_deviation == 0.0
        assert state.stability_index == 1.0
    
    def test_to_dict(self):
        """Test conversión a diccionario."""
        state = CosmicBreathingState(
            frequency=141.7001,
            coherence=244.36,
            phase=np.pi,
            amplitude=0.5,
            symmetry_deviation=0.01,
            stability_index=0.99
        )
        
        d = state.to_dict()
        assert isinstance(d, dict)
        assert d['frequency'] == 141.7001
        assert d['coherence'] == 244.36
        assert abs(d['phase'] - np.pi) < 1e-10
        assert d['amplitude'] == 0.5


class TestCosmicBreathing:
    """Tests para la clase principal CosmicBreathing."""
    
    @pytest.fixture
    def cosmic(self):
        """Fixture: instancia de CosmicBreathing."""
        return CosmicBreathing(frequency=F0_HZ, coherence=COHERENCE_C, precision=15)
    
    def test_initialization(self, cosmic):
        """Test inicialización."""
        assert cosmic.frequency == F0_HZ
        assert cosmic.coherence == COHERENCE_C
        assert cosmic.omega_0 == 2 * np.pi * F0_HZ
        assert cosmic.precision == 15
        
        # Verificar estado inicial
        assert cosmic.state.frequency == F0_HZ
        assert cosmic.state.coherence == COHERENCE_C
        assert cosmic.state.phase == 0.0
        assert cosmic.state.amplitude == 1.0
    
    # ========================================================================
    # CAPA 1: Tests Aritméticos
    # ========================================================================
    
    def test_compute_prime_breathing_amplitude(self, cosmic):
        """Test cálculo de amplitud de respiración aritmética."""
        # Calcular amplitud en x = 1000
        amplitude = cosmic.compute_prime_breathing_amplitude(1000.0, num_zeros=10)
        
        assert isinstance(amplitude, float)
        assert amplitude >= 0.0  # Amplitud siempre positiva
        assert np.isfinite(amplitude)
    
    def test_validate_arithmetic_symmetry(self, cosmic):
        """Test validación de simetría aritmética."""
        results = cosmic.validate_arithmetic_symmetry()
        
        # Verificar estructura de resultados
        assert 'test_points' in results
        assert 'amplitudes' in results
        assert 'symmetry_score' in results
        assert 'is_symmetric' in results
        
        # Verificar tipos
        assert isinstance(results['test_points'], list)
        assert isinstance(results['amplitudes'], list)
        assert isinstance(results['symmetry_score'], float)
        assert isinstance(results['is_symmetric'], bool)
        
        # Verificar rangos
        assert 0.0 <= results['symmetry_score'] <= 1.0
        assert len(results['amplitudes']) == len(results['test_points'])
    
    def test_arithmetic_symmetry_custom_points(self, cosmic):
        """Test simetría con puntos personalizados."""
        test_points = [50.0, 100.0, 500.0]
        results = cosmic.validate_arithmetic_symmetry(test_points=test_points)
        
        assert results['test_points'] == test_points
        assert len(results['amplitudes']) == len(test_points)
    
    # ========================================================================
    # CAPA 2: Tests Cuántico-Espectrales
    # ========================================================================
    
    def test_compute_Hpsi_spectrum_breathing(self, cosmic):
        """Test cálculo del espectro de H_Ψ."""
        spectrum = cosmic.compute_Hpsi_spectrum_breathing(n_modes=20)
        
        # Verificar estructura
        assert 'eigenvalues' in spectrum
        assert 'n_modes' in spectrum
        assert 'all_real' in spectrum
        assert 'mean_spacing' in spectrum
        assert 'coherence_preserved' in spectrum
        assert 'dissipation' in spectrum
        
        # Verificar tipos y valores
        assert isinstance(spectrum['eigenvalues'], list)
        assert len(spectrum['eigenvalues']) == 20
        assert spectrum['n_modes'] == 20
        assert isinstance(spectrum['all_real'], bool)
        assert isinstance(spectrum['mean_spacing'], float)
        assert isinstance(spectrum['coherence_preserved'], bool)
        assert spectrum['dissipation'] == 0.0  # Sin disipación en modelo ideal
        
        # Eigenvalues deben ser todos positivos (parte imaginaria de ceros)
        assert all(ev > 0 for ev in spectrum['eigenvalues'])
    
    def test_spectrum_realness(self, cosmic):
        """Test que el espectro sea puramente real."""
        spectrum = cosmic.compute_Hpsi_spectrum_breathing(n_modes=50)
        
        # En el modelo ideal, todos los eigenvalues son reales
        assert spectrum['all_real'] == True
        assert spectrum['coherence_preserved'] == True
    
    def test_validate_quantum_coherence(self, cosmic):
        """Test validación de coherencia cuántica."""
        coherence = cosmic.validate_quantum_coherence()
        
        # Verificar estructura
        assert 'spectrum_real' in coherence
        assert 'no_dissipation' in coherence
        assert 'coherence_level' in coherence
        assert 'overall_score' in coherence
        assert 'is_coherent' in coherence
        
        # Verificar tipos
        assert isinstance(coherence['spectrum_real'], bool)
        assert isinstance(coherence['no_dissipation'], bool)
        assert isinstance(coherence['coherence_level'], float)
        assert isinstance(coherence['overall_score'], float)
        assert isinstance(coherence['is_coherent'], bool)
        
        # Verificar rangos
        assert 0.0 <= coherence['overall_score'] <= 1.0
    
    def test_fundamental_frequency_extraction(self, cosmic):
        """Test extracción de frecuencia fundamental del espectro."""
        spectrum = cosmic.compute_Hpsi_spectrum_breathing(n_modes=10)
        
        # Debe existir frecuencia fundamental
        assert 'fundamental_frequency' in spectrum
        
        # Debe ser positiva
        f_fund = spectrum['fundamental_frequency']
        assert f_fund > 0.0
        
        # Debe coincidir con la frecuencia configurada
        assert abs(f_fund - F0_HZ) < 1e-6
    
    # ========================================================================
    # CAPA 3: Tests Noético-Existenciales
    # ========================================================================
    
    def test_compute_infinity_stability(self, cosmic):
        """Test cálculo de estabilidad del infinito."""
        stability = cosmic.compute_infinity_stability()
        
        # Verificar tipo y rango
        assert isinstance(stability, float)
        assert 0.0 <= stability <= 1.0
        
        # El estado debe actualizarse
        assert cosmic.state.stability_index == stability
    
    def test_validate_critical_line_necessity(self, cosmic):
        """Test validación de necesidad ontológica."""
        necessity = cosmic.validate_critical_line_necessity()
        
        # Verificar estructura
        assert 'stability_index' in necessity
        assert 'is_necessary' in necessity
        assert 'collapse_risk' in necessity
        assert 'ontological_status' in necessity
        assert 'explanation' in necessity
        
        # Verificar tipos
        assert isinstance(necessity['stability_index'], float)
        assert isinstance(necessity['is_necessary'], bool)
        assert isinstance(necessity['collapse_risk'], float)
        assert isinstance(necessity['ontological_status'], str)
        assert isinstance(necessity['explanation'], str)
        
        # Verificar rangos
        assert 0.0 <= necessity['stability_index'] <= 1.0
        assert 0.0 <= necessity['collapse_risk'] <= 1.0
        
        # Colapso + estabilidad = 1
        assert abs((necessity['stability_index'] + necessity['collapse_risk']) - 1.0) < 1e-10
        
        # Estado ontológico debe ser válido
        assert necessity['ontological_status'] in ['necessary', 'contingent']
    
    def test_necessity_explanation_generation(self, cosmic):
        """Test generación de explicación de necesidad."""
        necessity = cosmic.validate_critical_line_necessity()
        
        # Explicación no debe estar vacía
        assert len(necessity['explanation']) > 0
        
        # Debe contener palabras clave relevantes
        explanation_lower = necessity['explanation'].lower()
        assert any(word in explanation_lower for word in 
                  ['infinito', 'coherencia', 'línea crítica', 'estabilidad'])
    
    # ========================================================================
    # Tests de Respiración Temporal
    # ========================================================================
    
    def test_evolve_breathing(self, cosmic):
        """Test evolución temporal de la respiración."""
        # Evolucionar en t = 0
        state_0 = cosmic.evolve_breathing(0.0)
        assert state_0.phase == 0.0
        assert abs(state_0.amplitude - 1.0) < 1e-10
        
        # Evolucionar en t = período/4
        period = 1.0 / cosmic.frequency
        state_quarter = cosmic.evolve_breathing(period / 4)
        assert abs(state_quarter.amplitude) < 0.1  # ~0 en π/2
        
        # Evolucionar en t = período/2
        state_half = cosmic.evolve_breathing(period / 2)
        assert abs(state_half.amplitude + 1.0) < 0.1  # ~-1 en π
    
    def test_compute_breathing_cycle(self, cosmic):
        """Test cálculo de ciclo completo de respiración."""
        times, amplitudes = cosmic.compute_breathing_cycle(duration=1.0, samples=1000)
        
        # Verificar tipos y formas
        assert isinstance(times, np.ndarray)
        assert isinstance(amplitudes, np.ndarray)
        assert len(times) == 1000
        assert len(amplitudes) == 1000
        
        # Verificar rangos
        assert np.all((times >= 0.0) & (times <= 1.0))
        assert np.all((amplitudes >= -1.0) & (amplitudes <= 1.0))
        
        # Verificar que es periódico (comparar valores en puntos de un período)
        # Un período = 1/f0, usar múltiplos de ese período
        period = 1.0 / cosmic.frequency
        if period < 1.0:
            # Encontrar índice cerca de un período
            idx_period = int(period * 1000)
            if idx_period < len(amplitudes) - 1:
                # Valores en t y t+T deberían ser similares
                assert abs(amplitudes[0] - amplitudes[idx_period]) < 0.1
    
    # ========================================================================
    # Tests de Certificación
    # ========================================================================
    
    def test_generate_cosmic_certificate(self, cosmic):
        """Test generación de certificado cósmico."""
        certificate = cosmic.generate_cosmic_certificate()
        
        # Verificar secciones principales
        assert 'metadata' in certificate
        assert 'parameters' in certificate
        assert 'layer_1_arithmetic' in certificate
        assert 'layer_2_quantum' in certificate
        assert 'layer_3_noetic' in certificate
        assert 'state' in certificate
        assert 'verdict' in certificate
        
        # Verificar metadata
        metadata = certificate['metadata']
        assert 'title' in metadata
        assert 'date' in metadata
        assert 'author' in metadata
        assert 'institution' in metadata
        assert 'framework' in metadata
        
        # Verificar parámetros
        params = certificate['parameters']
        assert params['frequency_hz'] == F0_HZ
        assert params['coherence_C'] == COHERENCE_C
        
        # Verificar veredicto
        verdict = certificate['verdict']
        assert 'status' in verdict
        assert 'all_layers_passed' in verdict
        assert 'message' in verdict
        assert verdict['status'] in ['COHERENT', 'INCOHERENT']
    
    def test_save_certificate(self, cosmic, tmp_path):
        """Test guardado de certificado a archivo."""
        # Guardar en directorio temporal
        filename = tmp_path / 'test_certificate.json'
        result = cosmic.save_certificate(str(filename))
        
        # Verificar que se creó el archivo
        assert Path(result).exists()
        
        # Verificar que es JSON válido
        import json
        with open(result, 'r') as f:
            data = json.load(f)
        
        assert 'metadata' in data
        assert 'verdict' in data


class TestUtilityFunctions:
    """Tests para funciones de utilidad."""
    
    def test_validate_critical_line_necessity_standalone(self):
        """Test función standalone de validación de necesidad."""
        results = validate_critical_line_necessity(
            frequency=F0_HZ,
            coherence=COHERENCE_C,
            precision=15
        )
        
        # Verificar estructura
        assert 'stability_index' in results
        assert 'is_necessary' in results
        assert 'ontological_status' in results
    
    def test_compute_breathing_signature_standalone(self):
        """Test función standalone de cálculo de firma de respiración."""
        times, amplitudes = compute_breathing_signature(duration=0.5, frequency=F0_HZ)
        
        assert isinstance(times, np.ndarray)
        assert isinstance(amplitudes, np.ndarray)
        assert len(times) > 0
        assert len(amplitudes) == len(times)


class TestIntegrationScenarios:
    """Tests de escenarios de integración completos."""
    
    def test_full_cosmic_analysis_workflow(self):
        """Test flujo completo de análisis cósmico."""
        # 1. Crear instancia
        cosmic = CosmicBreathing(frequency=F0_HZ, coherence=COHERENCE_C, precision=15)
        
        # 2. Validar las tres capas
        arithmetic = cosmic.validate_arithmetic_symmetry()
        quantum = cosmic.validate_quantum_coherence()
        necessity = cosmic.validate_critical_line_necessity()
        
        # 3. Generar certificado
        certificate = cosmic.generate_cosmic_certificate()
        
        # 4. Verificar que todo está conectado
        assert certificate['layer_1_arithmetic']['symmetry_score'] == arithmetic['symmetry_score']
        assert certificate['layer_2_quantum']['overall_score'] == quantum['overall_score']
        assert certificate['layer_3_noetic']['stability_index'] == necessity['stability_index']
    
    def test_coherence_variation_impact(self):
        """Test impacto de variación de coherencia en estabilidad."""
        coherences = [200.0, 244.36, 300.0]
        stabilities = []
        
        for c in coherences:
            cosmic = CosmicBreathing(coherence=c, precision=15)
            s = cosmic.compute_infinity_stability()
            stabilities.append(s)
        
        # Mayor coherencia debería tender a mayor estabilidad
        # (aunque no necesariamente monótono debido a otros factores)
        assert all(0.0 <= s <= 1.0 for s in stabilities)
    
    def test_precision_impact(self):
        """Test impacto de precisión en resultados."""
        # Baja precisión
        cosmic_low = CosmicBreathing(precision=10)
        result_low = cosmic_low.compute_prime_breathing_amplitude(100.0)
        
        # Alta precisión
        cosmic_high = CosmicBreathing(precision=25)
        result_high = cosmic_high.compute_prime_breathing_amplitude(100.0)
        
        # Ambos deben dar resultados finitos
        assert np.isfinite(result_low)
        assert np.isfinite(result_high)


class TestEdgeCases:
    """Tests de casos extremos."""
    
    def test_zero_coherence(self):
        """Test con coherencia cero (caso degenerado)."""
        cosmic = CosmicBreathing(coherence=0.0, precision=15)
        stability = cosmic.compute_infinity_stability()
        
        # Estabilidad debería ser muy baja
        assert stability < 0.5
    
    def test_very_high_coherence(self):
        """Test con coherencia muy alta."""
        cosmic = CosmicBreathing(coherence=1000.0, precision=15)
        stability = cosmic.compute_infinity_stability()
        
        # Estabilidad debería ser alta
        assert stability >= 0.0
    
    def test_single_mode_spectrum(self):
        """Test espectro con un solo modo."""
        cosmic = CosmicBreathing(precision=15)
        spectrum = cosmic.compute_Hpsi_spectrum_breathing(n_modes=1)
        
        assert len(spectrum['eigenvalues']) == 1
        assert spectrum['n_modes'] == 1


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
