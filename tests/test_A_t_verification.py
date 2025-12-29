"""
Test suite for echo_qcal A_t verification module

Tests the Temporal Alignment Verifier (Aₜ) for the Coherence Sovereignty Theorem (ℂₛ)
"""

import pytest
import json
import os
from echo_qcal.A_t_verification import TemporalAlignmentVerifier


class TestTemporalAlignmentVerifier:
    """Tests for the TemporalAlignmentVerifier class"""
    
    def setup_method(self):
        """Setup test fixture"""
        self.verifier = TemporalAlignmentVerifier()
    
    def test_initialization(self):
        """Test that verifier initializes with correct QCAL parameters"""
        assert self.verifier.f0 == 141.7001, "Frecuencia primordial debe ser 141.7001 Hz"
        assert abs(self.verifier.tau0 - (1 / 141.7001)) < 1e-10, "τ₀ debe ser 1/f₀"
        assert self.verifier.block9_timestamp == 1231511700.000000, "Block 9 timestamp incorrecto"
        assert self.verifier.block9_hash == "000000008d9dc510f23c2657fc4f67bea30078cc05a90eb89e84cc475c080805"
        
    def test_threshold_values(self):
        """Test that thresholds are correctly set"""
        assert self.verifier.coherence_threshold == 99.95, "Umbral de coherencia debe ser 99.95%"
        assert self.verifier.delta_t_threshold == 0.010, "Umbral de ΔT debe ser 10 ms"
    
    def test_verify_temporal_alignment_structure(self):
        """Test that verification returns correct structure"""
        results = self.verifier.verify_temporal_alignment()
        
        # Verificar estructura del resultado
        assert isinstance(results, dict), "Resultado debe ser un diccionario"
        assert 'verification_passed' in results
        assert 'parameters' in results
        assert 'alignment_metrics' in results
        assert 'statistical_analysis' in results
        assert 'thresholds' in results
        
    def test_parameters_section(self):
        """Test parameters section of results"""
        results = self.verifier.verify_temporal_alignment()
        params = results['parameters']
        
        assert params['f0_hz'] == 141.7001
        assert params['tau0_s'] == self.verifier.tau0
        assert params['block9_timestamp'] == 1231511700.000000
        assert 'block9_datetime' in params
        assert params['block9_hash'] == self.verifier.block9_hash
        
    def test_alignment_metrics_section(self):
        """Test alignment metrics calculations"""
        results = self.verifier.verify_temporal_alignment()
        metrics = results['alignment_metrics']
        
        # Verificar que las métricas existen
        assert 'N_ideal' in metrics
        assert 'N_integer' in metrics
        assert 'T_ideal_s' in metrics
        assert 'delta_T_s' in metrics
        assert 'delta_T_ms' in metrics
        assert 'coherence_percent' in metrics
        assert 'phase' in metrics
        assert 'phase_description' in metrics
        
        # Verificar que las conversiones son correctas
        assert abs(metrics['delta_T_ms'] - metrics['delta_T_s'] * 1000) < 1e-6
        
        # Verificar que la fase está entre 0 y 1
        assert 0 <= metrics['phase'] <= 1
        
    def test_statistical_analysis_section(self):
        """Test statistical analysis calculations"""
        results = self.verifier.verify_temporal_alignment()
        stats = results['statistical_analysis']
        
        # Verificar campos
        assert 'window_s' in stats
        assert 'epsilon_s' in stats
        assert 'p_value' in stats
        assert 'bayes_factor' in stats
        assert 'significance' in stats
        
        # Verificar valores esperados
        assert stats['window_s'] == 7200  # 2 horas
        assert stats['epsilon_s'] == 0.010  # 10 ms
        
        # Verificar cálculos
        expected_p_value = (2 * 0.010) / 7200
        assert abs(stats['p_value'] - expected_p_value) < 1e-10
        
        expected_bayes = 7200 / (2 * 0.010)
        assert abs(stats['bayes_factor'] - expected_bayes) < 1e-10
        
        # Verificar significancia
        assert stats['significance'] in ['EXTREME', 'MODERATE']
        
    def test_thresholds_section(self):
        """Test thresholds section"""
        results = self.verifier.verify_temporal_alignment()
        thresholds = results['thresholds']
        
        assert thresholds['coherence_threshold_percent'] == 99.95
        assert thresholds['delta_t_threshold_s'] == 0.010
        assert thresholds['delta_t_threshold_ms'] == 10.0
        
    def test_verification_logic(self):
        """Test that verification logic is correct"""
        results = self.verifier.verify_temporal_alignment()
        
        delta_T = results['alignment_metrics']['delta_T_s']
        coherence = results['alignment_metrics']['coherence_percent']
        
        # Verificar lógica de aprobación
        expected_pass = (
            delta_T <= self.verifier.delta_t_threshold and
            coherence >= self.verifier.coherence_threshold
        )
        
        assert results['verification_passed'] == expected_pass
        
    def test_generate_report_returns_results(self):
        """Test that generate_verification_report returns the results"""
        results = self.verifier.verify_temporal_alignment()
        report = self.verifier.generate_verification_report(results)
        
        assert report == results
        
    def test_save_results_to_json(self):
        """Test JSON saving functionality"""
        results = self.verifier.verify_temporal_alignment()
        
        # Usar un nombre de archivo temporal
        test_filename = "test_A_t_results.json"
        
        try:
            saved_path = self.verifier.save_results_to_json(results, test_filename)
            
            # Verificar que la función devuelve una ruta válida y que el archivo existe
            assert saved_path, "save_results_to_json debe devolver una ruta no vacía"
            assert os.path.exists(saved_path)
            
            # Verificar que el contenido es correcto
            with open(saved_path, 'r') as f:
                loaded_results = json.load(f)
            
            # Comparar campos clave
            assert loaded_results['verification_passed'] == results['verification_passed']
            assert loaded_results['parameters']['f0_hz'] == results['parameters']['f0_hz']
            
        finally:
            # Limpiar archivo de prueba
            if os.path.exists(test_filename):
                os.remove(test_filename)
    
    def test_phase_description(self):
        """Test phase description logic"""
        results = self.verifier.verify_temporal_alignment()
        phase = results['alignment_metrics']['phase']
        description = results['alignment_metrics']['phase_description']
        
        if 0.49 < phase < 0.51:
            assert description == 'INVERSIÓN'
        else:
            assert description == 'OTRO'
    
    def test_p_value_significance(self):
        """Test p-value significance classification"""
        results = self.verifier.verify_temporal_alignment()
        p_value = results['statistical_analysis']['p_value']
        significance = results['statistical_analysis']['significance']
        
        if p_value < 1e-5:
            assert significance == 'EXTREME'
        else:
            assert significance == 'MODERATE'
    
    def test_main_function_returns_results(self):
        """Test that main function returns results"""
        from echo_qcal.A_t_verification import main
        
        results = main()
        assert isinstance(results, dict)
        assert 'verification_passed' in results
        
    def test_numerical_precision(self):
        """Test that calculations maintain sufficient precision"""
        results = self.verifier.verify_temporal_alignment()
        
        # Verificar que tau0 tiene precisión suficiente
        tau0 = results['parameters']['tau0_s']
        assert len(str(tau0).split('.')[-1]) >= 10, "tau0 debe tener al menos 10 decimales"
        
        # Verificar precisión de N_ideal
        N_ideal = results['alignment_metrics']['N_ideal']
        assert N_ideal > 0, "N_ideal debe ser positivo"


class TestTemporalAlignmentIntegration:
    """Integration tests for the complete verification flow"""
    
    def test_complete_verification_flow(self):
        """Test complete verification workflow"""
        verifier = TemporalAlignmentVerifier()
        
        # Paso 1: Verificar
        results = verifier.verify_temporal_alignment()
        assert results is not None
        
        # Paso 2: Generar reporte
        report = verifier.generate_verification_report(results)
        assert report == results
        
        # Paso 3: Guardar a JSON
        test_filename = "test_integration_results.json"
        saved_path = None
        try:
            saved_path = verifier.save_results_to_json(results, test_filename)
            assert os.path.exists(saved_path)
        finally:
            cleanup_path = saved_path or test_filename
            if cleanup_path and os.path.exists(cleanup_path):
                os.remove(cleanup_path)
    
    def test_qcal_constants_consistency(self):
        """Test consistency with QCAL ∞³ constants"""
        verifier = TemporalAlignmentVerifier()
        
        # Verificar que f0 es consistente con la documentación QCAL
        assert verifier.f0 == 141.7001, "f0 debe coincidir con .qcal_beacon"
        
        # Verificar relación τ₀ = 1/f₀
        expected_tau0 = 1.0 / verifier.f0
        assert abs(verifier.tau0 - expected_tau0) < 1e-12


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
