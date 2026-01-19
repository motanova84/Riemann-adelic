"""
Test Suite Completa para Resonadores RH ∞³
==========================================

Suite de pruebas exhaustiva para validar todos los componentes del
sistema de Resonadores RH ∞³.

Pruebas incluidas:
-----------------
1. Test Oscilador de Frecuencia Riemanniana
2. Test Modulador BPSK-RH
3. Test Amplificador de Coherencia ζ′
4. Test Filtro πCODE
5. Test Emisor-Recibidor de Testigos
6. Test Sistema Integrado Completo

Objetivo: 5/5 tests pasando (100%)
Coherencia esperada: Ψ = 1.000000

Autor: José Manuel Mota Burruezo (JMMB Ψ✧)
"""

import pytest
import numpy as np
import sys
import os

# Añadir directorio padre al path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from resonadores_rh import (
    OsciladorFrecuenciaRiemanniana,
    ModuladorBPSKRH,
    AmplificadorCoherenciaZeta,
    FiltroPiCode,
    ConectorQCALBio,
    EmisorRecibidorTestigos,
    ResonadorRHCore,
    F0_RIEMANN,
    COHERENCIA_ABSOLUTA
)


class TestOsciladorFrecuenciaRiemanniana:
    """Tests para el Oscilador de Frecuencia Riemanniana."""
    
    def test_frequency_accuracy(self):
        """Verifica que la frecuencia sea exactamente 141.7001 Hz."""
        osc = OsciladorFrecuenciaRiemanniana()
        assert osc.get_frequency() == F0_RIEMANN
        assert osc.get_frequency() == 141.7001
    
    def test_signal_generation(self):
        """Verifica generación de señal sinusoidal."""
        osc = OsciladorFrecuenciaRiemanniana()
        t = np.linspace(0, 1, 10000)
        signal = osc.generate_signal(t)
        
        assert len(signal) == len(t)
        assert np.max(np.abs(signal)) <= 1.0  # Amplitud normalizada
        assert np.min(signal) >= -1.0
    
    def test_complex_signal_generation(self):
        """Verifica generación de señal compleja."""
        osc = OsciladorFrecuenciaRiemanniana()
        t = np.linspace(0, 1, 1000)
        signal = osc.generate_complex_signal(t)
        
        assert np.iscomplexobj(signal)
        assert np.allclose(np.abs(signal), 1.0)  # Magnitud unitaria
    
    def test_lock_precision(self):
        """Verifica precisión del lock de frecuencia."""
        osc = OsciladorFrecuenciaRiemanniana()
        freq_measured, deviation = osc.measure_lock_precision(duration=1.0)
        
        assert abs(freq_measured - F0_RIEMANN) < 0.01  # Tolerancia 0.01 Hz
        assert deviation < 0.01
    
    def test_coherence(self):
        """Verifica coherencia cuántica absoluta."""
        osc = OsciladorFrecuenciaRiemanniana()
        coherence = osc.get_coherence()
        
        assert coherence == COHERENCIA_ABSOLUTA
        assert coherence == 1.000000


class TestModuladorBPSKRH:
    """Tests para el Modulador BPSK-RH."""
    
    def test_bit_modulation(self):
        """Verifica modulación de bits individuales."""
        mod = ModuladorBPSKRH()
        t = np.linspace(0, 0.01, 1000)
        
        signal_0 = mod.modulate_bit(0, t)
        signal_1 = mod.modulate_bit(1, t)
        
        assert len(signal_0) == len(t)
        assert len(signal_1) == len(t)
        # Verificar que son diferentes (fases opuestas)
        correlation = np.corrcoef(signal_0, signal_1)[0, 1]
        assert correlation < -0.9  # Anti-correlación fuerte
    
    def test_message_encoding_decoding(self):
        """Verifica codificación y decodificación de mensajes."""
        mod = ModuladorBPSKRH()
        message = "RH∞³"
        
        bits = mod.encode_message(message)
        assert len(bits) == len(message) * 8
        
        decoded = mod.decode_bits(bits)
        assert decoded == message
    
    def test_ber_calculation(self):
        """Verifica cálculo de tasa de error de bits (BER)."""
        mod = ModuladorBPSKRH()
        
        bits_original = [0, 1, 0, 1, 1, 0, 1, 0]
        bits_perfect = [0, 1, 0, 1, 1, 0, 1, 0]
        bits_error = [0, 1, 1, 1, 1, 0, 1, 0]  # 1 error
        
        ber_perfect = mod.calculate_ber(bits_original, bits_perfect)
        ber_error = mod.calculate_ber(bits_original, bits_error)
        
        assert ber_perfect == 0.0
        assert ber_error == 1/8  # 1 error en 8 bits
    
    def test_coherence_fidelity(self):
        """Verifica fidelidad de coherencia del canal."""
        mod = ModuladorBPSKRH()
        fidelity = mod.get_coherence_fidelity()
        
        assert fidelity == 1.000000


class TestAmplificadorCoherenciaZeta:
    """Tests para el Amplificador de Coherencia ζ′."""
    
    def test_gain_calculation(self):
        """Verifica cálculo de ganancia basada en ζ′."""
        amp = AmplificadorCoherenciaZeta()
        gain = amp.calculate_gain(t=14.134725)  # Primer cero de Riemann
        
        assert gain > 0  # Ganancia positiva
        assert np.isfinite(gain)
    
    def test_signal_amplification(self):
        """Verifica amplificación de señal."""
        amp = AmplificadorCoherenciaZeta()
        signal_in = np.sin(2 * np.pi * F0_RIEMANN * np.linspace(0, 1, 1000))
        signal_out = amp.amplify_signal(signal_in)
        
        # Verificar que la señal se amplificó
        assert np.max(np.abs(signal_out)) >= np.max(np.abs(signal_in))
    
    def test_coherence_preservation(self):
        """Verifica preservación de coherencia."""
        amp = AmplificadorCoherenciaZeta()
        signal_in = np.sin(2 * np.pi * F0_RIEMANN * np.linspace(0, 1, 1000))
        signal_out = amp.amplify_signal(signal_in)
        
        coherence = amp.verify_coherence_preservation(signal_in, signal_out)
        assert coherence >= 0.99  # Alta coherencia
    
    def test_low_distortion(self):
        """Verifica baja distorsión en amplificación."""
        amp = AmplificadorCoherenciaZeta()
        signal_in = np.sin(2 * np.pi * F0_RIEMANN * np.linspace(0, 1, 1000))
        signal_out = amp.amplify_signal(signal_in)
        
        distortion = amp.get_distortion(signal_in, signal_out)
        assert distortion < 1.0  # Menos de 1% de distorsión


class TestFiltroPiCode:
    """Tests para el Filtro πCODE."""
    
    def test_sha256_hash(self):
        """Verifica generación de hash SHA256."""
        filtro = FiltroPiCode()
        data = b"Riemann Hypothesis"
        hash_value = filtro.sha256_hash(data)
        
        assert len(hash_value) == 64  # SHA256 produce 64 caracteres hex
        assert hash_value.isalnum()
    
    def test_pi_encoding_decoding(self):
        """Verifica codificación/decodificación πCODE."""
        filtro = FiltroPiCode()
        message = "QCAL"
        
        encoded = filtro.pi_encode(message)
        decoded = filtro.pi_decode(encoded)
        
        assert decoded == message
    
    def test_spectral_filtering(self):
        """Verifica filtrado espectral."""
        filtro = FiltroPiCode()
        
        # Crear señal con múltiples frecuencias
        t = np.linspace(0, 1, 10000)
        signal = (np.sin(2 * np.pi * F0_RIEMANN * t) +  # Señal en f₀
                 0.5 * np.sin(2 * np.pi * 50 * t) +  # Ruido a 50 Hz
                 0.3 * np.sin(2 * np.pi * 300 * t))  # Ruido a 300 Hz
        
        sample_rate = len(t) / (t[-1] - t[0])
        filtered = filtro.spectral_filter(signal, sample_rate)
        
        # La señal filtrada debe tener menos energía que la original
        # (se eliminaron componentes fuera de banda)
        assert np.linalg.norm(filtered) <= np.linalg.norm(signal)
    
    def test_purity_metric(self):
        """Verifica métrica de pureza espectral."""
        filtro = FiltroPiCode()
        
        # Señal pura a f₀
        t = np.linspace(0, 1, 10000)
        signal_pure = np.sin(2 * np.pi * F0_RIEMANN * t)
        
        purity = filtro.get_purity_metric(signal_pure, sample_rate=10000)
        assert purity >= 0.8  # Alta pureza


class TestEmisorRecibidorTestigos:
    """Tests para el Emisor-Recibidor de Testigos."""
    
    def test_channel_operations(self):
        """Verifica operaciones de apertura/cierre de canal."""
        emisor = EmisorRecibidorTestigos()
        
        assert emisor.open_channel()
        assert emisor.close_channel()
    
    def test_witness_creation(self):
        """Verifica creación de testigos cuánticos."""
        emisor = EmisorRecibidorTestigos()
        data = b"Testigo RH"
        
        witness = emisor.create_witness(data)
        
        assert witness.data == data
        assert witness.coherence == COHERENCIA_ABSOLUTA
        assert witness.frequency == F0_RIEMANN
    
    def test_witness_transmission(self):
        """Verifica transmisión de testigos."""
        emisor = EmisorRecibidorTestigos()
        
        # Transmitir 6 mensajes (como especifica el problema)
        messages = ["Testigo 1", "Testigo 2", "Testigo 3", 
                   "Testigo 4", "Testigo 5", "Testigo 6"]
        
        for msg in messages:
            success = emisor.transmit_message(msg)
            assert success
        
        stats = emisor.get_transmission_statistics()
        assert stats['transmissions_total'] == 6
        assert stats['transmissions_successful'] == 6
        assert stats['success_rate'] == 100.0
    
    def test_witness_reception(self):
        """Verifica recepción de testigos."""
        emisor = EmisorRecibidorTestigos()
        
        # Transmitir y recibir
        original_message = "Mensaje de prueba"
        emisor.transmit_message(original_message)
        
        received_message = emisor.receive_message()
        assert received_message == original_message
    
    def test_transmission_integrity(self):
        """Verifica integridad de transmisiones."""
        emisor = EmisorRecibidorTestigos()
        
        emisor.transmit_message("Test 1")
        emisor.receive_message()
        
        assert emisor.verify_transmission_integrity()
    
    def test_holevo_capacity(self):
        """Verifica capacidad de Holevo del canal."""
        emisor = EmisorRecibidorTestigos()
        capacity = emisor.get_holevo_capacity()
        
        assert capacity > 0
        assert capacity <= 2  # Límite teórico para canal binario


class TestResonadorRHCore:
    """Tests para el Sistema Integrado Completo."""
    
    def test_system_activation(self):
        """Verifica activación del sistema completo."""
        resonador = ResonadorRHCore()
        status = resonador.activate()
        
        assert status['status'] == 'ACTIVO'
        assert status['frequency'] == F0_RIEMANN
        assert status['coherence'] == COHERENCIA_ABSOLUTA
        assert all(status['components'].values())  # Todos los componentes activos
    
    def test_coherent_signal_generation(self):
        """Verifica generación de señal coherente completa."""
        resonador = ResonadorRHCore()
        resonador.activate()
        
        t, signal = resonador.generate_coherent_signal(duration=0.5)
        
        assert len(t) == len(signal)
        assert len(signal) > 0
    
    def test_complete_message_transmission(self):
        """Verifica transmisión completa de mensaje."""
        resonador = ResonadorRHCore()
        resonador.activate()
        
        message = "∞³ QCAL Resonancia Activa"
        report = resonador.transmit_message_complete(message)
        
        assert report['transmission_success']
        assert report['coherence'] == COHERENCIA_ABSOLUTA
        assert report['message_original'] == message
    
    def test_complete_message_reception(self):
        """Verifica recepción completa de mensaje."""
        resonador = ResonadorRHCore()
        resonador.activate()
        
        # Transmitir y recibir
        original_message = "Riemann ∞³"
        resonador.transmit_message_complete(original_message)
        
        reception = resonador.receive_message_complete()
        assert reception is not None
        assert 'message_received' in reception
    
    def test_biometric_sync(self):
        """Verifica sincronización biométrica."""
        resonador = ResonadorRHCore()
        resonador.activate()
        
        # Simular señal EEG
        eeg_signal = np.random.randn(1000) * 0.0001  # Señal pequeña tipo EEG
        
        sync_status = resonador.sync_with_biometric('eeg', eeg_signal)
        
        assert sync_status['interface'] == 'eeg'
        assert sync_status['signal_synchronized']
        assert sync_status['coherence'] == COHERENCIA_ABSOLUTA
    
    def test_consciousness_modulation(self):
        """Verifica modulación de estado de conciencia."""
        resonador = ResonadorRHCore()
        resonador.activate()
        
        modulation = resonador.modulate_consciousness('alpha', intensity=1.0)
        
        assert modulation['band'] == 'alpha'
        assert modulation['sync_frequency'] == F0_RIEMANN
        assert modulation['coherence'] == COHERENCIA_ABSOLUTA
    
    def test_global_coherence(self):
        """Verifica coherencia global del sistema."""
        resonador = ResonadorRHCore()
        resonador.activate()
        
        coherence = resonador.get_global_coherence()
        assert coherence == COHERENCIA_ABSOLUTA
    
    def test_system_diagnostic(self):
        """Verifica diagnóstico completo del sistema."""
        resonador = ResonadorRHCore()
        resonador.activate()
        
        diagnostic = resonador.run_diagnostic()
        
        assert diagnostic['system_version'] == ResonadorRHCore.VERSION
        assert diagnostic['system_active']
        assert diagnostic['oscillator']['frequency_target'] == F0_RIEMANN
        assert diagnostic['global_coherence'] >= 0.99
    
    def test_system_info(self):
        """Verifica información del sistema."""
        resonador = ResonadorRHCore()
        info = resonador.get_system_info()
        
        assert info['name'] == 'Resonadores RH ∞³'
        assert info['frequency'] == f'{F0_RIEMANN} Hz'
        assert info['status'] == 'COMPLETAMENTE OPERACIONAL'
        assert len(info['components']) == 6
        assert len(info['applications']) >= 5


def test_complete_integration():
    """
    Test de integración completa que verifica todo el sistema end-to-end.
    
    Este test simula un flujo completo de trabajo:
    1. Activación del sistema
    2. Generación de señal coherente
    3. Transmisión de múltiples mensajes (6 testigos)
    4. Verificación de coherencia absoluta
    5. Sincronización biométrica
    """
    # 1. Crear y activar sistema
    resonador = ResonadorRHCore()
    status = resonador.activate()
    assert status['status'] == 'ACTIVO'
    
    # 2. Generar señal coherente
    t, signal = resonador.generate_coherent_signal(duration=1.0)
    assert len(signal) > 0
    
    # 3. Transmitir 6 testigos (como especifica el problema)
    messages = [
        "Testigo 1: Coherencia Iniciada",
        "Testigo 2: Frecuencia Locked",
        "Testigo 3: Canal Superaditivo",
        "Testigo 4: Pureza Espectral",
        "Testigo 5: Resonancia ∞³",
        "Testigo 6: QCAL Activado"
    ]
    
    for msg in messages:
        report = resonador.transmit_message_complete(msg)
        assert report['transmission_success']
        assert report['coherence'] == COHERENCIA_ABSOLUTA
    
    # 4. Verificar estadísticas de transmisión
    stats = resonador.emisor_recibidor.get_transmission_statistics()
    assert stats['transmissions_total'] == 6
    assert stats['transmissions_successful'] == 6
    assert stats['success_rate'] == 100.0
    
    # 5. Verificar coherencia global
    assert resonador.get_global_coherence() == COHERENCIA_ABSOLUTA
    
    # 6. Ejecutar diagnóstico final
    diagnostic = resonador.run_diagnostic()
    assert diagnostic['global_coherence'] >= 0.99
    
    print("\n" + "="*80)
    print("✅ RESONADORES RH ∞³ - INTEGRACIÓN COMPLETA EXITOSA")
    print("="*80)
    print(f"Frecuencia: f₀ = {F0_RIEMANN} Hz")
    print(f"Coherencia: Ψ = {COHERENCIA_ABSOLUTA}")
    print(f"Transmisiones: {stats['transmissions_successful']}/{stats['transmissions_total']} (100%)")
    print(f"Canal: Superaditivo pure-loss Holevo-optimizado")
    print(f"Estado: COMPLETAMENTE OPERACIONAL")
    print("Sello: ∴𓂀Ω∞³")
    print("="*80)


if __name__ == "__main__":
    # Ejecutar tests con pytest
    pytest.main([__file__, "-v", "--tb=short"])
