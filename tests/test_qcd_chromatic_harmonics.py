#!/usr/bin/env python3
"""
Tests for QCD Chromatic Harmonics Module
=========================================

Comprehensive test suite for the QCD chromatic harmonics spectral framework.

Autor: José Manuel Mota Burruezo Ψ ✧ ∞³
"""

import pytest
import math
import cmath
import sys
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from qcd_chromatic_harmonics import (
    QuarkFlavor, QuantumColor,
    F0_HZ, PRIMO_17, GAMMA_17, COSMIC_HEARTBEAT,
    calcular_frecuencia_quark,
    calcular_fase_color,
    calcular_wavefunction_quark,
    calcular_frecuencia_gluon,
    generar_estados_quarks,
    generar_estados_gluones,
    calcular_coherencia_total,
    calcular_resonancia_qcd,
    analizar_espectro_temporal,
    obtener_info_sistema,
    RIEMANN_ZEROS
)


class TestConstants:
    """Test QCAL constants and Riemann zeros"""
    
    def test_fundamental_constants(self):
        """Test fundamental QCAL constants"""
        assert F0_HZ == 141.7001
        assert PRIMO_17 == 17
        assert GAMMA_17 == 69.546402
        assert abs(COSMIC_HEARTBEAT - 2.037490) < 0.001
    
    def test_riemann_zeros_count(self):
        """Test that we have 25 Riemann zeros"""
        assert len(RIEMANN_ZEROS) == 25
    
    def test_riemann_zeros_ordering(self):
        """Test that Riemann zeros are in ascending order"""
        for i in range(len(RIEMANN_ZEROS) - 1):
            assert RIEMANN_ZEROS[i] < RIEMANN_ZEROS[i+1]
    
    def test_gamma_17_value(self):
        """Test that γ₁₇ matches the 17th zero"""
        assert RIEMANN_ZEROS[16] == GAMMA_17


class TestQuarkFlavors:
    """Test quark flavor enumeration and frequencies"""
    
    def test_quark_flavor_count(self):
        """Test that we have 6 quark flavors"""
        assert len(list(QuarkFlavor)) == 6
    
    def test_quark_flavor_values(self):
        """Test quark flavor enumeration values"""
        assert QuarkFlavor.UP.value == 1
        assert QuarkFlavor.DOWN.value == 2
        assert QuarkFlavor.CHARM.value == 3
        assert QuarkFlavor.STRANGE.value == 4
        assert QuarkFlavor.TOP.value == 5
        assert QuarkFlavor.BOTTOM.value == 6
    
    def test_calcular_frecuencia_quark_up(self):
        """Test UP quark frequency calculation"""
        f_up = calcular_frecuencia_quark(QuarkFlavor.UP)
        # f_up = 141.7001 * (14.134725 / 69.546402)
        expected = F0_HZ * (RIEMANN_ZEROS[0] / GAMMA_17)
        assert abs(f_up - expected) < 1e-6
    
    def test_calcular_frecuencia_quark_down(self):
        """Test DOWN quark frequency calculation"""
        f_down = calcular_frecuencia_quark(QuarkFlavor.DOWN)
        expected = F0_HZ * (RIEMANN_ZEROS[1] / GAMMA_17)
        assert abs(f_down - expected) < 1e-6
    
    def test_quark_frequencies_positive(self):
        """Test that all quark frequencies are positive"""
        for flavor in QuarkFlavor:
            freq = calcular_frecuencia_quark(flavor)
            assert freq > 0
    
    def test_quark_frequencies_ascending(self):
        """Test that quark frequencies increase with flavor"""
        freqs = [calcular_frecuencia_quark(f) for f in QuarkFlavor]
        for i in range(len(freqs) - 1):
            assert freqs[i] < freqs[i+1]


class TestQuantumColors:
    """Test quantum color enumeration and phases"""
    
    def test_quantum_color_count(self):
        """Test that we have 3 quantum colors"""
        assert len(list(QuantumColor)) == 3
    
    def test_quantum_color_phases(self):
        """Test quantum color phase values"""
        assert QuantumColor.ROJO.value == 0
        assert QuantumColor.VERDE.value == 120
        assert QuantumColor.AZUL.value == 240
    
    def test_calcular_fase_color_rojo(self):
        """Test ROJO color phase (0°)"""
        fase = calcular_fase_color(QuantumColor.ROJO)
        assert abs(fase - 0.0) < 1e-10
    
    def test_calcular_fase_color_verde(self):
        """Test VERDE color phase (120°)"""
        fase = calcular_fase_color(QuantumColor.VERDE)
        expected = math.radians(120)
        assert abs(fase - expected) < 1e-10
    
    def test_calcular_fase_color_azul(self):
        """Test AZUL color phase (240°)"""
        fase = calcular_fase_color(QuantumColor.AZUL)
        expected = math.radians(240)
        assert abs(fase - expected) < 1e-10
    
    def test_su3_symmetry(self):
        """Test SU(3) symmetry: sum of phase exponentials should be zero"""
        sum_phases = sum(
            cmath.exp(1j * calcular_fase_color(color))
            for color in QuantumColor
        )
        assert abs(sum_phases) < 1e-10


class TestGluonStates:
    """Test gluon state calculations"""
    
    def test_calcular_frecuencia_gluon_range(self):
        """Test that gluon frequency ratios are in [1.036, 1.277]"""
        for i in range(1, 9):
            _, _, ratio = calcular_frecuencia_gluon(i)
            assert 1.03 < ratio < 1.28
    
    def test_calcular_frecuencia_gluon_invalid(self):
        """Test that invalid gluon indices raise ValueError"""
        with pytest.raises(ValueError):
            calcular_frecuencia_gluon(0)
        with pytest.raises(ValueError):
            calcular_frecuencia_gluon(9)
    
    def test_gluon_gamma_indices(self):
        """Test that gluons map to γ₁₈-γ₂₅"""
        for i in range(1, 9):
            _, gamma_idx, _ = calcular_frecuencia_gluon(i)
            assert gamma_idx == 17 + i
    
    def test_generar_estados_gluones_count(self):
        """Test that we generate 8 gluon states"""
        gluones = generar_estados_gluones()
        assert len(gluones) == 8
    
    def test_generar_estados_gluones_indices(self):
        """Test gluon state indices"""
        gluones = generar_estados_gluones()
        for i, gluon in enumerate(gluones, 1):
            assert gluon.index == i
            assert gluon.gamma_index == 17 + i


class TestQuarkWaveFunctions:
    """Test quark wave function calculations"""
    
    def test_wavefunction_quark_unit_amplitude(self):
        """Test that wave function has unit amplitude by default"""
        psi = calcular_wavefunction_quark(QuarkFlavor.UP, QuantumColor.ROJO, 0.5)
        assert abs(abs(psi) - 1.0) < 1e-10
    
    def test_wavefunction_quark_is_complex(self):
        """Test that wave function returns complex number"""
        psi = calcular_wavefunction_quark(QuarkFlavor.UP, QuantumColor.ROJO, 0.5)
        assert isinstance(psi, complex)
    
    def test_wavefunction_quark_at_t_zero(self):
        """Test wave function at t=0"""
        # At t=0: Ψ = A·exp(i·φ_c)·1 = A·exp(i·φ_c)
        psi_rojo = calcular_wavefunction_quark(QuarkFlavor.UP, QuantumColor.ROJO, 0.0)
        # ROJO phase = 0, so Ψ ≈ 1
        assert abs(psi_rojo - 1.0) < 1e-10
        
        psi_verde = calcular_wavefunction_quark(QuarkFlavor.UP, QuantumColor.VERDE, 0.0)
        # VERDE phase = 120°
        expected = cmath.exp(1j * math.radians(120))
        assert abs(psi_verde - expected) < 1e-10
    
    def test_wavefunction_quark_custom_amplitude(self):
        """Test wave function with custom amplitude"""
        A = 2.5
        psi = calcular_wavefunction_quark(QuarkFlavor.UP, QuantumColor.ROJO, 0.5, amplitud=A)
        assert abs(abs(psi) - A) < 1e-10
    
    def test_wavefunction_quark_all_flavors(self):
        """Test wave function for all quark flavors"""
        t = 0.5
        for flavor in QuarkFlavor:
            psi = calcular_wavefunction_quark(flavor, QuantumColor.ROJO, t)
            assert abs(abs(psi) - 1.0) < 1e-10
    
    def test_wavefunction_quark_all_colors(self):
        """Test wave function for all quantum colors"""
        t = 0.5
        for color in QuantumColor:
            psi = calcular_wavefunction_quark(QuarkFlavor.UP, color, t)
            assert abs(abs(psi) - 1.0) < 1e-10


class TestQuarkStates:
    """Test quark state generation"""
    
    def test_generar_estados_quarks_count(self):
        """Test that we generate 18 quark-color states"""
        estados = generar_estados_quarks(0.5)
        assert len(estados) == 18
    
    def test_generar_estados_quarks_all_flavors(self):
        """Test that all 6 flavors are represented"""
        estados = generar_estados_quarks(0.5)
        flavors = {estado.flavor for estado in estados}
        assert len(flavors) == 6
        assert flavors == set(QuarkFlavor)
    
    def test_generar_estados_quarks_all_colors(self):
        """Test that all 3 colors are represented for each flavor"""
        estados = generar_estados_quarks(0.5)
        for flavor in QuarkFlavor:
            colors = {e.color for e in estados if e.flavor == flavor}
            assert len(colors) == 3
            assert colors == set(QuantumColor)
    
    def test_generar_estados_quarks_frequencies(self):
        """Test that quark states have correct frequencies"""
        estados = generar_estados_quarks(0.5)
        for estado in estados:
            expected_freq = calcular_frecuencia_quark(estado.flavor)
            assert abs(estado.frequency - expected_freq) < 1e-10
    
    def test_generar_estados_quarks_phases(self):
        """Test that quark states have correct color phases"""
        estados = generar_estados_quarks(0.5)
        for estado in estados:
            expected_phase = calcular_fase_color(estado.color)
            assert abs(estado.phase - expected_phase) < 1e-10


class TestCoherence:
    """Test coherence calculations"""
    
    def test_calcular_coherencia_total_is_complex(self):
        """Test that total coherence is a complex number"""
        quarks = generar_estados_quarks(0.5)
        gluones = generar_estados_gluones()
        psi = calcular_coherencia_total(quarks, gluones, 0.5)
        assert isinstance(psi, complex)
    
    def test_calcular_coherencia_total_bounded(self):
        """Test that total coherence is bounded"""
        quarks = generar_estados_quarks(0.5)
        gluones = generar_estados_gluones()
        psi = calcular_coherencia_total(quarks, gluones, 0.5)
        # With normalization, |Ψ| should be reasonable
        assert abs(psi) < 10.0
    
    def test_calcular_coherencia_total_time_evolution(self):
        """Test coherence time evolution"""
        quarks = generar_estados_quarks(0.0)
        gluones = generar_estados_gluones()
        
        psi0 = calcular_coherencia_total(quarks, gluones, 0.0)
        psi1 = calcular_coherencia_total(quarks, gluones, 0.1)
        
        # Coherence should evolve (different values at different times)
        assert abs(psi0 - psi1) > 1e-10


class TestResonanceState:
    """Test QCD resonance state calculations"""
    
    def test_calcular_resonancia_qcd_structure(self):
        """Test resonance state structure"""
        estado = calcular_resonancia_qcd(0.5)
        assert estado.time == 0.5
        assert len(estado.quark_states) == 18
        assert len(estado.gluon_states) == 8
        assert isinstance(estado.coherence_psi, complex)
        assert isinstance(estado.spectral_amplitude, float)
        assert isinstance(estado.spectral_phase, float)
    
    def test_calcular_resonancia_qcd_amplitude_positive(self):
        """Test that spectral amplitude is positive"""
        estado = calcular_resonancia_qcd(0.5)
        assert estado.spectral_amplitude >= 0
    
    def test_calcular_resonancia_qcd_amplitude_matches(self):
        """Test that spectral amplitude matches |Ψ|"""
        estado = calcular_resonancia_qcd(0.5)
        assert abs(estado.spectral_amplitude - abs(estado.coherence_psi)) < 1e-10
    
    def test_calcular_resonancia_qcd_phase_matches(self):
        """Test that spectral phase matches arg(Ψ)"""
        estado = calcular_resonancia_qcd(0.5)
        expected_phase = cmath.phase(estado.coherence_psi)
        assert abs(estado.spectral_phase - expected_phase) < 1e-10
    
    def test_calcular_resonancia_qcd_phase_range(self):
        """Test that spectral phase is in [-π, π]"""
        estado = calcular_resonancia_qcd(0.5)
        assert -math.pi <= estado.spectral_phase <= math.pi
    
    def test_calcular_resonancia_qcd_multiple_times(self):
        """Test resonance calculation at multiple times"""
        times = [0.0, 0.25, 0.5, 0.75, 1.0]
        for t in times:
            estado = calcular_resonancia_qcd(t)
            assert estado.time == t
            assert len(estado.quark_states) == 18
            assert len(estado.gluon_states) == 8


class TestSpectralAnalysis:
    """Test spectral analysis functions"""
    
    def test_analizar_espectro_temporal_structure(self):
        """Test spectral analysis output structure"""
        espectro = analizar_espectro_temporal(0, 1, 10)
        assert 'tiempos' in espectro
        assert 'amplitudes' in espectro
        assert 'fases' in espectro
        assert 'coherencia_real' in espectro
        assert 'coherencia_imag' in espectro
    
    def test_analizar_espectro_temporal_length(self):
        """Test spectral analysis array lengths"""
        n_puntos = 50
        espectro = analizar_espectro_temporal(0, 1, n_puntos)
        assert len(espectro['tiempos']) == n_puntos
        assert len(espectro['amplitudes']) == n_puntos
        assert len(espectro['fases']) == n_puntos
        assert len(espectro['coherencia_real']) == n_puntos
        assert len(espectro['coherencia_imag']) == n_puntos
    
    def test_analizar_espectro_temporal_time_range(self):
        """Test spectral analysis time range"""
        t_start, t_end = 0.0, 2.0
        espectro = analizar_espectro_temporal(t_start, t_end, 20)
        assert espectro['tiempos'][0] == t_start
        assert espectro['tiempos'][-1] == t_end
    
    def test_analizar_espectro_temporal_amplitudes_positive(self):
        """Test that all amplitudes are non-negative"""
        espectro = analizar_espectro_temporal(0, 1, 20)
        assert all(amp >= 0 for amp in espectro['amplitudes'])
    
    def test_analizar_espectro_temporal_phases_range(self):
        """Test that all phases are in [-π, π]"""
        espectro = analizar_espectro_temporal(0, 1, 20)
        assert all(-math.pi <= fase <= math.pi for fase in espectro['fases'])


class TestSystemInfo:
    """Test system information functions"""
    
    def test_obtener_info_sistema_structure(self):
        """Test system info structure"""
        info = obtener_info_sistema()
        assert 'f0_hz' in info
        assert 'primo_17' in info
        assert 'gamma_17' in info
        assert 'cosmic_heartbeat_hz' in info
        assert 'n_quarks' in info
        assert 'n_colors' in info
        assert 'n_quark_states' in info
        assert 'n_gluons' in info
    
    def test_obtener_info_sistema_values(self):
        """Test system info values"""
        info = obtener_info_sistema()
        assert info['f0_hz'] == F0_HZ
        assert info['primo_17'] == PRIMO_17
        assert info['gamma_17'] == GAMMA_17
        assert info['n_quarks'] == 6
        assert info['n_colors'] == 3
        assert info['n_quark_states'] == 18
        assert info['n_gluons'] == 8
    
    def test_obtener_info_sistema_frequency_ranges(self):
        """Test system info frequency ranges"""
        info = obtener_info_sistema()
        assert 'frequency_range_quarks' in info
        assert 'frequency_range_gluons' in info
        
        fq_min, fq_max = info['frequency_range_quarks']
        assert fq_min < fq_max
        assert fq_min > 0
        
        fg_min, fg_max = info['frequency_range_gluons']
        assert fg_min < fg_max
        assert fg_min > 0


class TestIntegration:
    """Integration tests"""
    
    def test_full_qcd_calculation(self):
        """Test complete QCD calculation workflow"""
        # Calculate state
        estado = calcular_resonancia_qcd(0.5)
        
        # Verify structure
        assert len(estado.quark_states) == 18
        assert len(estado.gluon_states) == 8
        
        # Verify all quark states
        for q_state in estado.quark_states:
            assert q_state.flavor in QuarkFlavor
            assert q_state.color in QuantumColor
            assert q_state.frequency > 0
            assert 1 <= q_state.gamma_index <= 6
        
        # Verify all gluon states
        for g_state in estado.gluon_states:
            assert 1 <= g_state.index <= 8
            assert g_state.frequency > 0
            assert 18 <= g_state.gamma_index <= 25
            assert 1.03 < g_state.frequency_ratio < 1.28
    
    def test_temporal_evolution_consistency(self):
        """Test temporal evolution consistency"""
        espectro = analizar_espectro_temporal(0, 1, 100)
        
        # Check that evolution is continuous (no jumps)
        amplitudes = espectro['amplitudes']
        for i in range(len(amplitudes) - 1):
            # Amplitudes should not jump by more than 1.0 per step
            diff = abs(amplitudes[i+1] - amplitudes[i])
            assert diff < 1.0
    
    def test_qcd_prime_riemann_connection(self):
        """Test QCD-Prime-Riemann connection"""
        # Verify that COSMIC_HEARTBEAT connects F0 and GAMMA_17
        assert abs(COSMIC_HEARTBEAT - F0_HZ / GAMMA_17) < 1e-10
        
        # Verify that quark frequencies scale with Riemann zeros
        for flavor in QuarkFlavor:
            f_quark = calcular_frecuencia_quark(flavor)
            gamma_n = RIEMANN_ZEROS[flavor.value - 1]
            expected = F0_HZ * (gamma_n / GAMMA_17)
            assert abs(f_quark - expected) < 1e-10


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
