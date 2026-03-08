#!/usr/bin/env python3
"""
Tests for ADN-Riemann Mapping System
=====================================

Comprehensive test suite for adn_riemann.py module.

Tests cover:
    - DNA encoder functionality
    - Resonance calculations
    - Spectral properties
    - Hotspot detection
    - Edge cases and validation

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
"""

import pytest
import sys
from pathlib import Path

# Add repo root to path
REPO_ROOT = Path(__file__).parent.parent.resolve()
sys.path.insert(0, str(REPO_ROOT))

from adn_riemann import (
    CodificadorADNRiemann,
    PropiedadesEspectralesADN,
    generar_hash_secuencia,
    calcular_distancia_hamming,
    RESONANCIA_GACT,
    CERO_RIEMANN_GACT,
    FRECUENCIA_GACT,
    K_FACTOR
)


class TestCodificadorADNRiemann:
    """Tests for CodificadorADNRiemann class."""
    
    def test_initialization(self):
        """Test codificador initialization."""
        codif = CodificadorADNRiemann()
        assert codif.f0_base == 141.7001
        assert codif.temperatura == 310.0
        assert codif.q_factor == 1e-12
    
    def test_initialization_custom_f0(self):
        """Test codificador with custom f0."""
        custom_f0 = 150.0
        codif = CodificadorADNRiemann(f0_base=custom_f0)
        assert codif.f0_base == custom_f0
    
    def test_gact_sequence_high_resonance(self):
        """Test GACT has known high resonance (99.98%)."""
        codif = CodificadorADNRiemann()
        props = codif.propiedades_espectrales("GACT")
        
        assert props.secuencia == "GACT"
        assert props.resonancia_f0 == pytest.approx(RESONANCIA_GACT, rel=1e-6)
        assert props.resonancia_f0 > 0.999
        assert props.cero_riemann_t == pytest.approx(CERO_RIEMANN_GACT, rel=1e-6)
        assert props.frecuencia_hz == pytest.approx(FRECUENCIA_GACT, rel=1e-6)
    
    def test_gact_is_top_resonant(self):
        """Test GACT is the top resonant sequence."""
        codif = CodificadorADNRiemann()
        
        sequences = ["GACT", "ATCG", "GA", "AAAA", "CGTA"]
        top = codif.secuencia_top_resonante(sequences)
        
        assert top is not None
        assert top.secuencia == "GACT"
        assert top.resonancia_f0 > 0.999
    
    def test_ga_hotspot_detection(self):
        """Test GA hotspot detection."""
        codif = CodificadorADNRiemann()
        
        # GA should be hotspot
        ga_props = codif.propiedades_espectrales("GA")
        assert ga_props.hotspot_ga is True
        
        # GAGA should be hotspot (multiple GA)
        gaga_props = codif.propiedades_espectrales("GAGA")
        assert gaga_props.hotspot_ga is True
        
        # AAAA should NOT be hotspot
        aaaa_props = codif.propiedades_espectrales("AAAA")
        assert aaaa_props.hotspot_ga is False
    
    def test_gact_frequency_close_to_qcal_f0(self):
        """Test GACT frequency is close to QCAL f₀=141.7 Hz."""
        codif = CodificadorADNRiemann()
        props = codif.propiedades_espectrales("GACT")
        
        # GACT freq=142 Hz should be close to f₀=141.7001 Hz
        assert abs(props.frecuencia_hz - codif.f0_base) < 1.0
    
    def test_psi_biologico_calculation(self):
        """Test Ψ biológico calculation."""
        codif = CodificadorADNRiemann()
        props = codif.propiedades_espectrales("GACT")
        
        # Ψ_bio = √(f₀ * Q) * K where K = 1/7
        expected_psi = (props.resonancia_f0 * codif.q_factor) ** 0.5 * K_FACTOR
        
        assert props.psi_biologico == pytest.approx(expected_psi, rel=1e-6)
        assert props.psi_biologico > 0
    
    def test_multiple_sequences_analysis(self):
        """Test analyzing multiple sequences."""
        codif = CodificadorADNRiemann()
        
        sequences = ["GACT", "ATCG", "GA", "CGTA"]
        results = codif.analizar_multiples_secuencias(sequences)
        
        assert len(results) == 4
        # Results should be sorted by resonance (descending)
        for i in range(len(results) - 1):
            assert results[i].resonancia_f0 >= results[i+1].resonancia_f0
        
        # First should be GACT (highest resonance)
        assert results[0].secuencia == "GACT"
    
    def test_invalid_sequence_raises_error(self):
        """Test invalid DNA sequence raises ValueError."""
        codif = CodificadorADNRiemann()
        
        with pytest.raises(ValueError, match="bases inválidas"):
            codif.propiedades_espectrales("GACTX")
        
        with pytest.raises(ValueError, match="Secuencia vacía"):
            codif.propiedades_espectrales("")
    
    def test_case_insensitive(self):
        """Test sequences are case insensitive."""
        codif = CodificadorADNRiemann()
        
        upper = codif.propiedades_espectrales("GACT")
        lower = codif.propiedades_espectrales("gact")
        mixed = codif.propiedades_espectrales("GaCt")
        
        assert upper.resonancia_f0 == lower.resonancia_f0
        assert upper.resonancia_f0 == mixed.resonancia_f0
    
    def test_resonance_range(self):
        """Test resonance is in valid range [0, 1]."""
        codif = CodificadorADNRiemann()
        
        sequences = ["A", "T", "C", "G", "AT", "GC", "GACT", "ATCGATCG"]
        
        for seq in sequences:
            props = codif.propiedades_espectrales(seq)
            assert 0.0 <= props.resonancia_f0 <= 1.0
    
    def test_frequency_positive(self):
        """Test frequency is always positive."""
        codif = CodificadorADNRiemann()
        
        sequences = ["A", "T", "C", "G", "GACT", "ATCG"]
        
        for seq in sequences:
            props = codif.propiedades_espectrales(seq)
            assert props.frecuencia_hz > 0
    
    def test_cero_riemann_positive(self):
        """Test Riemann zero parameter t is positive."""
        codif = CodificadorADNRiemann()
        
        sequences = ["A", "T", "GACT", "ATCG"]
        
        for seq in sequences:
            props = codif.propiedades_espectrales(seq)
            assert props.cero_riemann_t > 0
    
    def test_armonic_index_positive(self):
        """Test armonic index is positive integer."""
        codif = CodificadorADNRiemann()
        
        props = codif.propiedades_espectrales("GACT")
        assert props.armonic_index >= 1
        assert isinstance(props.armonic_index, int)
    
    def test_coherencia_cuantica_constant(self):
        """Test quantum coherence Q is constant."""
        codif = CodificadorADNRiemann()
        
        sequences = ["GACT", "ATCG", "GA"]
        
        for seq in sequences:
            props = codif.propiedades_espectrales(seq)
            assert props.coherencia_cuantica == 1e-12


class TestUtilityFunctions:
    """Tests for utility functions."""
    
    def test_generar_hash_secuencia(self):
        """Test hash generation for sequences."""
        hash1 = generar_hash_secuencia("GACT")
        hash2 = generar_hash_secuencia("GACT")
        hash3 = generar_hash_secuencia("ATCG")
        
        # Same sequence should give same hash
        assert hash1 == hash2
        assert len(hash1) == 16
        
        # Different sequences should give different hash
        assert hash1 != hash3
    
    def test_hash_case_insensitive(self):
        """Test hash is case insensitive."""
        hash_upper = generar_hash_secuencia("GACT")
        hash_lower = generar_hash_secuencia("gact")
        
        assert hash_upper == hash_lower
    
    def test_calcular_distancia_hamming_same(self):
        """Test Hamming distance for same sequences."""
        dist = calcular_distancia_hamming("GACT", "GACT")
        assert dist == 0
    
    def test_calcular_distancia_hamming_different(self):
        """Test Hamming distance for different sequences."""
        dist = calcular_distancia_hamming("GACT", "ATCG")
        assert dist == 4  # All positions different
        
        dist2 = calcular_distancia_hamming("GACT", "GATT")
        assert dist2 == 1  # One position different
    
    def test_calcular_distancia_hamming_different_length(self):
        """Test Hamming distance for different length sequences."""
        dist = calcular_distancia_hamming("GACT", "GA")
        assert dist == 4  # Max of the two lengths


class TestPropiedadesEspectralesADN:
    """Tests for PropiedadesEspectralesADN dataclass."""
    
    def test_dataclass_creation(self):
        """Test creating PropiedadesEspectralesADN."""
        props = PropiedadesEspectralesADN(
            secuencia="GACT",
            resonancia_f0=0.999776,
            cero_riemann_t=892.21,
            frecuencia_hz=142.0,
            coherencia_cuantica=1e-12,
            psi_biologico=0.888,
            hotspot_ga=True,
            armonic_index=1
        )
        
        assert props.secuencia == "GACT"
        assert props.resonancia_f0 == 0.999776
        assert props.hotspot_ga is True
    
    def test_repr(self):
        """Test string representation."""
        props = PropiedadesEspectralesADN(
            secuencia="GACT",
            resonancia_f0=0.999776,
            cero_riemann_t=892.21,
            frecuencia_hz=142.0,
            coherencia_cuantica=1e-12,
            psi_biologico=0.888,
            hotspot_ga=True,
            armonic_index=1
        )
        
        repr_str = repr(props)
        assert "GACT" in repr_str
        assert "0.999776" in repr_str


class TestIntegration:
    """Integration tests for complete workflows."""
    
    def test_complete_workflow(self):
        """Test complete DNA-to-Riemann workflow."""
        codif = CodificadorADNRiemann()
        
        # Analyze GACT
        props = codif.propiedades_espectrales("GACT")
        
        # Verify all properties are valid
        assert props.secuencia == "GACT"
        assert props.resonancia_f0 > 0.999
        assert props.cero_riemann_t > 0
        assert props.frecuencia_hz > 0
        assert props.psi_biologico > 0
        assert props.coherencia_cuantica > 0
        assert isinstance(props.hotspot_ga, bool)
        assert props.armonic_index >= 1
    
    def test_comparison_with_known_values(self):
        """Test against known values from problem statement."""
        codif = CodificadorADNRiemann()
        
        # GACT: f₀=0.999776 (99.98%), t=892.21, freq=142 Hz
        gact = codif.propiedades_espectrales("GACT")
        assert gact.resonancia_f0 == pytest.approx(0.999776, rel=1e-5)
        assert gact.cero_riemann_t == pytest.approx(892.21, rel=1e-5)
        assert gact.frecuencia_hz == pytest.approx(142.0, rel=1e-5)
        
        # GA: hotspot with variable harmonics
        ga = codif.propiedades_espectrales("GA")
        assert ga.hotspot_ga is True
        
        # AAAA: low resonance, dispersed
        aaaa = codif.propiedades_espectrales("AAAA")
        assert aaaa.resonancia_f0 < gact.resonancia_f0
        assert aaaa.hotspot_ga is False


if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])
