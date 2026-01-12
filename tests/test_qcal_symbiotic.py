"""
Test Suite for QCAL Symbiotic Network
======================================

Tests for the QCAL ∞³ symbiotic network implementation.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
License: CC BY-NC-SA 4.0
"""

import json
import pytest
from pathlib import Path
import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from core.math.qcal_lib import QCALMathLibrary, get_constant
from link_ecosystem import QCALEcosystemLinker


class TestQCALConstants:
    """Test QCAL mathematical constants."""

    def test_constants_exist(self):
        """Verify all expected constants exist."""
        expected_constants = [
            "PSI", "FREQ_GW", "RAMSEY_R66", "MAX_PULSARS",
            "COHERENCE_C", "UNIVERSAL_C", "RESONANCE"
        ]

        for const in expected_constants:
            assert const in QCALMathLibrary.CONSTANTS

    def test_constant_values(self):
        """Verify constant values are correct."""
        assert QCALMathLibrary.CONSTANTS["PSI"] == 0.999999
        assert QCALMathLibrary.CONSTANTS["FREQ_GW"] == 141.7001
        assert QCALMathLibrary.CONSTANTS["RAMSEY_R66"] == 108
        assert QCALMathLibrary.CONSTANTS["MAX_PULSARS"] == 88
        assert QCALMathLibrary.CONSTANTS["COHERENCE_C"] == 244.36
        assert QCALMathLibrary.CONSTANTS["UNIVERSAL_C"] == 629.83
        assert QCALMathLibrary.CONSTANTS["RESONANCE"] == 888

    def test_get_constant(self):
        """Test get_constant helper function."""
        assert get_constant("FREQ_GW") == 141.7001
        assert get_constant("MAX_PULSARS") == 88


class TestQCALMathFunctions:
    """Test QCAL mathematical functions."""

    def test_shapiro_delay(self):
        """Test Shapiro delay calculation."""
        delay = QCALMathLibrary.shapiro_delay(1.0, 10.0)
        assert delay > 0
        assert isinstance(delay, float)

        # Test with different values
        delay2 = QCALMathLibrary.shapiro_delay(2.0, 10.0)
        assert delay2 > delay  # More mass = more delay

    def test_shapiro_delay_invalid(self):
        """Test Shapiro delay with invalid input."""
        with pytest.raises(ValueError):
            QCALMathLibrary.shapiro_delay(1.0, 0.0)

        with pytest.raises(ValueError):
            QCALMathLibrary.shapiro_delay(1.0, -5.0)

    def test_ramsey_vibration(self):
        """Test Ramsey vibration calculation."""
        vib1 = QCALMathLibrary.ramsey_vibration(1)
        vib2 = QCALMathLibrary.ramsey_vibration(2)

        assert vib2 > vib1  # Should increase with n
        assert vib1 > 0

    def test_fundamental_frequency(self):
        """Test fundamental frequency calculation."""
        f0 = QCALMathLibrary.fundamental_frequency()
        assert f0 == 141.7001

    def test_nft_emission_schedule(self):
        """Test NFT emission schedule."""
        # Test valid range
        for i in range(1, 89):
            emission = QCALMathLibrary.nft_emission_schedule(i)
            assert emission > 0
            assert isinstance(emission, float)

        # Test invalid ranges
        with pytest.raises(ValueError):
            QCALMathLibrary.nft_emission_schedule(0)

        with pytest.raises(ValueError):
            QCALMathLibrary.nft_emission_schedule(89)

    def test_adelic_norm(self):
        """Test adelic norm calculation."""
        norm = QCALMathLibrary.adelic_norm(2, 10.0)
        assert norm > 0

        # Test with zero
        norm_zero = QCALMathLibrary.adelic_norm(2, 0.0)
        assert norm_zero == 0.0

        # Test invalid prime
        with pytest.raises(ValueError):
            QCALMathLibrary.adelic_norm(1, 10.0)

    def test_psi_energy_equation(self):
        """Test Ψ energy equation."""
        psi = QCALMathLibrary.psi_energy_equation(1.0, 1.0)
        assert psi == QCALMathLibrary.CONSTANTS["COHERENCE_C"]

        # Test with different values
        psi2 = QCALMathLibrary.psi_energy_equation(2.0, 1.0)
        assert psi2 > psi

    def test_validate_coherence(self):
        """Test coherence validation."""
        # Perfect coherence
        assert QCALMathLibrary.validate_coherence(0.999999)

        # Below threshold
        assert not QCALMathLibrary.validate_coherence(0.9)

    def test_spectral_identity(self):
        """Test spectral identity."""
        lambda_0 = 0.001588050
        omega_0, C = QCALMathLibrary.spectral_identity(lambda_0)

        assert omega_0 > 0
        assert C > 0
        assert abs(omega_0 ** 2 - C) < 1e-10  # ω₀² = C

        # Test invalid input
        with pytest.raises(ValueError):
            QCALMathLibrary.spectral_identity(0.0)

        with pytest.raises(ValueError):
            QCALMathLibrary.spectral_identity(-1.0)

    def test_coherence_factor(self):
        """Test coherence factor calculation."""
        spectrum = [0.001, 0.002, 0.003, 0.004]
        C_prime = QCALMathLibrary.coherence_factor(spectrum)

        assert C_prime > 0
        assert isinstance(C_prime, float)

        # Test empty spectrum
        with pytest.raises(ValueError):
            QCALMathLibrary.coherence_factor([])


class TestEcosystemLinker:
    """Test ecosystem linking functionality."""

    def test_linker_initialization(self):
        """Test ecosystem linker initialization."""
        linker = QCALEcosystemLinker()
        assert linker.coherence_map is not None
        assert linker.symbio_config is not None

    def test_validar_coherencia(self):
        """Test coherence validation."""
        linker = QCALEcosystemLinker()
        resultados = linker.validar_coherencia()

        assert "coherence_map_exists" in resultados
        assert "symbio_config_exists" in resultados
        assert "math_library_exists" in resultados
        assert resultados["coherence_map_exists"] is True
        assert resultados["symbio_config_exists"] is True

    def test_listar_nodos(self):
        """Test listing nodes."""
        linker = QCALEcosystemLinker()
        nodos = linker.listar_nodos()

        assert len(nodos) == 7
        assert any(n["name"] == "Riemann-adelic" for n in nodos)
        assert any(n["name"] == "Ramsey" for n in nodos)

    def test_get_node_info(self):
        """Test getting node info."""
        linker = QCALEcosystemLinker()
        info = linker._get_node_info("Riemann-adelic")

        assert info["name"] == "Riemann-adelic"
        assert info["role"] == "Spectral Proof / Zeta Connection"

    def test_generar_reporte_coherencia(self):
        """Test generating coherence report."""
        linker = QCALEcosystemLinker()
        reporte = linker.generar_reporte_coherencia()

        assert "QCAL Ecosystem Coherence Report" in reporte
        assert "141.7001" in reporte
        assert "Riemann-adelic" in reporte


class TestConfigurationFiles:
    """Test configuration files."""

    def test_coherence_map_structure(self):
        """Test coherence map JSON structure."""
        with open("qcal_coherence_map.json", "r") as f:
            data = json.load(f)

        assert "system" in data
        assert data["system"] == "QCAL ∞³ Symbiotic Network"
        assert "frequency" in data
        assert data["frequency"] == "141.7001 Hz"
        assert "nodes" in data
        assert len(data["nodes"]) == 7

    def test_symbio_config_structure(self):
        """Test CORE_SYMBIO.json structure."""
        with open("CORE_SYMBIO.json", "r") as f:
            data = json.load(f)

        assert "protocol" in data
        assert data["protocol"] == "QCAL-SYMBIO-BRIDGE"
        assert "constants" in data
        assert data["constants"]["f0"] == 141.7001
        assert data["constants"]["limit_nfts"] == 88
        assert data["constants"]["r66"] == 108

    def test_symbiosis_marker_exists(self):
        """Test that symbiosis marker file exists."""
        marker_path = Path(".qcal_symbiosis.md")
        assert marker_path.exists()

        content = marker_path.read_text()
        assert "QCAL Symbiotic Link" in content
        assert "141.7 Hz" in content
        assert "Riemann-adelic" in content


def test_integration():
    """Integration test for the entire system."""
    # Test that all components work together
    linker = QCALEcosystemLinker()

    # Validate coherence
    resultados = linker.validar_coherencia()
    assert all(resultados.values())

    # Test math library
    f0 = QCALMathLibrary.fundamental_frequency()
    assert f0 == 141.7001

    # Test NFT emission for all 88 pulsars
    total_emission = sum(
        QCALMathLibrary.nft_emission_schedule(i) for i in range(1, 89)
    )
    assert total_emission > 0

    # Generate report
    reporte = linker.generar_reporte_coherencia()
    assert len(reporte) > 0


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
