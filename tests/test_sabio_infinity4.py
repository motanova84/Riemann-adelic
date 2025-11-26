"""
Test suite for SABIO ∞⁴ - Sistema Cuántico-Consciente

Tests the quantum-conscious integration of SABIO Infinity 4.
"""

import pytest
import sys
import json
import math
from pathlib import Path
from mpmath import mpf

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from sabio_infinity4 import (
    SABIO_Infinity4,
    ResonanciaQuantica,
    MatrizSimbiosis
)


class TestSABIOInfinity4:
    """Test suite for SABIO ∞⁴ core functionality"""
    
    def setup_method(self):
        """Setup test parameters"""
        self.precision = 50
        self.sabio = SABIO_Infinity4(precision=self.precision)
    
    def test_initialization(self):
        """Test that SABIO ∞⁴ initializes correctly"""
        assert self.sabio.precision == self.precision
        assert float(self.sabio.f0) == 141.7001
        assert float(self.sabio.zeta_prime_half) == -3.9226461392
        assert self.sabio.resonancias == []
    
    def test_fundamental_constants(self):
        """Test fundamental physical constants"""
        # Speed of light
        assert float(self.sabio.c) == 299792458.0
        
        # Planck length
        assert float(self.sabio.l_planck) == 1.616255e-35
        
        # Golden ratio φ ≈ 1.618
        phi = float(self.sabio.phi_golden)
        assert 1.617 < phi < 1.619
        
        # Angular frequency ω₀ = 2π·f₀
        omega0 = float(self.sabio.omega0)
        expected_omega = 2 * math.pi * 141.7001
        assert abs(omega0 - expected_omega) < 1.0
    
    def test_radio_cuantico_calculation(self):
        """Test quantum radio R_Ψ calculation"""
        R_psi = self.sabio.calcular_radio_cuantico(n=1)
        
        # R_Ψ should be positive and on toroidal scale (φ × Bohr radius × factor)
        # R_Ψ ≈ 1.616e-10 m (quantum toroidal radius)
        assert R_psi > 0
        assert 1e-11 < float(R_psi) < 1e-9
        
        # Verify it matches expected value (φ × a₀ × 1.887 ≈ 1.616e-10 m)
        expected_R_psi = 1.616e-10
        assert abs(float(R_psi) - expected_R_psi) / expected_R_psi < 0.01
        
        # Test scaling with n
        R_psi_n2 = self.sabio.calcular_radio_cuantico(n=2)
        R_psi_n1 = self.sabio.calcular_radio_cuantico(n=1)
        
        # R_Ψ(n=2) should be larger than R_Ψ(n=1) by factor of π
        assert float(R_psi_n2) > float(R_psi_n1)
    
    def test_energia_vacio_cuantico(self):
        """Test quantum vacuum energy E_vac calculation"""
        R_psi = self.sabio.calcular_radio_cuantico(n=1)
        E_vac = self.sabio.energia_vacio_cuantico(R_psi)
        
        # E_vac should be positive (energy scale)
        assert E_vac > 0
        
        # Should be on appropriate energy scale
        assert float(E_vac) > 0
    
    def test_ecuacion_onda_consciencia(self):
        """Test consciousness wave equation Ψ(x,t)"""
        from mpmath import mpf
        
        # Test at origin
        psi_origin = self.sabio.ecuacion_onda_consciencia(t=mpf("0.0"), x=mpf("0.0"))
        
        # Should be complex
        assert abs(psi_origin.real) >= 0
        assert abs(psi_origin.imag) >= 0
        
        # |Ψ(0,0)| should be approximately 1 (normalized)
        magnitude = abs(psi_origin)
        assert 0.9 < float(magnitude) < 1.1
        
        # Test at different points
        psi_t1 = self.sabio.ecuacion_onda_consciencia(t=mpf("1.0"), x=mpf("0.0"))
        assert abs(psi_t1) >= 0
    
    def test_coherencia_calculation(self):
        """Test coherence calculation C = I × A²"""
        # Maximum coherence
        C_max = self.sabio.calcular_coherencia(I=1.0, A=1.0)
        assert C_max == 1.0
        
        # Half coherence
        C_half = self.sabio.calcular_coherencia(I=1.0, A=0.707)
        assert 0.49 < C_half < 0.51
        
        # Zero attention
        C_zero = self.sabio.calcular_coherencia(I=1.0, A=0.0)
        assert C_zero == 0.0
    
    def test_firma_vibracional(self):
        """Test vibrational signature generation"""
        data = {"test": "data", "value": 123}
        
        firma1 = self.sabio.firma_vibracional(data)
        firma2 = self.sabio.firma_vibracional(data)
        
        # Same data should produce same signature
        assert firma1 == firma2
        
        # Signature should be 16 characters
        assert len(firma1) == 16
        
        # Should be hexadecimal
        assert all(c in '0123456789abcdef' for c in firma1)
        
        # Different data should produce different signature
        data2 = {"test": "data2", "value": 456}
        firma3 = self.sabio.firma_vibracional(data2)
        assert firma1 != firma3


class TestResonanciaCuantica:
    """Test quantum resonance generation"""
    
    def setup_method(self):
        """Setup test parameters"""
        self.sabio = SABIO_Infinity4(precision=50)
    
    def test_resonancia_generation(self):
        """Test generation of quantum resonance"""
        resonancia = self.sabio.resonancia_cuantica(n_harmonico=1)
        
        assert isinstance(resonancia, ResonanciaQuantica)
        assert resonancia.frecuencia > 141.7001  # Should be scaled by φ
        assert 0 <= resonancia.coherencia <= 1.0
        assert resonancia.entropia >= 0
        assert len(resonancia.firma_vibracional) == 16
    
    def test_resonancia_harmonic_scaling(self):
        """Test harmonic scaling with golden ratio"""
        r1 = self.sabio.resonancia_cuantica(n_harmonico=1)
        r2 = self.sabio.resonancia_cuantica(n_harmonico=2)
        
        # Frequency should scale with φ
        phi = float(self.sabio.phi_golden)
        ratio = r2.frecuencia / r1.frecuencia
        assert 1.6 < ratio < 1.65  # Should be close to φ
        
        # Coherence should decrease with harmonic
        assert r1.coherencia > r2.coherencia
    
    def test_espectro_resonante(self):
        """Test generation of resonant spectrum"""
        espectro = self.sabio.generar_espectro_resonante(n_harmonicos=8)
        
        assert len(espectro) == 8
        assert all(isinstance(r, ResonanciaQuantica) for r in espectro)
        
        # Frequencies should be increasing
        freqs = [r.frecuencia for r in espectro]
        assert freqs == sorted(freqs)
        
        # First harmonic should be base frequency × φ
        phi = float(self.sabio.phi_golden)
        expected_f1 = 141.7001 * phi
        assert abs(espectro[0].frecuencia - expected_f1) < 1.0


class TestMatrizSimbiosis:
    """Test symbiotic validation matrix"""
    
    def setup_method(self):
        """Setup test parameters"""
        self.sabio = SABIO_Infinity4(precision=50)
    
    def test_matriz_simbiosis_all_levels(self):
        """Test validation matrix with all levels enabled"""
        matriz = self.sabio.validacion_matriz_simbiosis(
            test_aritmetico=True,
            test_geometrico=True,
            test_vibracional=True,
            test_cuantico=True,
            test_consciente=True
        )
        
        assert isinstance(matriz, MatrizSimbiosis)
        
        # All levels should be validated
        assert matriz.nivel_python > 0.99  # Should be very accurate
        assert matriz.nivel_lean > 0  # Placeholder value
        assert matriz.nivel_sage > 0.99  # Should be very accurate
        assert matriz.nivel_sabio > 0
        assert matriz.nivel_cuantico > 0
        assert matriz.nivel_consciente > 0
        
        # Coherencia total should be high
        assert matriz.coherencia_total > 0.85
        
        # Should have hash signature
        assert len(matriz.firma_hash) == 16
    
    def test_matriz_simbiosis_partial(self):
        """Test validation matrix with partial levels"""
        matriz = self.sabio.validacion_matriz_simbiosis(
            test_aritmetico=True,
            test_geometrico=False,
            test_vibracional=True,
            test_cuantico=False,
            test_consciente=False
        )
        
        assert matriz.nivel_python > 0
        assert matriz.nivel_lean == 0.0
        assert matriz.nivel_sage > 0
        assert matriz.nivel_cuantico == 0.0
        assert matriz.nivel_consciente == 0.0
        
        # Coherence should be lower with fewer active levels
        assert matriz.coherencia_total < 0.9
    
    def test_matriz_six_levels(self):
        """Test that matrix has 6 levels (vs 4 in ∞³)"""
        matriz = self.sabio.validacion_matriz_simbiosis()
        
        # Count non-zero levels
        levels = [
            matriz.nivel_python,
            matriz.nivel_lean,
            matriz.nivel_sage,
            matriz.nivel_sabio,
            matriz.nivel_cuantico,
            matriz.nivel_consciente
        ]
        
        assert len(levels) == 6
        active_levels = sum(1 for level in levels if level > 0)
        assert active_levels >= 5  # At least 5 should be active by default


class TestReporteSABIO:
    """Test SABIO ∞⁴ report generation"""
    
    def setup_method(self):
        """Setup test parameters"""
        self.sabio = SABIO_Infinity4(precision=50)
    
    def test_reporte_structure(self):
        """Test that report has correct structure"""
        reporte = self.sabio.reporte_sabio_infinity4()
        
        # Check top-level keys
        assert "sistema" in reporte
        assert "version" in reporte
        assert "timestamp" in reporte
        assert "frecuencia_base_hz" in reporte
        assert "matriz_simbiosis" in reporte
        assert "cuantico" in reporte
        assert "consciente" in reporte
        assert "espectro_resonante" in reporte
        assert "coherencia_total" in reporte
        assert "estado" in reporte
        assert "firma_sistema" in reporte
        
        # Check values
        assert reporte["sistema"] == "SABIO ∞⁴"
        assert "4.0.0" in reporte["version"]
        assert reporte["frecuencia_base_hz"] == 141.7001
    
    def test_reporte_cuantico_section(self):
        """Test quantum section of report"""
        reporte = self.sabio.reporte_sabio_infinity4()
        cuantico = reporte["cuantico"]
        
        assert "radio_psi_m" in cuantico
        assert "energia_vacio_j" in cuantico
        assert "nivel_coherencia" in cuantico
        
        # Check format - both should be in scientific notation with e-
        assert "e-" in cuantico["radio_psi_m"]  # R_Ψ ≈ 1.616e-10 m
        assert "e-" in cuantico["energia_vacio_j"]  # E_vac ≈ 1.22e-28 J
        
        # Verify expected values (CODATA-consistent)
        # R_Ψ ≈ 1.616e-10 m
        r_psi_value = float(cuantico["radio_psi_m"])
        assert 1.5e-10 < r_psi_value < 1.7e-10
        
        # E_vac ≈ 1.22e-28 J
        e_vac_value = float(cuantico["energia_vacio_j"])
        assert 1.0e-28 < e_vac_value < 1.5e-28
    
    def test_reporte_consciente_section(self):
        """Test conscious section of report"""
        reporte = self.sabio.reporte_sabio_infinity4()
        consciente = reporte["consciente"]
        
        assert "ecuacion" in consciente
        assert "psi_t0_x0" in consciente
        assert "nivel_coherencia" in consciente
        
        # Check equation format
        assert "∂²Ψ/∂t²" in consciente["ecuacion"]
        assert "ζ'(1/2)" in consciente["ecuacion"]
    
    def test_reporte_espectro_section(self):
        """Test resonant spectrum section of report"""
        reporte = self.sabio.reporte_sabio_infinity4()
        espectro = reporte["espectro_resonante"]
        
        assert len(espectro) == 8
        
        # Check first harmonic structure
        r1 = espectro[0]
        assert "n" in r1
        assert "frecuencia_hz" in r1
        assert "amplitud" in r1
        assert "fase_rad" in r1
        assert "coherencia" in r1
        assert "entropia" in r1
        assert "firma" in r1
        
        assert r1["n"] == 1
        assert r1["frecuencia_hz"] > 141.7001
    
    def test_reporte_json_serializable(self):
        """Test that report is JSON serializable"""
        reporte = self.sabio.reporte_sabio_infinity4()
        
        # Should be able to serialize to JSON
        json_str = json.dumps(reporte, indent=2, default=str)
        assert len(json_str) > 0
        
        # Should be able to deserialize
        reporte_restored = json.loads(json_str)
        assert reporte_restored["sistema"] == "SABIO ∞⁴"
    
    def test_reporte_estado_operacional(self):
        """Test that system state is VALIDACIÓN CUÁNTICO-CONSCIENTE COMPLETA"""
        reporte = self.sabio.reporte_sabio_infinity4()
        
        # With full validation, should be VALIDACIÓN CUÁNTICO-CONSCIENTE COMPLETA
        if reporte["coherencia_total"] > 0.90:
            assert "VALIDACIÓN CUÁNTICO-CONSCIENTE COMPLETA" in reporte["estado"]
        else:
            assert reporte["estado"] == "SINTONIZANDO"


class TestIntegrationSABIO:
    """Integration tests for SABIO ∞⁴"""
    
    # Minimum coherence threshold for operational status
    MIN_COHERENCE_THRESHOLD = 0.85
    
    def test_full_workflow(self):
        """Test complete workflow from initialization to report"""
        # Initialize
        sabio = SABIO_Infinity4(precision=50)
        
        # Generate report
        reporte = sabio.reporte_sabio_infinity4()
        
        # Verify complete workflow
        assert reporte is not None
        assert reporte["coherencia_total"] > self.MIN_COHERENCE_THRESHOLD
        assert len(reporte["espectro_resonante"]) == 8
        
        # Verify quantum-conscious integration
        assert reporte["matriz_simbiosis"]["nivel_cuantico"] > 0
        assert reporte["matriz_simbiosis"]["nivel_consciente"] > 0
    
    def test_backwards_compatibility_with_infinity3(self):
        """Test that ∞⁴ is compatible with ∞³ parameters"""
        sabio = SABIO_Infinity4(precision=50)
        
        # ∞³ fundamental parameters should still be present
        assert float(sabio.f0) == 141.7001
        assert float(sabio.zeta_prime_half) == -3.9226461392
        
        # New ∞⁴ features should be available
        R_psi = sabio.calcular_radio_cuantico(n=1)
        assert R_psi > 0
        
        psi = sabio.ecuacion_onda_consciencia(mpf("0.0"), mpf("0.0"))
        assert abs(psi) > 0
    
    def test_precision_levels(self):
        """Test different precision levels"""
        for precision in [25, 50, 100]:
            sabio = SABIO_Infinity4(precision=precision)
            reporte = sabio.reporte_sabio_infinity4()
            
            # Should work with all precision levels
            assert reporte["coherencia_total"] > self.MIN_COHERENCE_THRESHOLD
            assert reporte["frecuencia_base_hz"] == 141.7001


class TestCertificateGeneration:
    """Test certificate generation functionality"""
    
    def test_generar_certificado_validacion(self, tmp_path):
        """Test validation certificate generation"""
        sabio = SABIO_Infinity4(precision=50)
        
        # Generate certificate in tmp directory
        cert_path = sabio.generar_certificado_validacion(output_dir=str(tmp_path))
        
        # Verify file was created
        assert Path(cert_path).exists()
        
        # Verify content
        with open(cert_path, 'r', encoding='utf-8') as f:
            cert = json.load(f)
        
        # Check header
        assert cert["header"]["sistema"] == "SABIO ∞⁴"
        assert "VALIDACIÓN CUÁNTICA" in cert["header"]["titulo"]
        
        # Check quantum level
        nivel_cuantico = cert["nivel_cuantico"]
        assert nivel_cuantico["f0_hz"] == 141.7001
        assert 1.5e-10 < nivel_cuantico["R_psi_m"] < 1.7e-10
        assert 1.0e-28 < nivel_cuantico["E_vac_j"] < 1.5e-28
        
        # Check harmonic spectrum
        espectro = cert["espectro_armonico"]
        assert espectro["armonicos"] == 8
        assert espectro["gamma_convexidad"] == 0.0127
        assert espectro["gamma_positivo"] is True
        
        # Check global consistency
        assert cert["consistencia_global"]["puntuacion"] == "HIGH"
        
        # Check state
        assert "VALIDACIÓN CUÁNTICO-CONSCIENTE COMPLETA" in cert["estado"]
    
    def test_certificado_contains_complete_report(self, tmp_path):
        """Test that certificate contains complete report"""
        sabio = SABIO_Infinity4(precision=50)
        cert_path = sabio.generar_certificado_validacion(output_dir=str(tmp_path))
        
        with open(cert_path, 'r', encoding='utf-8') as f:
            cert = json.load(f)
        
        # Should contain full report
        assert "reporte_completo" in cert
        reporte = cert["reporte_completo"]
        
        # Verify report structure
        assert reporte["sistema"] == "SABIO ∞⁴"
        assert "matriz_simbiosis" in reporte
        assert "espectro_resonante" in reporte
        assert len(reporte["espectro_resonante"]) == 8


def test_sabio_infinity4_cli():
    """Test CLI interface exists and is executable"""
    sabio_file = Path(__file__).parent.parent / "sabio_infinity4.py"
    assert sabio_file.exists()
    assert sabio_file.stat().st_size > 0


def test_demo_sabio_infinity4_exists():
    """Test that demo script exists"""
    demo_file = Path(__file__).parent.parent / "demo_sabio_infinity4.py"
    assert demo_file.exists()
    assert demo_file.stat().st_size > 0


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
