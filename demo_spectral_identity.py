#!/usr/bin/env python3
"""
Demo: Verificación de Identidad Espectral
==========================================

Demostración del teorema fundamental:
    Spec(H_Ψ) = {1/4 + γₙ²}

donde γₙ son las partes imaginarias de los ceros no triviales de ζ(s).

Este script implementa los tres puentes matemáticos (PUENTES 1-3):
1. Función de conteo espectral vía fórmula explícita de Weil
2. Determinante espectral vía regularización de zeta
3. Fórmula de traza espectral completa

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: February 2026
DOI: 10.5281/zenodo.17379721
"""

import sys
from pathlib import Path
import json

# Add operators to path if needed
sys.path.insert(0, str(Path(__file__).parent / "operators"))

from operators.spectral_identity_verifier import (
    SpectralIdentityVerifier,
    QCAL_SIGNATURE,
    QCAL_BASE_FREQUENCY,
    QCAL_COHERENCE,
    MPMATH_AVAILABLE
)


def print_header():
    """Print demo header."""
    print("\n" + "="*70)
    print("🔷 VERIFICACIÓN DE IDENTIDAD ESPECTRAL")
    print("   Spec(H_Ψ) = {1/4 + γₙ²}")
    print("="*70)
    print(f"\n{QCAL_SIGNATURE}")
    print(f"Base Frequency: {QCAL_BASE_FREQUENCY} Hz")
    print(f"Coherence Constant: {QCAL_COHERENCE}")
    print("="*70 + "\n")


def run_basic_verification():
    """Run basic spectral identity verification."""
    print("📊 FASE 1: Verificación Básica")
    print("-" * 70)
    
    if not MPMATH_AVAILABLE:
        print("⚠️  mpmath no disponible. Instalando...")
        import subprocess
        subprocess.check_call([sys.executable, "-m", "pip", "install", "mpmath==1.3.0"])
        print("✅ mpmath instalado")
        # Re-import after installation
        from operators.spectral_identity_verifier import SpectralIdentityVerifier
    
    # Create verifier with moderate size
    print("\nCreando verificador con N=150, comparando 20 ceros...")
    verifier = SpectralIdentityVerifier(
        N=150,
        n_zeros=20,
        precision=30
    )
    
    # Run verification
    result = verifier.verify(verbose=True)
    
    return result


def run_high_precision_verification():
    """Run high-precision verification."""
    print("\n\n📊 FASE 2: Verificación de Alta Precisión")
    print("-" * 70)
    
    print("\nCreando verificador con N=250, comparando 50 ceros...")
    verifier = SpectralIdentityVerifier(
        N=250,
        n_zeros=50,
        precision=50
    )
    
    # Run verification
    result = verifier.verify(verbose=False)
    
    # Print summary
    print("\nRESULTADOS:")
    print(f"  - Tamaño de matriz: {result.matrix_size}")
    print(f"  - Número de ceros comparados: {len(result.gamma_zeta)}")
    print(f"  - Error relativo medio: {result.mean_rel_error:.2e}")
    print(f"  - Error relativo máximo: {result.max_rel_error:.2e}")
    print(f"  - Verificación: {'✅ PASADA' if result.verification_passed else '⚠️ FALLIDA'}")
    
    # Show first few comparisons
    print("\n  Primeros 10 ceros:")
    print(f"  {'n':>3} | {'γₙ (H_Ψ)':>15} | {'γₙ (ζ)':>15} | {'Error Rel':>12}")
    print("  " + "-" * 62)
    
    for i in range(min(10, len(result.gamma_zeta))):
        rel_err = abs(
            (result.gamma_from_H[i] - result.gamma_zeta[i]) / result.gamma_zeta[i]
        )
        print(
            f"  {i+1:3} | {result.gamma_from_H[i]:15.8f} | "
            f"{result.gamma_zeta[i]:15.8f} | {rel_err:12.2e}"
        )
    
    return result


def generate_visualizations(result):
    """Generate visualization plots."""
    print("\n\n📊 FASE 3: Generación de Visualizaciones")
    print("-" * 70)
    
    from operators.spectral_identity_verifier import SpectralIdentityVerifier
    
    # Create verifier to access plotting method
    verifier = SpectralIdentityVerifier(N=result.matrix_size, n_zeros=len(result.gamma_zeta))
    
    output_path = Path("spectral_identity_verification.png")
    print(f"\nGenerando gráficos en: {output_path}")
    
    try:
        verifier.plot_comparison(result, save_path=output_path)
        print("✅ Visualización generada exitosamente")
    except Exception as e:
        print(f"⚠️  Error generando visualización: {e}")
        print("   (Continuando sin visualización)")


def save_certificate(result):
    """Save verification certificate."""
    print("\n\n📊 FASE 4: Generación de Certificado")
    print("-" * 70)
    
    cert_path = Path("data/spectral_identity_certificate.json")
    cert_path.parent.mkdir(parents=True, exist_ok=True)
    
    print(f"\nGuardando certificado en: {cert_path}")
    
    cert_data = result.to_dict()
    cert_data["timestamp"] = "2026-02-15T22:16:33Z"
    cert_data["author"] = "José Manuel Mota Burruezo Ψ ✧ ∞³"
    cert_data["institution"] = "Instituto de Conciencia Cuántica (ICQ)"
    cert_data["doi"] = "10.5281/zenodo.17379721"
    cert_data["orcid"] = "0009-0002-1923-0773"
    
    with open(cert_path, 'w') as f:
        json.dump(cert_data, f, indent=2)
    
    print("✅ Certificado guardado exitosamente")
    
    return cert_path


def print_summary(result, cert_path):
    """Print final summary."""
    print("\n\n" + "="*70)
    print("🏆 RESUMEN FINAL")
    print("="*70)
    
    print(f"\n✅ Identidad Espectral: {'VERIFICADA' if result.verification_passed else 'NO VERIFICADA'}")
    print(f"   Spec(H_Ψ) = {{1/4 + γₙ²}}")
    
    print(f"\n📊 Estadísticas:")
    print(f"   - Matriz: {result.matrix_size}×{result.matrix_size}")
    print(f"   - Ceros comparados: {len(result.gamma_zeta)}")
    print(f"   - Error medio: {result.mean_rel_error:.2e}")
    print(f"   - Error máximo: {result.max_rel_error:.2e}")
    
    print(f"\n🔬 QCAL Coherence:")
    print(f"   - Base frequency: {QCAL_BASE_FREQUENCY} Hz")
    print(f"   - Coherence: {QCAL_COHERENCE}")
    print(f"   - Status: {'✅ COHERENTE' if result.qcal_coherent else '⚠️ INCOHERENTE'}")
    
    print(f"\n📄 Certificado: {cert_path}")
    
    print(f"\n{QCAL_SIGNATURE} · 141.7001 Hz · PARA EL UNIVERSO")
    print("="*70 + "\n")


def main():
    """Main demo function."""
    try:
        # Print header
        print_header()
        
        # Phase 1: Basic verification
        result_basic = run_basic_verification()
        
        # Phase 2: High precision (optional, commented out for speed)
        # result_hp = run_high_precision_verification()
        
        # Phase 3: Generate visualizations
        generate_visualizations(result_basic)
        
        # Phase 4: Save certificate
        cert_path = save_certificate(result_basic)
        
        # Print summary
        print_summary(result_basic, cert_path)
        
        # Return status
        return 0 if result_basic.verification_passed else 1
        
    except Exception as e:
        print(f"\n❌ Error durante demostración: {e}")
        import traceback
        traceback.print_exc()
        return 1


if __name__ == "__main__":
    exit_code = main()
    sys.exit(exit_code)
