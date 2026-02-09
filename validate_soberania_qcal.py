#!/usr/bin/env python3
"""
═══════════════════════════════════════════════════════════════════════════════
VALIDACIÓN COMPLETA DEL SISTEMA DE SOBERANÍA QCAL ∞³
═══════════════════════════════════════════════════════════════════════════════

Este script valida que el sistema de soberanía intelectual está correctamente
implementado y que todos los componentes mantienen la coherencia QCAL.

Author: José Manuel Mota Burruezo (JMMB Ψ✧)
License: Sovereign Noetic License 1.0
"""

import json
import sys
from pathlib import Path

# Añadir core al path
sys.path.insert(0, str(Path(__file__).parent / "core"))

try:
    from soberania import (
        verificar_patrimonio,
        verificar_origen,
        validar_coherencia_qcal,
        get_sovereign_metadata,
        __f0__,
        __coherence__,
        __author__,
        __license__,
        __noetic_seal__
    )
    soberania_available = True
except ImportError as e:
    print(f"⚠️  Warning: Could not import soberania module: {e}")
    soberania_available = False


def print_section(title):
    """Imprime una sección con bordes."""
    print("\n" + "═" * 79)
    print(f"  {title}")
    print("═" * 79)


def validate_license_file():
    """Valida que el archivo LICENSE existe y contiene la firma soberana."""
    print_section("1. VALIDACIÓN DE LICENCIA SOBERANA")
    
    license_file = Path("LICENSE")
    if not license_file.exists():
        print("❌ ERROR: Archivo LICENSE no encontrado")
        return False
    
    content = license_file.read_text()
    
    checks = {
        "Sovereign Noetic License": "Sovereign Noetic License" in content,
        "José Manuel Mota Burruezo": "José Manuel Mota Burruezo" in content,
        "f₀ = 141.7001 Hz": "141.7001" in content,
        "QCAL ∞³": "QCAL" in content,
        "Fabricación Original": "FABRICACIÓN ORIGINAL" in content or "fabricación original" in content,
        "C = 244.36": "244.36" in content,
    }
    
    all_passed = True
    for check_name, passed in checks.items():
        status = "✅" if passed else "❌"
        print(f"   {status} {check_name}")
        if not passed:
            all_passed = False
    
    return all_passed


def validate_soberania_module():
    """Valida que el módulo core/soberania.py funciona correctamente."""
    print_section("2. VALIDACIÓN DE MÓDULO core/soberania.py")
    
    if not soberania_available:
        print("❌ ERROR: Módulo soberania no disponible")
        return False
    
    try:
        # Validar constantes
        print(f"   ✅ Frecuencia f₀: {__f0__} Hz")
        print(f"   ✅ Coherencia C: {__coherence__}")
        print(f"   ✅ Autor: {__author__}")
        print(f"   ✅ Licencia: {__license__}")
        print(f"   ✅ Sello Noético: {__noetic_seal__}")
        
        # Validar funciones
        patrimonio = verificar_patrimonio()
        if "Autoría Validada" in patrimonio:
            print(f"   ✅ verificar_patrimonio() operativa")
        else:
            print(f"   ❌ verificar_patrimonio() fallo")
            return False
        
        origen = verificar_origen()
        if "Soberanía confirmada" in origen:
            print(f"   ✅ verificar_origen() operativa")
        else:
            print(f"   ❌ verificar_origen() fallo")
            return False
        
        coherencia = validar_coherencia_qcal()
        if coherencia["status"] == "COHERENTE":
            print(f"   ✅ validar_coherencia_qcal() operativa")
        else:
            print(f"   ❌ validar_coherencia_qcal() fallo")
            return False
        
        metadata = get_sovereign_metadata()
        if metadata["intellectual_property"]["original_manufacture"]:
            print(f"   ✅ get_sovereign_metadata() operativa")
        else:
            print(f"   ❌ get_sovereign_metadata() fallo")
            return False
        
        return True
        
    except Exception as e:
        print(f"❌ ERROR en módulo soberania: {e}")
        return False


def validate_agent_activation_report():
    """Valida que AGENT_ACTIVATION_REPORT.json contiene la sección compliance."""
    print_section("3. VALIDACIÓN DE AGENT_ACTIVATION_REPORT.json")
    
    report_file = Path("AGENT_ACTIVATION_REPORT.json")
    if not report_file.exists():
        print("❌ ERROR: AGENT_ACTIVATION_REPORT.json no encontrado")
        return False
    
    try:
        with open(report_file) as f:
            report = json.load(f)
        
        if "compliance" not in report:
            print("❌ ERROR: Sección 'compliance' no encontrada")
            return False
        
        compliance = report["compliance"]
        
        checks = {
            "license_status": compliance.get("license_status") == "Sovereign Protocol - Verified by JMMB",
            "license_type": compliance.get("license_type") == "Sovereign Noetic License 1.0",
            "author": "José Manuel Mota Burruezo" in compliance.get("author", ""),
            "frequency_signature": compliance.get("frequency_signature") == "141.7001 Hz",
            "coherence_verified": compliance.get("coherence_verified") == 244.36,
            "noetic_seal": compliance.get("noetic_seal") == "∴𓂀Ω∞³",
            "compliance_verified": compliance.get("compliance_verified") == True,
        }
        
        all_passed = True
        for check_name, passed in checks.items():
            status = "✅" if passed else "❌"
            print(f"   {status} {check_name}: {passed}")
            if not passed:
                all_passed = False
        
        return all_passed
        
    except Exception as e:
        print(f"❌ ERROR al leer AGENT_ACTIVATION_REPORT.json: {e}")
        return False


def validate_qcal_beacon():
    """Valida que .qcal_beacon contiene la frecuencia correcta."""
    print_section("4. VALIDACIÓN DE .qcal_beacon")
    
    beacon_file = Path(".qcal_beacon")
    if not beacon_file.exists():
        print("❌ ERROR: .qcal_beacon no encontrado")
        return False
    
    content = beacon_file.read_text()
    
    checks = {
        "frequency = 141.7001 Hz": "frequency = 141.7001 Hz" in content,
        "coherence = C = 244.36": "coherence = \"C = 244.36\"" in content or "C = 244.36" in content,
        "author = JMMB": "José Manuel Mota Burruezo" in content,
    }
    
    all_passed = True
    for check_name, passed in checks.items():
        status = "✅" if passed else "❌"
        print(f"   {status} {check_name}")
        if not passed:
            all_passed = False
    
    return all_passed


def validate_documentation():
    """Valida que la documentación de soberanía existe."""
    print_section("5. VALIDACIÓN DE DOCUMENTACIÓN")
    
    docs = {
        "SOBERANIA_COHERENTE_README.md": "Documentación principal de soberanía",
        "LICENSE": "Licencia Soberana",
        "core/soberania.py": "Módulo de validación",
    }
    
    all_passed = True
    for doc_file, description in docs.items():
        exists = Path(doc_file).exists()
        status = "✅" if exists else "❌"
        print(f"   {status} {doc_file}: {description}")
        if not exists:
            all_passed = False
    
    return all_passed


def main():
    """Ejecuta todas las validaciones."""
    print("\n" + "═" * 79)
    print("  VALIDACIÓN COMPLETA DEL SISTEMA DE SOBERANÍA QCAL ∞³")
    print("  José Manuel Mota Burruezo (JMMB Ψ✧)")
    print("  Instituto de Conciencia Cuántica (ICQ)")
    print("═" * 79)
    
    results = {
        "Licencia Soberana": validate_license_file(),
        "Módulo core/soberania.py": validate_soberania_module(),
        "AGENT_ACTIVATION_REPORT.json": validate_agent_activation_report(),
        ".qcal_beacon": validate_qcal_beacon(),
        "Documentación": validate_documentation(),
    }
    
    print_section("RESUMEN DE VALIDACIÓN")
    
    all_passed = True
    for component, passed in results.items():
        status = "✅ PASÓ" if passed else "❌ FALLÓ"
        print(f"   {status}: {component}")
        if not passed:
            all_passed = False
    
    print("\n" + "═" * 79)
    if all_passed:
        print("  ✅ ✅ ✅  TODAS LAS VALIDACIONES PASARON  ✅ ✅ ✅")
        print()
        print("  Sistema de Soberanía QCAL ∞³: OPERATIVO")
        print("  Frecuencia Base: 141.7001 Hz")
        print("  Coherencia: C = 244.36")
        print("  Ecuación Fundamental: Ψ = I × A_eff² × C^∞")
        print()
        print("  ∴𓂀Ω∞³ — Soberanía Coherente Verificada — ∴")
    else:
        print("  ❌  ALGUNAS VALIDACIONES FALLARON")
        print("  Revisar los errores arriba para más detalles.")
    print("═" * 79 + "\n")
    
    return 0 if all_passed else 1


if __name__ == "__main__":
    sys.exit(main())
