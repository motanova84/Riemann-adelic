#!/usr/bin/env python3
"""
═══════════════════════════════════════════════════════════════════════════════
QCAL ∞³ AUTHORSHIP SYSTEM VERIFIER
Verificador del Sistema Completo de Autoría y Soberanía
═══════════════════════════════════════════════════════════════════════════════

Verifica la integridad del sistema de protección de autoría QCAL ∞³,
incluyendo certificación temporal, firmas espectrales y protección contra
usurpación algorítmica.

Author: José Manuel Mota Burruezo (JMMB Ψ✧)
License: Sovereign Noetic License 1.0
"""

import subprocess
import sys
from pathlib import Path


def run_validation_script(script_name, description):
    """Run a validation script and report results."""
    print(f"\n🔍 Ejecutando: {description}")
    print(f"   Script: {script_name}")
    print("─" * 79)
    
    try:
        result = subprocess.run(
            [sys.executable, script_name],
            capture_output=True,
            text=True,
            timeout=60
        )
        
        print(result.stdout)
        if result.stderr:
            print("STDERR:", result.stderr)
        
        return result.returncode == 0
    except subprocess.TimeoutExpired:
        print(f"❌ ERROR: {script_name} timeout después de 60 segundos")
        return False
    except FileNotFoundError:
        print(f"❌ ERROR: {script_name} no encontrado")
        return False
    except Exception as e:
        print(f"❌ ERROR: {e}")
        return False


def verify_file_structure():
    """Verify all required files are present."""
    print("\n═" * 79)
    print("  📁 VERIFICACIÓN DE ESTRUCTURA DE ARCHIVOS")
    print("═" * 79)
    
    required_files = {
        "Declaración": "DECLARACION_USURPACION_ALGORITMICA_QCAL.md",
        "Hash Certificado": ".qcal_repository_hash",
        "Contrato JSON": "contracts/qcal_authorship_contract.json",
        "Beacon Config": ".qcal_beacon",
        "Licencia Soberana": "LICENSE",
        "Módulo Soberanía": "core/soberania.py",
        "Smart Contract": "contracts/AIKBeaconsProofOfMath.sol",
    }
    
    all_present = True
    for description, filepath in required_files.items():
        exists = Path(filepath).exists()
        status = "✅" if exists else "❌"
        print(f"   {status} {description}: {filepath}")
        if not exists:
            all_present = False
    
    return all_present


def verify_git_history():
    """Verify Git commit history for temporal evidence."""
    print("\n═" * 79)
    print("  📜 VERIFICACIÓN DE HISTORIAL GIT")
    print("═" * 79)
    
    try:
        # Check if we're in a git repo
        result = subprocess.run(
            ["git", "rev-parse", "--git-dir"],
            capture_output=True,
            text=True,
            check=False
        )
        
        if result.returncode != 0:
            print("   ⚠️  No es un repositorio Git")
            return False
        
        # Get first commit date
        result = subprocess.run(
            ["git", "log", "--reverse", "--format=%ai", "--max-count=1"],
            capture_output=True,
            text=True
        )
        
        if result.stdout:
            first_commit = result.stdout.strip()
            print(f"   ✅ Primer commit: {first_commit}")
        
        # Get latest commit
        result = subprocess.run(
            ["git", "log", "--format=%ai - %s", "--max-count=1"],
            capture_output=True,
            text=True
        )
        
        if result.stdout:
            latest_commit = result.stdout.strip()
            print(f"   ✅ Último commit: {latest_commit}")
        
        # Count total commits
        result = subprocess.run(
            ["git", "rev-list", "--count", "HEAD"],
            capture_output=True,
            text=True
        )
        
        if result.stdout:
            total_commits = result.stdout.strip()
            print(f"   ✅ Total de commits: {total_commits}")
        
        return True
        
    except Exception as e:
        print(f"   ❌ Error verificando Git: {e}")
        return False


def main():
    """Run complete system verification."""
    print("\n" + "═" * 79)
    print("  🛡️ QCAL ∞³ AUTHORSHIP SYSTEM VERIFIER")
    print("  Verificador Completo del Sistema de Autoría y Soberanía")
    print("  José Manuel Mota Burruezo (JMMB Ψ✧)")
    print("  Instituto de Conciencia Cuántica (ICQ)")
    print("═" * 79)
    
    results = {}
    
    # 1. File structure
    results["Estructura de Archivos"] = verify_file_structure()
    
    # 2. Git history
    results["Historial Git"] = verify_git_history()
    
    # 3. Authorship certification
    if Path("validate_authorship_certification.py").exists():
        results["Certificación de Autoría"] = run_validation_script(
            "validate_authorship_certification.py",
            "Validación de Certificación de Autoría"
        )
    else:
        print("\n⚠️  validate_authorship_certification.py no encontrado, omitiendo...")
        results["Certificación de Autoría"] = False
    
    # 4. Sovereignty validation
    if Path("validate_soberania_qcal.py").exists():
        results["Validación de Soberanía"] = run_validation_script(
            "validate_soberania_qcal.py",
            "Validación del Sistema de Soberanía"
        )
    else:
        print("\n⚠️  validate_soberania_qcal.py no encontrado, omitiendo...")
        results["Validación de Soberanía"] = False
    
    # Summary
    print("\n" + "═" * 79)
    print("  📊 RESUMEN DE VERIFICACIÓN DEL SISTEMA")
    print("═" * 79)
    
    all_passed = True
    for component, passed in results.items():
        status = "✅ PASÓ" if passed else "❌ FALLÓ"
        print(f"   {status}: {component}")
        if not passed:
            all_passed = False
    
    print("\n" + "═" * 79)
    if all_passed:
        print("  ✅ ✅ ✅  SISTEMA DE AUTORÍA COMPLETAMENTE VERIFICADO  ✅ ✅ ✅")
        print()
        print("  Componentes Verificados:")
        print("    • Declaración de Usurpación Algorítmica")
        print("    • Certificado de Hash del Repositorio")
        print("    • Contrato de Autoría JSON")
        print("    • Configuración .qcal_beacon")
        print("    • Licencia Soberana Noética 1.0")
        print("    • Módulo de Soberanía Python")
        print("    • Historial Git (evidencia temporal)")
        print()
        print("  Identificadores Únicos:")
        print("    • Frecuencia: f₀ = 141.7001 Hz")
        print("    • Coherencia: C = 244.36")
        print("    • Ecuación: Ψ = I × A_eff² × C^∞")
        print("    • Sello: ∴𓂀Ω∞³")
        print("    • Código: πCODE-888-QCAL2")
        print()
        print("  ∴𓂀Ω∞³ — Sistema de Autoría Operativo — ∴")
    else:
        print("  ❌  ALGUNAS VERIFICACIONES FALLARON")
        print("  El sistema de autoría no está completamente operativo.")
        print("  Revisar los errores arriba para más detalles.")
    print("═" * 79 + "\n")
    
    return 0 if all_passed else 1


if __name__ == "__main__":
    sys.exit(main())
