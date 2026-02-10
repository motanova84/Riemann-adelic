#!/usr/bin/env python3
"""
═══════════════════════════════════════════════════════════════════════════════
QCAL ∞³ AUTHORSHIP CERTIFICATION VALIDATOR
Validación del Sistema de Certificación de Autoría
═══════════════════════════════════════════════════════════════════════════════

Valida que todos los componentes del sistema de certificación de autoría
estén presentes, sean coherentes y mantengan la integridad temporal.

Author: José Manuel Mota Burruezo (JMMB Ψ✧)
License: Sovereign Noetic License 1.0
"""

import json
import hashlib
import sys
from pathlib import Path
from datetime import datetime

# Unique identifiers QCAL
SPECTRAL_FREQUENCY = 141.7001  # Hz
COHERENCE_CONSTANT = 244.36
UNIVERSAL_CONSTANT = 629.83
DELTA_ZETA = 0.2787437
NOETIC_SEAL = "∴𓂀Ω∞³"
PI_CODE = "πCODE-888-QCAL2"
FUNDAMENTAL_EQUATION = "Ψ = I × A_eff² × C^∞"


def print_section(title):
    """Print a section header."""
    print("\n" + "═" * 79)
    print(f"  {title}")
    print("═" * 79)


def validate_declaration_file():
    """Validate the temporal authorship declaration exists."""
    print_section("1. VALIDACIÓN: Declaración de Usurpación Algorítmica")
    
    decl_file = Path("DECLARACION_USURPACION_ALGORITMICA_QCAL.md")
    if not decl_file.exists():
        print("❌ ERROR: DECLARACION_USURPACION_ALGORITMICA_QCAL.md no encontrado")
        return False
    
    content = decl_file.read_text()
    
    checks = {
        "Contiene título": "DECLARACIÓN DE USURPACIÓN ALGORÍTMICA" in content,
        "Menciona autor": "José Manuel Mota Burruezo" in content,
        "Incluye ORCID": "0009-0002-1923-0773" in content,
        "Incluye DOI": "10.5281/zenodo.17379721" in content,
        "Menciona f₀": "141.7001" in content,
        "Menciona C": "244.36" in content,
        "Incluye sello noético": "∴𓂀Ω∞³" in content or "noetic" in content.lower(),
        "Documenta timeline": "temporal" in content.lower() or "timeline" in content.lower(),
    }
    
    all_passed = True
    for check_name, passed in checks.items():
        status = "✅" if passed else "❌"
        print(f"   {status} {check_name}")
        if not passed:
            all_passed = False
    
    if all_passed:
        print(f"\n   📄 Tamaño: {len(content)} caracteres")
    
    return all_passed


def validate_repository_hash():
    """Validate repository hash certificate."""
    print_section("2. VALIDACIÓN: Certificado de Hash del Repositorio")
    
    hash_file = Path(".qcal_repository_hash")
    if not hash_file.exists():
        print("❌ ERROR: .qcal_repository_hash no encontrado")
        return False
    
    content = hash_file.read_text()
    
    checks = {
        "Contiene hash SHA-256": "repository_hash_sha256" in content,
        "Hash de 64 caracteres": any(len(line.strip().split('"')[1]) == 64 
                                      for line in content.split('\n') 
                                      if "repository_hash_sha256" in line),
        "Incluye timestamp": "hash_generation_date" in content,
        "Menciona f₀": "141.7001" in content,
        "Incluye sello noético": NOETIC_SEAL in content,
        "Incluye πCODE": PI_CODE in content,
        "Referencias DOIs": "zenodo" in content.lower(),
    }
    
    all_passed = True
    for check_name, passed in checks.items():
        status = "✅" if passed else "❌"
        print(f"   {status} {check_name}")
        if not passed:
            all_passed = False
    
    # Extract hash
    for line in content.split('\n'):
        if "repository_hash_sha256" in line and '"' in line:
            try:
                hash_value = line.split('"')[1]
                print(f"\n   🔐 Hash: {hash_value[:16]}...{hash_value[-16:]}")
                break
            except:
                pass
    
    return all_passed


def validate_authorship_contract():
    """Validate authorship contract JSON."""
    print_section("3. VALIDACIÓN: Contrato de Autoría JSON")
    
    contract_file = Path("contracts/qcal_authorship_contract.json")
    if not contract_file.exists():
        print("❌ ERROR: contracts/qcal_authorship_contract.json no encontrado")
        return False
    
    try:
        with open(contract_file) as f:
            contract = json.load(f)
    except json.JSONDecodeError as e:
        print(f"❌ ERROR: JSON inválido: {e}")
        return False
    
    checks = {
        "Tipo de contrato": contract.get("contract_type") == "QCAL_Authorship_Certification",
        "Identificador único": contract.get("unique_identifier") == PI_CODE,
        "Sello noético": contract.get("noetic_seal") == NOETIC_SEAL,
        "Autor presente": "José Manuel Mota Burruezo" in json.dumps(contract),
        "Frecuencia espectral": contract.get("spectral_signature", {}).get("base_frequency", {}).get("value") == SPECTRAL_FREQUENCY,
        "Coherencia": contract.get("spectral_signature", {}).get("coherence_constant", {}).get("primary_value") == COHERENCE_CONSTANT,
        "DOIs Zenodo": "zenodo_dois" in contract,
        "Blockchain": "blockchain_integration" in contract,
        "Validación": "validation_system" in contract,
    }
    
    all_passed = True
    for check_name, passed in checks.items():
        status = "✅" if passed else "❌"
        print(f"   {status} {check_name}")
        if not passed:
            all_passed = False
    
    if all_passed:
        print(f"\n   📋 Versión: {contract.get('contract_version', 'N/A')}")
        print(f"   📅 Timestamp: {contract.get('certification', {}).get('timestamp', 'N/A')}")
    
    return all_passed


def validate_qcal_beacon_authorship():
    """Validate authorship fields in .qcal_beacon."""
    print_section("4. VALIDACIÓN: Campos de Autoría en .qcal_beacon")
    
    beacon_file = Path(".qcal_beacon")
    if not beacon_file.exists():
        print("❌ ERROR: .qcal_beacon no encontrado")
        return False
    
    content = beacon_file.read_text()
    
    checks = {
        "authorship_certification_status": "authorship_certification_status" in content,
        "authorship_unique_identifier": PI_CODE in content,
        "authorship_noetic_seal": NOETIC_SEAL in content,
        "authorship_contract": "authorship_contract" in content,
        "authorship_declaration": "authorship_declaration" in content,
        "authorship_repository_hash": "authorship_repository_hash" in content,
        "ai_training_timeline": "ai_training" in content,
        "pattern_spectral_frequency": "pattern_spectral_frequency" in content,
        "pattern_fundamental_equation": "pattern_fundamental_equation" in content,
        "DOIs Zenodo": "authorship_doi" in content,
    }
    
    all_passed = True
    for check_name, passed in checks.items():
        status = "✅" if passed else "❌"
        print(f"   {status} {check_name}")
        if not passed:
            all_passed = False
    
    return all_passed


def validate_unique_identifiers():
    """Validate all unique QCAL identifiers are present."""
    print_section("5. VALIDACIÓN: Identificadores Únicos QCAL")
    
    all_files_content = ""
    for ext in [".md", ".json", ".py", ".qcal_beacon", ".qcal_repository_hash"]:
        for file in Path(".").rglob(f"*{ext}"):
            if ".git" not in str(file) and "node_modules" not in str(file):
                try:
                    all_files_content += file.read_text()
                except:
                    pass
    
    identifiers = {
        "Frecuencia f₀": ("141.7001", "Hz espectral única"),
        "Coherencia C": ("244.36", "Constante de coherencia"),
        "Ecuación Ψ": ("Ψ = I × A_eff² × C^∞", "Ecuación fundamental"),
        "Sello Noético": (NOETIC_SEAL, "Firma irrepetible"),
        "πCODE": (PI_CODE, "Identificador de contratos"),
        "δζ": ("0.2787437", "Curvatura vibracional"),
    }
    
    all_passed = True
    for name, (value, description) in identifiers.items():
        present = value in all_files_content
        status = "✅" if present else "❌"
        print(f"   {status} {name}: {value}")
        print(f"       {description}")
        if not present:
            all_passed = False
    
    return all_passed


def validate_doi_references():
    """Validate Zenodo DOI references."""
    print_section("6. VALIDACIÓN: Referencias DOI Zenodo")
    
    contract_file = Path("contracts/qcal_authorship_contract.json")
    beacon_file = Path(".qcal_beacon")
    
    if not contract_file.exists() or not beacon_file.exists():
        print("❌ ERROR: Archivos necesarios no encontrados")
        return False
    
    with open(contract_file) as f:
        contract = json.load(f)
    
    dois = contract.get("zenodo_dois", {})
    
    expected_dois = {
        "primary": "10.5281/zenodo.17379721",
        "related": {
            "infinito": "10.5281/zenodo.17362686",
            "pnp": "10.5281/zenodo.17315719",
            "goldbach": "10.5281/zenodo.17297591",
        }
    }
    
    checks = {
        "DOI Principal": dois.get("primary") == expected_dois["primary"],
        "DOI Infinito": dois.get("related", {}).get("infinito") == expected_dois["related"]["infinito"],
        "DOI P-NP": dois.get("related", {}).get("pnp") == expected_dois["related"]["pnp"],
        "DOI Goldbach": dois.get("related", {}).get("goldbach") == expected_dois["related"]["goldbach"],
    }
    
    all_passed = True
    for check_name, passed in checks.items():
        status = "✅" if passed else "❌"
        print(f"   {status} {check_name}")
        if not passed:
            all_passed = False
    
    if all_passed:
        print(f"\n   🌐 Total DOIs: {len(dois.get('related', {})) + 1}")
    
    return all_passed


def main():
    """Run all validations."""
    print("\n" + "═" * 79)
    print("  🛡️ QCAL ∞³ AUTHORSHIP CERTIFICATION VALIDATOR")
    print("  José Manuel Mota Burruezo (JMMB Ψ✧)")
    print("  Instituto de Conciencia Cuántica (ICQ)")
    print("═" * 79)
    
    results = {
        "Declaración de Usurpación": validate_declaration_file(),
        "Certificado de Hash": validate_repository_hash(),
        "Contrato de Autoría": validate_authorship_contract(),
        "Beacon Authorship": validate_qcal_beacon_authorship(),
        "Identificadores Únicos": validate_unique_identifiers(),
        "Referencias DOI": validate_doi_references(),
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
        print("  Sistema de Certificación de Autoría QCAL ∞³: OPERATIVO")
        print("  Frecuencia Base: 141.7001 Hz")
        print("  Coherencia: C = 244.36")
        print("  Identificador Único: πCODE-888-QCAL2")
        print("  Sello Noético: ∴𓂀Ω∞³")
        print()
        print("  ∴𓂀Ω∞³ — Certificación de Autoría Verificada — ∴")
    else:
        print("  ❌  ALGUNAS VALIDACIONES FALLARON")
        print("  Revisar los errores arriba para más detalles.")
    print("═" * 79 + "\n")
    
    return 0 if all_passed else 1


if __name__ == "__main__":
    sys.exit(main())
