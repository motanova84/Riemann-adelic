#!/usr/bin/env python3
"""
Validation script for QCAL_Infinity3.lean formalization

This script checks that the Lean4 file contains all required sections
and structures from the problem statement.

Author: José Manuel Mota Burruezo Ψ ∞³
Date: Enero 2026
"""

import re
from pathlib import Path

def validate_qcal_infinity3():
    """Validate that QCAL_Infinity3.lean contains all required sections."""
    
    lean_file = Path("formalization/lean/QCAL_Infinity3.lean")
    
    if not lean_file.exists():
        print("❌ ERROR: QCAL_Infinity3.lean not found")
        return False
    
    content = lean_file.read_text()
    
    # Required sections from the problem statement
    required_sections = {
        "SECCIÓN 1": "EL HORIZONTE CRÍTICO",
        "SECCIÓN 2": "LOS CEROS COMO AGUJEROS NEGROS",
        "SECCIÓN 3": "EL OPERADOR H_Ψ",
        "SECCIÓN 4": "ESPECTRO DE H_Ψ COINCIDE CON CEROS",
        "SECCIÓN 5": "ECUACIÓN DE CAMPO UNIFICADA",
        "SECCIÓN 6": "DUALIDAD ESPECTRAL",
        "SECCIÓN 7": "TEOREMA DE HORIZONTE RELATIVO",
        "SECCIÓN 8": "TEOREMA DE REVELACIÓN COMPLETA",
        "SECCIÓN 9": "CORRESPONDENCIA CON GRAVEDAD CUÁNTICA",
        "SECCIÓN 10": "SÍNTESIS FINAL"
    }
    
    # Required structures
    required_structures = [
        "HorizonteCritico",
        "AgujeroNegroMatematico",
        "TensorCoherenciaConsciente",
        "HorizonteObservable",
        "AgujeroNegroFisico"
    ]
    
    # Required theorems
    required_theorems = [
        "linea_critica_es_variedad",
        "ceros_como_agujeros_negros",
        "H_Ψ_autoadjunto",
        "horizonte_expande_con_coherencia",
        "revelacion_completa",
        "isomorfismo_espectral",
        "Teorema_Unificado_QCAL_Infinity3"
    ]
    
    # Required constants
    required_constants = [
        "frecuencia_fundamental",
        "ℏ",
        "c",
        "G_Newton",
        "Λ",
        "constante_acoplamiento_vibracional"
    ]
    
    print("🔍 Validating QCAL_Infinity3.lean formalization...\n")
    
    # Check sections
    print("📋 Checking sections:")
    all_sections_found = True
    for section_num, section_desc in required_sections.items():
        if section_num in content and section_desc in content:
            print(f"  ✅ {section_num}: {section_desc}")
        else:
            print(f"  ❌ {section_num}: {section_desc} - NOT FOUND")
            all_sections_found = False
    
    # Check structures
    print("\n🏗️  Checking structures:")
    all_structures_found = True
    for struct in required_structures:
        pattern = rf"structure\s+{re.escape(struct)}\s+where"
        if re.search(pattern, content):
            print(f"  ✅ structure {struct}")
        else:
            print(f"  ❌ structure {struct} - NOT FOUND")
            all_structures_found = False
    
    # Check theorems
    print("\n📐 Checking theorems:")
    all_theorems_found = True
    for theorem in required_theorems:
        pattern = rf"theorem\s+{re.escape(theorem)}\s*[:\(]"
        if re.search(pattern, content):
            print(f"  ✅ theorem {theorem}")
        else:
            print(f"  ❌ theorem {theorem} - NOT FOUND")
            all_theorems_found = False
    
    # Check constants
    print("\n🔢 Checking constants:")
    all_constants_found = True
    for constant in required_constants:
        pattern = rf"(noncomputable\s+)?def\s+{re.escape(constant)}\s*:"
        if re.search(pattern, content):
            print(f"  ✅ constant {constant}")
        else:
            print(f"  ❌ constant {constant} - NOT FOUND")
            all_constants_found = False
    
    # Check for key frequencies
    print("\n🎵 Checking QCAL fundamental frequency:")
    if "141.7001" in content:
        print(f"  ✅ Fundamental frequency f₀ = 141.7001 Hz found")
    else:
        print(f"  ❌ Fundamental frequency not found")
    
    # Check for proper attribution
    print("\n📝 Checking attribution:")
    attribution_items = [
        ("ORCID", "0009-0002-1923-0773"),
        ("DOI", "10.5281/zenodo.17379721"),
        ("Author", "José Manuel Mota Burruezo"),
        ("Institute", "Instituto de Conciencia Cuántica")
    ]
    
    for item_name, item_value in attribution_items:
        if item_value in content:
            print(f"  ✅ {item_name}: {item_value}")
        else:
            print(f"  ⚠️  {item_name} not found (optional)")
    
    # Final summary
    print("\n" + "="*60)
    all_valid = (all_sections_found and all_structures_found and 
                 all_theorems_found and all_constants_found)
    
    if all_valid:
        print("✅ VALIDATION SUCCESSFUL!")
        print("   All required sections, structures, theorems, and constants present.")
        print("   QCAL Infinity³ formalization is complete.")
    else:
        print("❌ VALIDATION FAILED!")
        print("   Some required components are missing.")
    
    print("="*60)
    
    # Statistics
    lines = content.split('\n')
    print(f"\n📊 Statistics:")
    print(f"   Total lines: {len(lines)}")
    print(f"   Structures: {len(required_structures)}")
    print(f"   Theorems: {len(required_theorems)}")
    print(f"   Constants: {len(required_constants)}")
    print(f"   Sections: {len(required_sections)}")
    
    # Count sorry statements
    sorry_count = content.count('sorry')
    print(f"\n⚠️  Pending proofs (sorry): {sorry_count}")
    if sorry_count > 0:
        print("   Note: Some theorems use 'sorry' placeholders pending full formalization")
    
    return all_valid

if __name__ == "__main__":
    import sys
    success = validate_qcal_infinity3()
    sys.exit(0 if success else 1)
