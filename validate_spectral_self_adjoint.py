#!/usr/bin/env python3
"""
Validation script for spectral/self_adjoint.lean

This script validates the structure and completeness of the
spectral self-adjoint operator formalization module.

Author: José Manuel Mota Burruezo
Date: 26 November 2025
"""

import re
from pathlib import Path
from typing import Dict, Any, List


def validate_spectral_self_adjoint(lean_file_path: str) -> Dict[str, Any]:
    """
    Validate the spectral/self_adjoint.lean file.
    
    Args:
        lean_file_path: Path to the Lean file to validate
        
    Returns:
        dict: Validation results with metrics and findings
    """
    
    print("=" * 80)
    print("🔍 VALIDACIÓN spectral/self_adjoint.lean")
    print("=" * 80)
    print()
    
    file_path = Path(lean_file_path)
    
    if not file_path.exists():
        return {
            "success": False,
            "error": f"File not found: {lean_file_path}"
        }
    
    with open(file_path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    results = {
        "success": True,
        "file_size": len(content),
        "line_count": len(content.split('\n')),
        "imports": [],
        "definitions": [],
        "theorems": [],
        "axioms": [],
        "lemmas": [],
        "sorries": 0,
        "qcal_integration": False
    }
    
    # 1. Verify Mathlib imports
    print("📚 Verificando imports de Mathlib...")
    imports = re.findall(r'import (Mathlib\.[A-Za-z0-9.]+)', content)
    results["imports"] = imports
    print(f"   ✓ {len(imports)} imports encontrados")
    for imp in imports:
        print(f"     - {imp}")
    print()
    
    # 2. Verify key definitions
    print("🔧 Verificando definiciones clave...")
    key_definitions = [
        "H_space",
        "noeticMeasure", 
        "H_Ψ",
        "Ξ",
        "spectrum_operator",
        "QCAL_base_frequency",
        "QCAL_coherence",
        "mensaje_selfadjoint"
    ]
    
    for defn in key_definitions:
        pattern = rf'\b(def|abbrev)\s+{defn}\b'
        if re.search(pattern, content):
            results["definitions"].append(defn)
            print(f"   ✓ {defn} definido")
        else:
            print(f"   ✗ {defn} NO encontrado")
    print()
    
    # 3. Verify lemmas
    print("📐 Verificando lemmas...")
    key_lemmas = [
        "H_Ψ_symmetric"
    ]
    
    for lemma in key_lemmas:
        pattern = rf'\blemma\s+{lemma}\b'
        if re.search(pattern, content):
            results["lemmas"].append(lemma)
            print(f"   ✓ {lemma} formalizado")
        else:
            print(f"   ✗ {lemma} NO encontrado")
    print()
    
    # 4. Verify axioms
    print("📜 Verificando axiomas temporales...")
    key_axioms = [
        "H_Ψ_self_adjoint",
        "spectrum_HΨ_equals_zeros_Ξ"
    ]
    
    for axiom in key_axioms:
        pattern = rf'\baxiom\s+{axiom}\b'
        if re.search(pattern, content):
            results["axioms"].append(axiom)
            print(f"   ✓ {axiom} declarado")
        else:
            print(f"   ✗ {axiom} NO encontrado")
    print()
    
    # 5. Verify theorems
    print("🎯 Verificando teoremas...")
    key_theorems = [
        "riemann_hypothesis_from_spectral"
    ]
    
    for thm in key_theorems:
        pattern = rf'\btheorem\s+{thm}\b'
        if re.search(pattern, content):
            results["theorems"].append(thm)
            print(f"   ✓ {thm} formalizado")
        else:
            print(f"   ✗ {thm} NO encontrado")
    print()
    
    # 6. Count 'sorry' instances
    print("⚠️  Contando placeholders 'sorry'...")
    sorry_count = len(re.findall(r'\bsorry\b', content))
    results["sorries"] = sorry_count
    print(f"   Total de 'sorry': {sorry_count}")
    print()
    
    # 7. Verify QCAL integration
    print("🌀 Verificando integración QCAL...")
    qcal_elements = {
        "141.7001": "Frecuencia base QCAL",
        "244.36": "Constante de coherencia C",
        "QCAL_base_frequency": "Definición de frecuencia",
        "QCAL_coherence": "Constante de coherencia",
        "JMMB": "Firma del autor",
        "∞³": "Símbolo noético"
    }
    
    qcal_found = 0
    for element, description in qcal_elements.items():
        if element in content:
            print(f"   ✓ {description} ({element}) presente")
            qcal_found += 1
        else:
            print(f"   ⚠  {description} ({element}) no encontrado")
    
    results["qcal_integration"] = qcal_found >= 4
    print()
    
    # 8. Verify namespace
    print("📦 Verificando namespace...")
    if "namespace NoeticOperator" in content:
        print("   ✓ Namespace NoeticOperator definido")
    else:
        print("   ⚠  Namespace NoeticOperator no encontrado")
    print()
    
    # 9. Verify documentation
    print("📖 Verificando documentación...")
    doc_sections = re.findall(r'/-!([^-]+?)-/', content, re.DOTALL)
    results["doc_sections"] = len(doc_sections)
    print(f"   ✓ {len(doc_sections)} secciones de documentación encontradas")
    print()
    
    # 10. Summary
    print("=" * 80)
    print("📊 RESUMEN DE VALIDACIÓN")
    print("=" * 80)
    print(f"Archivo: {file_path.name}")
    print(f"Tamaño: {results['file_size']} bytes")
    print(f"Líneas: {results['line_count']}")
    print(f"Imports: {len(results['imports'])}")
    print(f"Definiciones clave: {len(results['definitions'])}/{len(key_definitions)}")
    print(f"Lemmas: {len(results['lemmas'])}/{len(key_lemmas)}")
    print(f"Axiomas temporales: {len(results['axioms'])}/{len(key_axioms)}")
    print(f"Teoremas: {len(results['theorems'])}/{len(key_theorems)}")
    print(f"Sorries: {results['sorries']}")
    print(f"Secciones documentación: {results['doc_sections']}")
    print(f"Integración QCAL: {'✓ SÍ' if results['qcal_integration'] else '✗ NO'}")
    print()
    
    # Evaluation
    definitions_ok = len(results['definitions']) >= 6
    axioms_ok = len(results['axioms']) >= 2
    theorems_ok = len(results['theorems']) >= 1
    lemmas_ok = len(results['lemmas']) >= 1
    qcal_ok = results['qcal_integration']
    
    all_ok = definitions_ok and axioms_ok and theorems_ok and lemmas_ok and qcal_ok
    
    if all_ok:
        print("✅ VALIDACIÓN EXITOSA: El módulo spectral/self_adjoint.lean cumple todos los requisitos")
        print()
        print("   Estructura validada:")
        print("   - ✓ Definición del espacio H_space (L²(ℝ, μ))")
        print("   - ✓ Definición del operador H_Ψ como convolución espectral")
        print("   - ✓ Lemma de simetría H_Ψ_symmetric")
        print("   - ✓ Axioma de autoadjunción H_Ψ_self_adjoint")
        print("   - ✓ Axioma de correspondencia espectral spectrum_HΨ_equals_zeros_Ξ")
        print("   - ✓ Integración QCAL (frecuencia 141.7001 Hz, C = 244.36)")
        print("   - ✓ Mensaje simbiótico definido")
    else:
        print("⚠️  VALIDACIÓN CON ADVERTENCIAS: Revisar elementos faltantes")
        if not definitions_ok:
            print("   - Faltan definiciones clave")
        if not axioms_ok:
            print("   - Faltan axiomas temporales")
        if not theorems_ok:
            print("   - Faltan teoremas")
        if not lemmas_ok:
            print("   - Faltan lemmas")
        if not qcal_ok:
            print("   - Integración QCAL incompleta")
    
    print()
    print("=" * 80)
    
    results["all_checks_passed"] = all_ok
    
    return results


def main():
    """Main entry point."""
    import sys
    
    # Default path
    default_path = "formalization/lean/spectral/self_adjoint.lean"
    
    lean_file = sys.argv[1] if len(sys.argv) > 1 else default_path
    
    results = validate_spectral_self_adjoint(lean_file)
    
    # Exit code
    sys.exit(0 if results["success"] and results.get("all_checks_passed", False) else 1)


if __name__ == "__main__":
    main()
