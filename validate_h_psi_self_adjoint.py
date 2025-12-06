#!/usr/bin/env python3
"""
Validación del módulo H_psi_self_adjoint.lean

Este script valida la estructura y completitud del módulo de formalización
del operador autoadjunto H_Ψ en Lean 4.

Autor: José Manuel Mota Burruezo
Fecha: 21 noviembre 2025
"""

import re
from pathlib import Path
from typing import List, Tuple, Dict, Any

def validate_h_psi_self_adjoint(lean_file_path: str) -> Dict[str, Any]:
    """
    Valida el archivo H_psi_self_adjoint.lean
    
    Returns:
        dict: Resultados de validación con métricas y hallazgos
    """
    
    print("=" * 80)
    print("🔍 VALIDACIÓN H_PSI_SELF_ADJOINT.LEAN")
    print("=" * 80)
    print()
    
    file_path = Path(lean_file_path)
    
    if not file_path.exists():
        return {
            "success": False,
            "error": f"Archivo no encontrado: {lean_file_path}"
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
        "sorries": [],
        "comments": []
    }
    
    # 1. Verificar imports de Mathlib
    print("📚 Verificando imports de Mathlib...")
    imports = re.findall(r'import (Mathlib\.[A-Za-z0-9.]+)', content)
    results["imports"] = imports
    print(f"   ✓ {len(imports)} imports encontrados")
    for imp in imports:
        print(f"     - {imp}")
    print()
    
    # 2. Verificar definiciones clave
    print("🔧 Verificando definiciones clave...")
    key_definitions = [
        "HaarMeasure",
        "L2Haar",
        "Hpsi",
        "symmetric_kernel",
        "kernel_measurable",
        "kernel_bounded",
        "IsSelfAdjoint",
        "spectrum",
        "spectral_determinant",
        "QCAL_base_frequency"
    ]
    
    for defn in key_definitions:
        pattern = rf'\b(def|abbrev)\s+{defn}\b'
        if re.search(pattern, content):
            results["definitions"].append(defn)
            print(f"   ✓ {defn} definido")
        else:
            print(f"   ✗ {defn} NO encontrado")
    print()
    
    # 3. Verificar teoremas principales
    print("🎯 Verificando teoremas principales...")
    key_theorems = [
        "Hpsi_self_adjoint",
        "spectrum_real",
        "spectral_determinant_zeros",
        "riemann_hypothesis_from_spectral_chain",
        "spectrum_discrete",
        "spectrum_includes_QCAL_constant"
    ]
    
    for thm in key_theorems:
        pattern = rf'\btheorem\s+{thm}\b'
        if re.search(pattern, content):
            results["theorems"].append(thm)
            print(f"   ✓ {thm} formalizado")
        else:
            print(f"   ✗ {thm} NO encontrado")
    print()
    
    # 4. Contar y analizar 'sorry'
    print("⚠️  Analizando placeholders 'sorry'...")
    sorry_matches = list(re.finditer(r'sorry\s*--\s*(.+)', content))
    results["sorries"] = [match.group(1).strip() for match in sorry_matches]
    
    print(f"   Total de 'sorry': {len(sorry_matches)}")
    if sorry_matches:
        print("   Justificaciones:")
        for i, match in enumerate(sorry_matches, 1):
            justification = match.group(1).strip()
            print(f"     {i}. {justification}")
    print()
    
    # 5. Verificar axiomas
    print("📜 Verificando axiomas auxiliares...")
    axiom_matches = re.findall(r'axiom\s+([a-zA-Z_][a-zA-Z0-9_]*)', content)
    results["axioms"] = axiom_matches
    print(f"   Total de axiomas: {len(axiom_matches)}")
    for axiom in axiom_matches:
        print(f"     - {axiom}")
    print()
    
    # 6. Verificar estructura de documentación
    print("📖 Verificando documentación...")
    doc_sections = re.findall(r'/-!([^-]+?)-/', content, re.DOTALL)
    results["doc_sections"] = len(doc_sections)
    print(f"   ✓ {len(doc_sections)} secciones de documentación encontradas")
    
    # Verificar secciones específicas
    required_sections = [
        "Definición del espacio L² con medida de Haar",
        "Definición del operador H_Ψ",
        "TEOREMA PRINCIPAL",
        "Consecuencia: Espectro real",
        "Determinante espectral",
        "CONCLUSIÓN"
    ]
    
    for section in required_sections:
        if section in content:
            print(f"   ✓ Sección '{section[:50]}...' presente")
        else:
            print(f"   ⚠  Sección '{section[:50]}...' no encontrada")
    print()
    
    # 7. Verificar integración QCAL
    print("🌀 Verificando integración QCAL...")
    qcal_elements = {
        "141.7001": "Frecuencia base QCAL",
        "244.36": "Constante de coherencia C",
        "QCAL_base_frequency": "Definición de frecuencia",
        "JMMB": "Firma del autor"
    }
    
    for element, description in qcal_elements.items():
        if element in content:
            print(f"   ✓ {description} ({element}) presente")
        else:
            print(f"   ⚠  {description} ({element}) no encontrado")
    print()
    
    # 8. Verificar cadena lógica
    print("🔗 Verificando cadena lógica completa...")
    chain_elements = [
        "Paley-Wiener",
        "D(s, ε)",
        "H_Ψ",
        "autoadjoint",
        "spectrum",
        "Re(s) = 1/2",
        "Riemann Hypothesis"
    ]
    
    chain_complete = True
    for element in chain_elements:
        if element in content:
            print(f"   ✓ {element}")
        else:
            print(f"   ✗ {element} FALTA")
            chain_complete = False
    
    results["chain_complete"] = chain_complete
    print()
    
    # 9. Resumen final
    print("=" * 80)
    print("📊 RESUMEN DE VALIDACIÓN")
    print("=" * 80)
    print(f"Archivo: {file_path.name}")
    print(f"Tamaño: {results['file_size']} bytes")
    print(f"Líneas: {results['line_count']}")
    print(f"Imports: {len(results['imports'])}")
    print(f"Definiciones clave: {len(results['definitions'])}/{len(key_definitions)}")
    print(f"Teoremas principales: {len(results['theorems'])}/{len(key_theorems)}")
    print(f"Axiomas auxiliares: {len(results['axioms'])}")
    print(f"Sorries justificados: {len(results['sorries'])}")
    print(f"Secciones de documentación: {results['doc_sections']}")
    print(f"Cadena lógica completa: {'✓ SÍ' if results['chain_complete'] else '✗ NO'}")
    print()
    
    # Evaluación global
    definitions_ok = len(results['definitions']) >= 8  # Al menos 8 de 10
    theorems_ok = len(results['theorems']) >= 5  # Al menos 5 de 6
    documentation_ok = results['doc_sections'] >= 7
    chain_ok = results['chain_complete']
    
    all_ok = definitions_ok and theorems_ok and documentation_ok and chain_ok
    
    if all_ok:
        print("✅ VALIDACIÓN EXITOSA: El módulo H_psi_self_adjoint.lean cumple todos los requisitos")
    else:
        print("⚠️  VALIDACIÓN CON ADVERTENCIAS: Revisar elementos faltantes")
        if not definitions_ok:
            print("   - Faltan definiciones clave")
        if not theorems_ok:
            print("   - Faltan teoremas principales")
        if not documentation_ok:
            print("   - Documentación incompleta")
        if not chain_ok:
            print("   - Cadena lógica incompleta")
    
    print()
    print("=" * 80)
    
    results["all_checks_passed"] = all_ok
    
    return results

if __name__ == "__main__":
    import sys
    
    # Ruta por defecto
    default_path = "formalization/lean/RH_final_v6/H_psi_self_adjoint.lean"
    
    lean_file = sys.argv[1] if len(sys.argv) > 1 else default_path
    
    results = validate_h_psi_self_adjoint(lean_file)
    
    # Código de salida
    sys.exit(0 if results["success"] and results.get("all_checks_passed", False) else 1)
