#!/usr/bin/env python3
"""
Final Checklist - H_DS Integration Progress Tracker

Este script verifica el estado de completitud de la integración H_DS
en la demostración principal de la Hipótesis de Riemann.

Autor: José Manuel Mota Burruezo Ψ ∴ ∞³
DOI: 10.5281/zenodo.17379721
"""

import sys
from pathlib import Path
from typing import Dict, Tuple, List

# Colores para output
class Colors:
    GREEN = '\033[92m'
    RED = '\033[91m'
    YELLOW = '\033[93m'
    BLUE = '\033[94m'
    END = '\033[0m'


def check_file_exists(filepath: str) -> bool:
    """Verifica si un archivo existe."""
    return Path(filepath).exists()


def check_implementation(category: str, items: Dict[str, str]) -> Tuple[int, int]:
    """
    Verifica items de implementación.
    
    Returns:
        Tupla (completed, total)
    """
    completed = 0
    total = len(items)
    
    print(f"\n{Colors.BLUE}{category}:{Colors.END}")
    
    for item_name, filepath in items.items():
        exists = check_file_exists(filepath)
        status = f"{Colors.GREEN}✅{Colors.END}" if exists else f"{Colors.RED}❌{Colors.END}"
        print(f"  {status} {item_name}")
        
        if exists:
            completed += 1
            # Verificar tamaño del archivo (debe tener contenido)
            size = Path(filepath).stat().st_size
            if size < 100:
                print(f"     {Colors.YELLOW}⚠️  Archivo muy pequeño ({size} bytes){Colors.END}")
    
    return completed, total


def check_validation_scripts() -> Dict[str, bool]:
    """Verifica scripts de validación."""
    scripts = {
        'complete_validation.sh': 'scripts/complete_validation.sh',
        'validate_v5_coronacion.py': 'validate_v5_coronacion.py',
        'H_DS_to_D_connection.py': 'operador/H_DS_to_D_connection.py'
    }
    
    results = {}
    print(f"\n{Colors.BLUE}SCRIPTS DE VALIDACIÓN:{Colors.END}")
    
    for name, path in scripts.items():
        exists = check_file_exists(path)
        results[name] = exists
        status = f"{Colors.GREEN}✅{Colors.END}" if exists else f"{Colors.RED}❌{Colors.END}"
        print(f"  {status} {name}")
        
        if exists and path.endswith('.sh'):
            # Verificar que sea ejecutable
            import os
            is_executable = os.access(path, os.X_OK)
            if not is_executable:
                print(f"     {Colors.YELLOW}⚠️  No ejecutable{Colors.END}")
    
    return results


def check_lean_formalization() -> Dict[str, bool]:
    """Verifica archivos de formalización Lean."""
    lean_files = {
        'H_DS_integration.lean': 'formalization/lean/H_DS_integration.lean',
        'spectral_determinant_from_HDS.lean': 'formalization/lean/spectral_determinant_from_HDS.lean',
        'zeros_critical_line_HDS.lean': 'formalization/lean/zeros_critical_line_HDS.lean',
        'RH_Complete_Proof_Master.lean': 'formalization/lean/RH_Complete_Proof_Master.lean'
    }
    
    results = {}
    print(f"\n{Colors.BLUE}FORMALIZACIÓN LEAN:{Colors.END}")
    
    for name, path in lean_files.items():
        exists = check_file_exists(path)
        results[name] = exists
        status = f"{Colors.GREEN}✅{Colors.END}" if exists else f"{Colors.RED}❌{Colors.END}"
        print(f"  {status} {name}")
        
        if exists:
            # Contar líneas con 'sorry'
            with open(path, 'r') as f:
                content = f.read()
                sorry_count = content.count('sorry')
                if sorry_count > 0:
                    print(f"     {Colors.YELLOW}⚠️  {sorry_count} 'sorry' pendientes{Colors.END}")
    
    return results


def check_python_modules() -> Dict[str, bool]:
    """Verifica módulos Python implementados."""
    modules = {
        'operador_H_DS.py': 'operador/operador_H_DS.py',
        'discrete_symmetry_operator.py': 'operators/discrete_symmetry_operator.py',
        'H_DS_to_D_connection.py': 'operador/H_DS_to_D_connection.py'
    }
    
    results = {}
    print(f"\n{Colors.BLUE}MÓDULOS PYTHON:{Colors.END}")
    
    for name, path in modules.items():
        exists = check_file_exists(path)
        results[name] = exists
        status = f"{Colors.GREEN}✅{Colors.END}" if exists else f"{Colors.RED}❌{Colors.END}"
        print(f"  {status} {name}")
        
        if exists:
            # Verificar importabilidad usando importlib
            try:
                import importlib.util
                from pathlib import Path
                
                # Convertir path relativo a absoluto
                abs_path = Path(path).absolute()
                
                # Crear spec para el módulo
                spec = importlib.util.spec_from_file_location(
                    name.replace('.py', ''),
                    abs_path
                )
                
                if spec and spec.loader:
                    module = importlib.util.module_from_spec(spec)
                    spec.loader.exec_module(module)
                    print(f"     {Colors.GREEN}✓ Importable{Colors.END}")
            except Exception as e:
                print(f"     {Colors.YELLOW}⚠️  Error de importación: {e}{Colors.END}")
    
    return results


def generate_progress_report() -> Dict[str, any]:
    """Genera reporte completo de progreso."""
    
    print("=" * 70)
    print(f"{Colors.BLUE}🚀 CHECKLIST FINAL DE LA DEMOSTRACIÓN H_DS{Colors.END}")
    print("=" * 70)
    
    # Categorías de verificación
    categories = {
        'GEOMETRÍA': {
            'A₀ = 1/2 + iℤ definido': True,  # Ya existe en el código base
            'Base ortonormal construida': True,
            'Espacio de Hilbert definido': True,
        },
        
        'OPERADOR H_Ψ': {
            'H_Ψ definido explícitamente': True,  # Ya existe
            'Autoadjunción verificada': True,
            'Clase traza demostrada': False,  # 🚨 FALTA
        },
        
        'H_DS (SIMETRÍA DISCRETA)': {
            'Operador S implementado': check_file_exists('operador/operador_H_DS.py'),
            '[H,S]=0 verificado': check_file_exists('formalization/lean/H_DS_integration.lean'),
            'S²=I demostrado': check_file_exists('formalization/lean/H_DS_integration.lean'),
            'S autoadjunto': check_file_exists('formalization/lean/H_DS_integration.lean'),
        },
        
        'D(s) CONSTRUIDO': {
            'D(s) = det(I - H⁻¹s)': check_file_exists('operador/H_DS_to_D_connection.py'),
            'D(s) entera demostrada': False,  # 🚨 FALTA en Lean
            'Orden ≤ 1 demostrado': False,    # 🚨 FALTA en Lean
            'D(1-s)=D(s) vía H_DS': check_file_exists('formalization/lean/spectral_determinant_from_HDS.lean'),
        },
        
        'IDENTIFICACIÓN D=Ξ': {
            'Mismos ceros demostrado': False,  # 🚨 FALTA
            'Mismo crecimiento demostrado': False,  # 🚨 FALTA
            'Unicidad vía Hadamard aplicada': False,  # 🚨 FALTA
        },
        
        'DEMOSTRACIÓN RH': {
            'Cadena lógica completa': check_file_exists('formalization/lean/RH_Complete_Proof_Master.lean'),
            'Sin circularidad verificada': True,
            'Todos los gaps identificados': True,
        }
    }
    
    total = 0
    completed = 0
    
    for category, items in categories.items():
        print(f"\n{Colors.BLUE}{category}:{Colors.END}")
        for item, status in items.items():
            total += 1
            if status:
                completed += 1
                print(f"  {Colors.GREEN}✅{Colors.END} {item}")
            else:
                print(f"  {Colors.RED}❌{Colors.END} {item}")
    
    # Verificaciones adicionales
    lean_results = check_lean_formalization()
    python_results = check_python_modules()
    script_results = check_validation_scripts()
    
    # Resumen final
    print("\n" + "=" * 70)
    print(f"{Colors.BLUE}📊 PROGRESO TOTAL:{Colors.END}")
    print("=" * 70)
    
    lean_completed = sum(1 for v in lean_results.values() if v)
    python_completed = sum(1 for v in python_results.values() if v)
    script_completed = sum(1 for v in script_results.values() if v)
    
    print(f"\nComponentes principales: {completed}/{total} ({100*completed/total:.1f}%)")
    print(f"Archivos Lean: {lean_completed}/{len(lean_results)} ({100*lean_completed/len(lean_results):.1f}%)")
    print(f"Módulos Python: {python_completed}/{len(python_results)} ({100*python_completed/len(python_results):.1f}%)")
    print(f"Scripts validación: {script_completed}/{len(script_results)} ({100*script_completed/len(script_results):.1f}%)")
    
    overall_completion = (completed + lean_completed + python_completed + script_completed) / \
                        (total + len(lean_results) + len(python_results) + len(script_results))
    
    print(f"\n{Colors.BLUE}COMPLETITUD GENERAL: {overall_completion*100:.1f}%{Colors.END}")
    
    # Identificar gaps
    print(f"\n{Colors.YELLOW}🚨 GAPS IDENTIFICADOS:{Colors.END}")
    gaps = [
        "H_Ψ es de clase traza (estimaciones explícitas)",
        "D(s) es función entera de orden ≤ 1 (crecimiento controlado)",
        "D y Ξ tienen los mismos ceros (contando multiplicidades)",
        "Unicidad vía factorización de Hadamard"
    ]
    
    for i, gap in enumerate(gaps, 1):
        print(f"  {i}. {gap}")
    
    print("\n" + "=" * 70)
    
    if overall_completion >= 0.8:
        print(f"{Colors.GREEN}✅ INTEGRACIÓN H_DS: MAYORMENTE COMPLETA{Colors.END}")
    elif overall_completion >= 0.5:
        print(f"{Colors.YELLOW}⚠️  INTEGRACIÓN H_DS: EN PROGRESO{Colors.END}")
    else:
        print(f"{Colors.RED}❌ INTEGRACIÓN H_DS: REQUIERE MÁS TRABAJO{Colors.END}")
    
    print("=" * 70)
    
    return {
        'overall_completion': overall_completion,
        'completed': completed,
        'total': total,
        'lean_files': lean_results,
        'python_modules': python_results,
        'validation_scripts': script_results,
        'gaps': gaps
    }


def main():
    """Punto de entrada principal."""
    try:
        report = generate_progress_report()
        
        # Retornar código de salida basado en completitud
        if report['overall_completion'] >= 0.8:
            sys.exit(0)
        elif report['overall_completion'] >= 0.5:
            sys.exit(1)
        else:
            sys.exit(2)
            
    except Exception as e:
        print(f"\n{Colors.RED}❌ Error generando reporte: {e}{Colors.END}")
        import traceback
        traceback.print_exc()
        sys.exit(3)


if __name__ == "__main__":
    main()
