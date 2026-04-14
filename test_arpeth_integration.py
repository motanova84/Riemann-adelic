#!/usr/bin/env python3
"""
test_arpeth_integration.py
--------------------------------------------------------
Test de integración del framework Arpeth con QCAL ∞³

Verifica que el framework Arpeth se integra correctamente con:
- Constantes QCAL (.qcal_beacon)
- Sistema de validación existente
- Estructura del repositorio

José Manuel Mota Burruezo Ψ ∞³ — Instituto Conciencia Cuántica
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
--------------------------------------------------------
"""

import os
import sys

def test_qcal_beacon_integration():
    """Verifica integración con .qcal_beacon."""
    print("Testing QCAL beacon integration...")
    
    beacon_path = "/home/runner/work/Riemann-adelic/Riemann-adelic/.qcal_beacon"
    
    if not os.path.exists(beacon_path):
        print("  ✗ .qcal_beacon not found")
        return False
    
    with open(beacon_path, 'r') as f:
        content = f.read()
    
    # Verificar constantes clave
    checks = [
        ("frequency = 141.7001 Hz", "141.7001"),
        ("coherence = \"C = 244.36\"", "244.36"),
        ("doi_rh_final", "zenodo"),
    ]
    
    for check_name, check_value in checks:
        if check_value in content:
            print(f"  ✓ Found {check_name}")
        else:
            print(f"  ✗ Missing {check_name}")
            return False
    
    print("  ✓ QCAL beacon integration OK")
    return True

def test_file_structure():
    """Verifica estructura de archivos del framework."""
    print("\nTesting file structure...")
    
    base = "/home/runner/work/Riemann-adelic/Riemann-adelic/formalization/lean"
    
    required_files = [
        "Arpeth.lean",
        "Arpeth/Core/Constants.lean",
        "Arpeth/Core/Operator.lean",
        "Arpeth/README.md",
        "Arpeth/Examples/BasicUsage.lean",
    ]
    
    all_exist = True
    for file in required_files:
        path = os.path.join(base, file)
        if os.path.exists(path):
            size = os.path.getsize(path)
            print(f"  ✓ {file} ({size} bytes)")
        else:
            print(f"  ✗ {file} not found")
            all_exist = False
    
    if all_exist:
        print("  ✓ File structure OK")
    
    return all_exist

def test_lakefile_integration():
    """Verifica que lakefile.lean incluye la librería Arpeth."""
    print("\nTesting lakefile integration...")
    
    lakefile_path = "/home/runner/work/Riemann-adelic/Riemann-adelic/formalization/lean/lakefile.lean"
    
    if not os.path.exists(lakefile_path):
        print("  ✗ lakefile.lean not found")
        return False
    
    with open(lakefile_path, 'r') as f:
        content = f.read()
    
    if "lean_lib Arpeth" in content:
        print("  ✓ Arpeth library defined in lakefile")
    else:
        print("  ✗ Arpeth library NOT found in lakefile")
        return False
    
    if "roots := #[`Arpeth]" in content or ".submodules `Arpeth" in content:
        print("  ✓ Arpeth roots configured")
    else:
        print("  ✗ Arpeth roots NOT configured")
        return False
    
    print("  ✓ Lakefile integration OK")
    return True

def test_documentation():
    """Verifica que la documentación está completa."""
    print("\nTesting documentation...")
    
    doc_files = [
        "/home/runner/work/Riemann-adelic/Riemann-adelic/formalization/lean/Arpeth/README.md",
        "/home/runner/work/Riemann-adelic/Riemann-adelic/ARPETH_IMPLEMENTATION_SUMMARY.md",
    ]
    
    all_ok = True
    for doc_file in doc_files:
        if os.path.exists(doc_file):
            size = os.path.getsize(doc_file)
            print(f"  ✓ {os.path.basename(doc_file)} exists ({size} bytes)")
            
            # Verificar contenido mínimo
            with open(doc_file, 'r') as f:
                content = f.read()
            
            if "141.7001" in content and "H_Ψ" in content or "H_Psi" in content:
                print(f"    ✓ Contains expected content")
            else:
                print(f"    ✗ Missing expected content")
                all_ok = False
        else:
            print(f"  ✗ {os.path.basename(doc_file)} not found")
            all_ok = False
    
    if all_ok:
        print("  ✓ Documentation OK")
    
    return all_ok

def test_validation_script():
    """Verifica que el script de validación existe y es ejecutable."""
    print("\nTesting validation script...")
    
    script_path = "/home/runner/work/Riemann-adelic/Riemann-adelic/validate_arpeth_framework.py"
    
    if not os.path.exists(script_path):
        print("  ✗ validate_arpeth_framework.py not found")
        return False
    
    print("  ✓ Validation script exists")
    
    # Verificar que es ejecutable
    if os.access(script_path, os.X_OK):
        print("  ✓ Script is executable")
    else:
        print("  ⚠ Script is not executable (but can run with python3)")
    
    # Intentar importar y verificar funciones clave
    try:
        with open(script_path, 'r') as f:
            content = f.read()
        
        required_funcs = [
            "validate_constants",
            "validate_spectral_identity",
            "validate_operator_definition",
        ]
        
        for func in required_funcs:
            if f"def {func}" in content:
                print(f"  ✓ Function {func} defined")
            else:
                print(f"  ✗ Function {func} NOT found")
                return False
        
        print("  ✓ Validation script OK")
        return True
    
    except Exception as e:
        print(f"  ✗ Error reading validation script: {e}")
        return False

def test_lean_syntax_basic():
    """Verifica sintaxis básica de archivos Lean (sin compilar)."""
    print("\nTesting Lean syntax (basic)...")
    
    lean_files = [
        "/home/runner/work/Riemann-adelic/Riemann-adelic/formalization/lean/Arpeth.lean",
        "/home/runner/work/Riemann-adelic/Riemann-adelic/formalization/lean/Arpeth/Core/Constants.lean",
        "/home/runner/work/Riemann-adelic/Riemann-adelic/formalization/lean/Arpeth/Core/Operator.lean",
    ]
    
    all_ok = True
    for lean_file in lean_files:
        if not os.path.exists(lean_file):
            print(f"  ✗ {os.path.basename(lean_file)} not found")
            all_ok = False
            continue
        
        with open(lean_file, 'r') as f:
            content = f.read()
        
        # Verificaciones básicas de sintaxis
        checks = [
            ("import", "Has import statements"),
            ("namespace", "Has namespace"),
            ("def " or "theorem " or "axiom ", "Has definitions/theorems"),
        ]
        
        file_ok = True
        for keyword, desc in checks:
            if keyword in content:
                pass  # OK
            else:
                print(f"  ⚠ {os.path.basename(lean_file)}: Missing {desc}")
                file_ok = False
        
        if file_ok:
            print(f"  ✓ {os.path.basename(lean_file)} syntax looks OK")
        else:
            all_ok = False
    
    if all_ok:
        print("  ✓ Lean syntax (basic) OK")
    
    return all_ok

def main():
    """Ejecuta todos los tests de integración."""
    print("="*70)
    print("Arpeth Framework Integration Tests".center(70))
    print("="*70)
    
    tests = [
        ("QCAL Beacon Integration", test_qcal_beacon_integration),
        ("File Structure", test_file_structure),
        ("Lakefile Integration", test_lakefile_integration),
        ("Documentation", test_documentation),
        ("Validation Script", test_validation_script),
        ("Lean Syntax (Basic)", test_lean_syntax_basic),
    ]
    
    results = []
    for test_name, test_func in tests:
        try:
            result = test_func()
            results.append((test_name, result))
        except Exception as e:
            print(f"\n✗ Error running {test_name}: {e}")
            results.append((test_name, False))
    
    # Resumen
    print("\n" + "="*70)
    print("Test Summary".center(70))
    print("="*70)
    
    passed = sum(1 for _, result in results if result)
    total = len(results)
    
    for test_name, result in results:
        status = "✓ PASSED" if result else "✗ FAILED"
        print(f"  {status}: {test_name}")
    
    print(f"\nTotal: {passed}/{total} tests passed")
    
    if passed == total:
        print("\n✅ All integration tests passed!")
        print("Framework Arpeth is fully integrated with QCAL ∞³\n")
        return 0
    else:
        print(f"\n⚠️  {total - passed} test(s) failed")
        print("Please review the failures above.\n")
        return 1

if __name__ == "__main__":
    sys.exit(main())
