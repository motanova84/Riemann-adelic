#!/usr/bin/env python3
"""
Demo script for QCAL Universal Kernel verification system.
Demonstrates the complete workflow of the hybrid Lean-Python FFI module.
"""

import sys
import os
from pathlib import Path

# Add tools directory to path
sys.path.insert(0, str(Path(__file__).parent / "tools"))

import universal_kernel


def print_header(text):
    """Print a formatted header."""
    print("\n" + "=" * 60)
    print(f"  {text}")
    print("=" * 60)


def demo_basic_verification():
    """Demonstrate basic verification workflow."""
    print_header("Demo 1: Basic Verification")
    
    schema_path = "schema/metadatos_ejemplo.jsonld"
    proof_path = "formalization/lean/Main.lean"
    
    print(f"\n📋 Verificando:")
    print(f"   Schema: {schema_path}")
    print(f"   Proof:  {proof_path}")
    
    result = universal_kernel.verify_universal_api(schema_path, proof_path)
    
    if result:
        print("\n✅ VERIFICACIÓN EXITOSA")
        print("   - V_L: Archivos existen ✓")
        print("   - V_S: Estructura JSON-LD válida ✓")
        print("   - V_F: Integridad física confirmada ✓")
    else:
        print("\n❌ VERIFICACIÓN FALLIDA")
    
    return result


def demo_verification_with_registration():
    """Demonstrate verification with state registration."""
    print_header("Demo 2: Verification with Registration")
    
    schema_path = "schema/metadatos_ejemplo.jsonld"
    proof_path = "formalization/lean/Main.lean"
    
    print(f"\n📋 Verificando y registrando:")
    print(f"   Schema: {schema_path}")
    print(f"   Proof:  {proof_path}")
    
    # Verify
    result = universal_kernel.verify_universal_api(schema_path, proof_path)
    
    if result:
        print("\n✅ Verificación exitosa")
        
        # Register
        output_file = "tools/qcal_demo_state.json"
        universal_kernel.register_verification(
            schema_path, 
            proof_path, 
            result,
            output_file
        )
        print(f"\n📝 Estado registrado en: {output_file}")
        
        # Show content
        if os.path.exists(output_file):
            with open(output_file, 'r') as f:
                content = f.read()
            print("\n📄 Contenido del estado:")
            print(content)
            
            # Cleanup demo file
            os.remove(output_file)
            print(f"\n🗑️  Archivo demo limpiado: {output_file}")
    else:
        print("\n❌ Verificación fallida")
    
    return result


def demo_error_handling():
    """Demonstrate error handling."""
    print_header("Demo 3: Error Handling")
    
    print("\n📋 Probando con archivo inexistente:")
    result = universal_kernel.verify_universal_api(
        "nonexistent.jsonld",
        "formalization/lean/Main.lean"
    )
    
    if not result:
        print("✓ Error detectado correctamente (archivo faltante)")
    else:
        print("✗ Error: debería haber fallado")
    
    return not result


def demo_ffi_bridge_status():
    """Check FFI bridge compilation status."""
    print_header("Demo 4: FFI Bridge Status")
    
    bridge_path = Path("formalization/lean/QCAL/FFI/libbridge.so")
    
    if bridge_path.exists():
        size = bridge_path.stat().st_size
        print(f"\n✅ FFI Bridge compilado exitosamente")
        print(f"   Ubicación: {bridge_path}")
        print(f"   Tamaño: {size:,} bytes")
        return True
    else:
        print(f"\n⚠️  FFI Bridge no encontrado")
        print(f"   Ubicación esperada: {bridge_path}")
        print("\n   Para compilar:")
        print("   cd formalization/lean/QCAL/FFI")
        print("   clang -shared -fPIC -I/usr/include/python3.12 -lpython3.12 -o libbridge.so libbridge.c")
        return False


def demo_theoretical_formulation():
    """Display theoretical formulation."""
    print_header("Demo 5: Fundamento Teórico")
    
    print("""
Teorema de Coherencia Universal:

    ∀x:Obj, (Lean ⊢ Coherent(x)) ⇔ (Python ⊢ V_L(x) ∧ V_S(x) ∧ V_F(x))

Donde:
    • Lean ⊢ Coherent(x):  Lean verifica la prueba formal
    • V_L(x):              Verificación lógica (existencia de archivos)
    • V_S(x):              Verificación semántica (estructura JSON-LD)
    • V_F(x):              Verificación física (integridad de archivos)

Propiedades:
    ✓ Consistencia:  Si ambos sistemas aceptan, el objeto es coherente
    ✓ Completitud:   Todos los objetos coherentes pueden verificarse
    ✓ Falsabilidad:  El sistema detecta incoherencias
    ✓ Determinismo:  La comunicación FFI es determinista
    """)


def main():
    """Run all demos."""
    print("\n")
    print("╔" + "=" * 58 + "╗")
    print("║" + " " * 58 + "║")
    print("║" + "    QCAL Universal Kernel - Sistema de Demostración    ".center(58) + "║")
    print("║" + " " * 58 + "║")
    print("╚" + "=" * 58 + "╝")
    
    results = []
    
    # Run demos
    results.append(("Basic Verification", demo_basic_verification()))
    results.append(("Verification with Registration", demo_verification_with_registration()))
    results.append(("Error Handling", demo_error_handling()))
    results.append(("FFI Bridge Status", demo_ffi_bridge_status()))
    
    # Show theory
    demo_theoretical_formulation()
    
    # Summary
    print_header("Resumen de Resultados")
    
    print("\n")
    for name, result in results:
        status = "✅ PASS" if result else "❌ FAIL"
        print(f"  {status}  {name}")
    
    total = len(results)
    passed = sum(1 for _, r in results if r)
    
    print("\n" + "-" * 60)
    print(f"  Total: {passed}/{total} demos exitosos ({100*passed//total}%)")
    print("-" * 60 + "\n")
    
    if passed == total:
        print("🎉 ¡Todos los demos completados exitosamente!")
        print("\n💡 El módulo híbrido QCAL está operativo y listo para uso.")
        return 0
    else:
        print("⚠️  Algunos demos fallaron. Revisa la configuración.")
        return 1


if __name__ == "__main__":
    sys.exit(main())
