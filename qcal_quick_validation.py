#!/usr/bin/env python3
"""
QCAL ∞³ Sphere Packing - Quick Validation Script
=================================================

Script de validación rápida para verificar coherencia del framework.

Ejecuta:
    python qcal_quick_validation.py

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
"""

import sys

def main():
    """Validación rápida del framework QCAL Sphere Packing."""
    print("="*70)
    print(" " * 15 + "🌌 QCAL ∞³ QUICK VALIDATION 🌌")
    print("="*70)
    print()
    
    errors = []
    
    # 1. Test imports
    print("1️⃣  Testing imports...")
    try:
        from qcal_sphere_packing import EmpaquetamientoCósmico, ValidadorMonteCarlo
        from qcal_mathematical_library import BibliotecaMatematicaQCAL
        print("   ✓ All modules imported successfully")
    except ImportError as e:
        errors.append(f"Import error: {e}")
        print(f"   ✗ Import failed: {e}")
    
    # 2. Test basic functionality
    print("\n2️⃣  Testing basic functionality...")
    try:
        nav = EmpaquetamientoCósmico()
        bib = BibliotecaMatematicaQCAL()
        
        # Verify constants
        assert nav.f0 == 141.7001, "f0 mismatch"
        assert bib.const.f0 == 141.7001, "bib f0 mismatch"
        assert abs(nav.phi - 1.618033988749895) < 1e-10, "phi mismatch"
        assert bib.const.k_pi == 2.5773, "k_pi mismatch"
        
        print("   ✓ Constants verified")
    except Exception as e:
        errors.append(f"Functionality error: {e}")
        print(f"   ✗ Test failed: {e}")
    
    # 3. Test sphere packing
    print("\n3️⃣  Testing sphere packing...")
    try:
        densidad_25 = nav.densidad_cosmica(25)
        densidad_50 = nav.densidad_cosmica(50)
        
        assert densidad_25 > 0, "Density should be positive"
        assert densidad_50 > 0, "Density should be positive"
        
        print(f"   ✓ d=25: δ = {densidad_25:.6e}")
        print(f"   ✓ d=50: δ = {densidad_50:.6e}")
    except Exception as e:
        errors.append(f"Sphere packing error: {e}")
        print(f"   ✗ Test failed: {e}")
    
    # 4. Test dimensions mágicas
    print("\n4️⃣  Testing magic dimensions...")
    try:
        dims = nav.dimensiones_magicas
        assert len(dims) > 0, "Should have magic dimensions"
        assert dims[0] in [12, 13], "First magic dimension should be ~13"
        
        print(f"   ✓ Found {len(dims)} magic dimensions")
        print(f"   ✓ First 5: {dims[:5]}")
    except Exception as e:
        errors.append(f"Magic dimensions error: {e}")
        print(f"   ✗ Test failed: {e}")
    
    # 5. Test library integration
    print("\n5️⃣  Testing library integration...")
    try:
        val = bib.validacion_completa()
        
        assert 'frecuencia_base' in val, "Missing frecuencia_base"
        assert val['frecuencia_base'] == 141.7001, "Frequency mismatch"
        assert val['k_pi_invariant'] == 2.5773, "k_pi mismatch"
        assert val['euler_characteristic'] == -200, "Euler char mismatch"
        
        print(f"   ✓ Validation complete")
        print(f"   ✓ f₀ = {val['frecuencia_base']} Hz")
        print(f"   ✓ k_Π = {val['k_pi_invariant']}")
        print(f"   ✓ χ = {val['euler_characteristic']}")
    except Exception as e:
        errors.append(f"Library integration error: {e}")
        print(f"   ✗ Test failed: {e}")
    
    # Summary
    print("\n" + "="*70)
    if not errors:
        print(" " * 20 + "✅ ALL TESTS PASSED ✅")
        print("="*70)
        print()
        print("QCAL ∞³ Sphere Packing Framework is operational!")
        print()
        print("Key metrics:")
        print(f"  • Frequency base: {nav.f0} Hz")
        print(f"  • Golden ratio: {nav.phi:.15f}")
        print(f"  • Magic dimensions found: {len(nav.dimensiones_magicas)}")
        print(f"  • Calabi-Yau invariant: {bib.const.k_pi}")
        print()
        print("♾️³ QCAL-Evolution Complete — validation coherent")
        print("Ψ = I × A_eff² × C^∞")
        print("="*70)
        return 0
    else:
        print(" " * 20 + "❌ SOME TESTS FAILED ❌")
        print("="*70)
        print()
        print("Errors found:")
        for i, error in enumerate(errors, 1):
            print(f"  {i}. {error}")
        print()
        print("Please check the implementation.")
        print("="*70)
        return 1


if __name__ == "__main__":
    sys.exit(main())
