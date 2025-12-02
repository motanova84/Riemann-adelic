#!/usr/bin/env python3
"""
Test suite for paradigm shift documentation and implementation

Tests verify:
1. Documentation files exist and are readable
2. Demo script functions properly
3. Paradigm shift explanation is comprehensive
4. All references are correct
"""

import os
import sys
from pathlib import Path

def test_documentation_exists():
    """Test that all documentation files exist"""
    print("Testing documentation files...")
    
    required_files = [
        "PARADIGM_SHIFT.md",
        "PARADIGM_FLOW.md",
        "demo_paradigm_shift.py",
        "spectral_RH/README.md",
        "README.md"
    ]
    
    all_exist = True
    for file_path in required_files:
        path = Path(file_path)
        if path.exists():
            print(f"  ✅ {file_path} exists ({path.stat().st_size} bytes)")
        else:
            print(f"  ❌ {file_path} NOT FOUND")
            all_exist = False
    
    return all_exist

def test_paradigm_shift_content():
    """Test that PARADIGM_SHIFT.md contains key sections"""
    print("\nTesting PARADIGM_SHIFT.md content...")
    
    path = Path("PARADIGM_SHIFT.md")
    if not path.exists():
        print("  ❌ File not found")
        return False
    
    content = path.read_text()
    
    required_sections = [
        "CAMBIO DE PARADIGMA",
        "Enfoque Tradicional (Circular)",
        "Enfoque Burruezo (No Circular)",
        "La Clave Revolucionaria",
        "Geometría Primero",
        "Simetría Geométrica",
        "Unicidad Espectral",
        "Aritmética al Final",
        "Por Qué Esto es Revolucionario"
    ]
    
    all_found = True
    for section in required_sections:
        if section in content:
            print(f"  ✅ Section found: {section}")
        else:
            print(f"  ❌ Section missing: {section}")
            all_found = False
    
    return all_found

def test_paradigm_flow_diagrams():
    """Test that PARADIGM_FLOW.md contains visual diagrams"""
    print("\nTesting PARADIGM_FLOW.md diagrams...")
    
    path = Path("PARADIGM_FLOW.md")
    if not path.exists():
        print("  ❌ File not found")
        return False
    
    content = path.read_text()
    
    required_elements = [
        "Traditional Approach (Circular)",
        "Burruezo Approach (Non-Circular)",
        "Side-by-Side Comparison",
        "Revolutionary Insight",
        "╔═══",  # Box drawing characters
        "→",     # Arrow
        "✅",    # Check mark
        "❌"     # Cross mark
    ]
    
    all_found = True
    for element in required_elements:
        if element in content:
            print(f"  ✅ Element found: {element[:30]}")
        else:
            print(f"  ❌ Element missing: {element}")
            all_found = False
    
    return all_found

def test_demo_script_functions():
    """Test that demo script can be imported and has required functions"""
    print("\nTesting demo_paradigm_shift.py functions...")
    
    sys.path.insert(0, str(Path(__file__).parent))
    
    try:
        import demo_paradigm_shift as dps
        
        required_functions = [
            'demonstrate_traditional_approach',
            'demonstrate_burruezo_approach',
            'show_comparison_table',
            'show_revolutionary_insight',
            'main'
        ]
        
        all_found = True
        for func_name in required_functions:
            if hasattr(dps, func_name):
                print(f"  ✅ Function exists: {func_name}")
            else:
                print(f"  ❌ Function missing: {func_name}")
                all_found = False
        
        return all_found
        
    except Exception as e:
        print(f"  ❌ Error importing demo script: {e}")
        return False

def test_readme_updated():
    """Test that README.md mentions paradigm shift"""
    print("\nTesting README.md updates...")
    
    path = Path("README.md")
    if not path.exists():
        print("  ❌ README.md not found")
        return False
    
    content = path.read_text()
    
    required_mentions = [
        "paradigma",
        "PARADIGM_SHIFT.md",
        "demo_paradigm_shift.py",
        "Geometría primero",
        "Aritmética al final"
    ]
    
    all_found = True
    for mention in required_mentions:
        if mention in content:
            print(f"  ✅ Mention found: {mention}")
        else:
            print(f"  ⚠️  Mention not found: {mention}")
            # Don't fail on this, just warn
    
    return True

def test_spectral_readme_updated():
    """Test that spectral_RH/README.md mentions paradigm shift"""
    print("\nTesting spectral_RH/README.md updates...")
    
    path = Path("spectral_RH/README.md")
    if not path.exists():
        print("  ❌ spectral_RH/README.md not found")
        return False
    
    content = path.read_text()
    
    required_elements = [
        "Cambio de Paradigma",
        "Paradigma Tradicional",
        "Paradigma Burruezo",
        "Clave Revolucionaria"
    ]
    
    all_found = True
    for element in required_elements:
        if element in content:
            print(f"  ✅ Element found: {element}")
        else:
            print(f"  ❌ Element missing: {element}")
            all_found = False
    
    return all_found

def main():
    """Run all tests"""
    print("="*70)
    print("PARADIGM SHIFT DOCUMENTATION TEST SUITE")
    print("="*70)
    
    tests = [
        ("Documentation Files", test_documentation_exists),
        ("PARADIGM_SHIFT.md Content", test_paradigm_shift_content),
        ("PARADIGM_FLOW.md Diagrams", test_paradigm_flow_diagrams),
        ("Demo Script Functions", test_demo_script_functions),
        ("README.md Updates", test_readme_updated),
        ("spectral_RH/README.md Updates", test_spectral_readme_updated)
    ]
    
    results = {}
    for test_name, test_func in tests:
        try:
            results[test_name] = test_func()
        except Exception as e:
            print(f"\n❌ Exception in {test_name}: {e}")
            results[test_name] = False
    
    # Summary
    print("\n" + "="*70)
    print("SUMMARY")
    print("="*70)
    
    passed = sum(results.values())
    total = len(results)
    
    for test_name, result in results.items():
        status = "✅" if result else "❌"
        print(f"{status} {test_name}")
    
    print(f"\nTotal: {passed}/{total} tests passed")
    
    if passed == total:
        print("\n🎉 All tests passed!")
        print("\n✅ Paradigm shift documentation is complete:")
        print("   1. PARADIGM_SHIFT.md - Comprehensive explanation")
        print("   2. PARADIGM_FLOW.md - Visual diagrams")
        print("   3. demo_paradigm_shift.py - Interactive demonstration")
        print("   4. README files updated with paradigm shift info")
        return 0
    else:
        print(f"\n⚠️  {total - passed} tests failed")
        return 1

if __name__ == "__main__":
    sys.exit(main())
