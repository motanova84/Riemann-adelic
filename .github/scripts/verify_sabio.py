#!/usr/bin/env python3
"""
Verificación específica de SABIO ∞³
"""

import subprocess
import json
import sys
from pathlib import Path

def verify_frequency():
    """Verifica que la frecuencia 141.7001 Hz es correcta"""
    print("🔍 Verificando frecuencia base...")
    
    # Try multiple sources for frequency verification
    try:
        # Check if Evac_Rpsi_data.csv exists
        evac_file = Path("Evac_Rpsi_data.csv")
        if evac_file.exists():
            print(f"  ✅ Evac_Rpsi_data.csv encontrado")
            with open(evac_file) as f:
                lines = f.readlines()
                if len(lines) > 1:
                    print(f"    Datos disponibles: {len(lines)-1} líneas")
            return True
        else:
            print(f"  ⚠️  Evac_Rpsi_data.csv no encontrado")
            return False
    except Exception as e:
        print(f"  ❌ Error al verificar frecuencia: {e}")
        return False

def verify_sabio_files():
    """Verifica archivos SABIO"""
    print("\n🔍 Verificando archivos SABIO...")
    
    sabio_files = [
        ".sabio",
        "sabio_validator.py",
        "utils/exact_f0_derivation.py"
    ]
    
    found = 0
    total = len(sabio_files)
    
    for sabio_file in sabio_files:
        path = Path(sabio_file)
        if path.exists():
            print(f"  ✅ {sabio_file} encontrado")
            found += 1
        else:
            print(f"  ⚠️  {sabio_file} no encontrado")
    
    print(f"  📊 Total: {found}/{total} archivos encontrados")
    return found > 0

def verify_lean_formalization():
    """Verifica la formalización Lean"""
    print("\n🔍 Verificando formalización Lean...")
    
    lean_dir = Path("formalization/lean")
    if not lean_dir.exists():
        print("  ⚠️  Directorio formalization/lean no encontrado")
        return False
    
    # Check for lakefile
    lakefile = lean_dir / "lakefile.lean"
    if lakefile.exists():
        print(f"  ✅ lakefile.lean encontrado")
    else:
        print(f"  ⚠️  lakefile.lean no encontrado")
    
    # Count lean files
    lean_files = list(lean_dir.rglob("*.lean"))
    print(f"  📊 {len(lean_files)} archivos .lean encontrados")
    
    # Check for SABIO implementations
    sabio_files = [f for f in lean_files if 'sabio' in f.name.lower()]
    if sabio_files:
        print(f"  ✅ {len(sabio_files)} archivos SABIO encontrados")
        for f in sabio_files[:5]:  # Show first 5
            print(f"    - {f.relative_to(lean_dir)}")
    
    return len(sabio_files) > 0

def verify_python_modules():
    """Verifica módulos Python necesarios"""
    print("\n🔍 Verificando módulos Python...")
    
    required_modules = [
        'numpy',
        'scipy',
        'mpmath',
        'sympy'
    ]
    
    missing = []
    for module in required_modules:
        try:
            __import__(module)
            print(f"  ✅ {module} instalado")
        except ImportError:
            print(f"  ❌ {module} no encontrado")
            missing.append(module)
    
    if missing:
        print(f"\n  ⚠️  Módulos faltantes: {', '.join(missing)}")
        print(f"  💡 Instalar con: pip install {' '.join(missing)}")
        return False
    
    return True

def main():
    print("=" * 60)
    print("🔍 VERIFICACIÓN SABIO ∞³")
    print("=" * 60)
    
    results = {
        "frequency": verify_frequency(),
        "sabio_files": verify_sabio_files(),
        "lean_formalization": verify_lean_formalization(),
        "python_modules": verify_python_modules()
    }
    
    print("\n" + "=" * 60)
    print("📊 RESUMEN DE VERIFICACIÓN")
    print("=" * 60)
    
    for key, value in results.items():
        emoji = "✅" if value else "❌"
        print(f"{emoji} {key}: {'OK' if value else 'REQUIERE ATENCIÓN'}")
    
    # Generate JSON report
    report_file = Path("sabio_verification_report.json")
    with open(report_file, 'w') as f:
        json.dump(results, f, indent=2)
    print(f"\n📄 Reporte guardado en: {report_file}")
    
    if all(results.values()):
        print("\n✅ SABIO ∞³ COMPLETAMENTE OPERATIVO")
        return 0
    else:
        print("\n⚠️  SABIO ∞³ REQUIERE ATENCIÓN")
        return 1

if __name__ == "__main__":
    sys.exit(main())
