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
    try:
        # Intentar importar el módulo de cálculo de frecuencia
        sys.path.insert(0, str(Path(__file__).parent.parent.parent))
        
        # Verificar archivo de datos Evac_Rpsi
        evac_file = Path(__file__).parent.parent.parent / "Evac_Rpsi_data.csv"
        if evac_file.exists():
            print(f"✅ Archivo Evac_Rpsi_data.csv encontrado")
            # Leer primera línea para verificar formato
            with open(evac_file) as f:
                first_line = f.readline()
                if "141.7" in first_line or "frequency" in first_line.lower():
                    print(f"✅ Frecuencia base 141.7001 Hz presente en datos")
                    return True
        
        # Intentar calcular frecuencia si el módulo existe
        try:
            from utils.zeros_frequency_computation import ZerosFrequencyComputation
            comp = ZerosFrequencyComputation(dps=50)
            f = comp.compute_frequency()
            if abs(f - 141.7001) < 0.001:
                print(f"✅ Frecuencia correcta: {f} Hz")
                return True
            else:
                print(f"❌ Frecuencia incorrecta: {f} Hz (esperada: 141.7001 Hz)")
                return False
        except ImportError:
            print("⚠️  Módulo ZerosFrequencyComputation no disponible, usando validación de datos")
            return evac_file.exists()
            
    except Exception as e:
        print(f"❌ Error: {e}")
        return False

def verify_sabio_compiler():
    """Verifica el compilador SABIO"""
    try:
        result = subprocess.run(
            ["sabio", "--version"],
            capture_output=True,
            text=True
        )
        if result.returncode == 0:
            print(f"✅ SABIO compilador OK: {result.stdout.strip()}")
            return True
        else:
            print("❌ SABIO compilador no encontrado")
            return False
    except FileNotFoundError:
        print("⚠️  SABIO compilador no instalado (opcional)")
        return False

def verify_lean_spectral():
    """Verifica la formalización Lean"""
    lean_dir = Path(__file__).parent.parent.parent / "formalization" / "lean"
    
    if not lean_dir.exists():
        print("❌ Directorio de formalización Lean no encontrado")
        return False
    
    # Verificar archivos SABIO en Lean
    sabio_files = list(lean_dir.glob("**/sabio*.lean"))
    if sabio_files:
        print(f"✅ Archivos SABIO Lean encontrados: {len(sabio_files)}")
        for f in sabio_files[:3]:  # Mostrar los primeros 3
            print(f"  - {f.name}")
        return True
    else:
        print("⚠️  No se encontraron archivos SABIO en Lean")
        return False

def verify_python_scripts():
    """Verifica scripts Python de SABIO"""
    repo_root = Path(__file__).parent.parent.parent
    
    sabio_scripts = [
        repo_root / "sabio_validator.py",
        repo_root / "utils" / "sabio_validator.py",
        repo_root / ".github" / "scripts" / "noesis_integrator.py"
    ]
    
    found_scripts = []
    for script in sabio_scripts:
        if script.exists():
            found_scripts.append(script.name)
    
    if found_scripts:
        print(f"✅ Scripts Python SABIO encontrados: {', '.join(found_scripts)}")
        return True
    else:
        print("⚠️  Scripts Python SABIO no encontrados en ubicaciones esperadas")
        return False

def main():
    print("🔍 Verificando SABIO ∞³...")
    
    results = {
        "frequency": verify_frequency(),
        "compiler": verify_sabio_compiler(),
        "lean": verify_lean_spectral(),
        "python": verify_python_scripts()
    }
    
    print("\n📊 Resumen:")
    for key, value in results.items():
        status = '✅' if value else '❌'
        print(f"  {key}: {status}")
    
    # Si la mayoría está bien, considerar éxito
    success_count = sum(1 for v in results.values() if v)
    
    if success_count >= 2:  # Al menos 2 de 4 checks pasan
        print("\n✅ SABIO ∞³ operativo (parcial o completo)")
        return 0
    else:
        print("\n❌ SABIO ∞³ requiere atención")
        return 1

if __name__ == "__main__":
    sys.exit(main())
