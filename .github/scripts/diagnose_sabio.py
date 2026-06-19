#!/usr/bin/env python3
"""
Diagnóstico rápido del problema SABIO ∞³
Verifica que todo el pipeline funciona correctamente
"""

import subprocess
import json
import sys
from pathlib import Path

def check_workflow_exists():
    """Verifica que los workflows relacionados con SABIO existen"""
    workflow_files = [
        ".github/workflows/sabio-symbiotic-ci.yml",
        ".github/workflows/sabio-symbiotic-matrix.yml",
        ".github/workflows/noesis_multi_repo_v2.yml"
    ]
    
    print("🔍 Verificando workflows...")
    found = []
    for wf in workflow_files:
        wf_path = Path(wf)
        if wf_path.exists():
            found.append(wf)
            print(f"  ✓ {wf}")
        else:
            print(f"  ✗ {wf} NO encontrado")
    
    return len(found) > 0

def check_verify_script():
    """Verifica que el script de verificación existe"""
    script_path = Path(".github/scripts/verify_sabio.py")
    if script_path.exists():
        print(f"✅ Script verify_sabio.py encontrado")
        return True
    else:
        print(f"❌ Script verify_sabio.py NO encontrado")
        return False

def check_integrator_script():
    """Verifica que el script integrador existe"""
    script_path = Path(".github/scripts/noesis_integrator.py")
    if script_path.exists():
        print(f"✅ Script noesis_integrator.py encontrado")
        return True
    else:
        print(f"❌ Script noesis_integrator.py NO encontrado")
        return False

def check_dependencies():
    """Verifica dependencias Python"""
    try:
        import numpy
        import scipy
        import sympy
        import mpmath
        print(f"✅ Dependencias Python OK")
        return True
    except ImportError as e:
        print(f"❌ Error dependencias: {e}")
        return False

def test_verify_script():
    """Prueba ejecución del script verify_sabio.py"""
    print("\n🧪 PROBANDO verify_sabio.py...")
    try:
        result = subprocess.run(
            [sys.executable, ".github/scripts/verify_sabio.py"],
            capture_output=True,
            text=True,
            timeout=60
        )
        
        if result.returncode == 0 or result.returncode == 1:  # 0 = success, 1 = partial
            print(f"✅ Script ejecutado (exit code: {result.returncode})")
            
            # Intentar parsear JSON
            try:
                data = json.loads(result.stdout)
                print(f"✅ Output es JSON válido")
                
                # Mostrar resumen
                if "overall" in data:
                    overall = data["overall"]
                    print(f"   Estado general: {overall.get('status', 'unknown')}")
                    print(f"   Mensaje: {overall.get('message', 'N/A')}")
                
                # Mostrar detalles de cada componente
                for component in ["frequency", "compiler", "lean", "python"]:
                    if component in data:
                        comp_data = data[component]
                        status = comp_data.get("status", "unknown")
                        msg = comp_data.get("message", "N/A")
                        print(f"   {component}: {status} - {msg}")
                
                return True
            except json.JSONDecodeError as e:
                print(f"❌ Output NO es JSON válido: {e}")
                print(f"   Output (primeros 500 chars): {result.stdout[:500]}")
                return False
        else:
            print(f"❌ Script falló con exit code: {result.returncode}")
            print(f"   stderr: {result.stderr[:200]}")
            return False
    except subprocess.TimeoutExpired:
        print(f"❌ Script timeout después de 60s")
        return False
    except Exception as e:
        print(f"❌ Error ejecutando script: {e}")
        return False

def test_integrator():
    """Prueba el integrador NOESIS con modo SABIO"""
    print("\n🧪 PROBANDO noesis_integrator.py --mode sabio...")
    try:
        result = subprocess.run(
            [sys.executable, ".github/scripts/noesis_integrator.py", "--mode", "sabio"],
            capture_output=True,
            text=True,
            timeout=120
        )
        
        if result.returncode == 0:
            print(f"✅ Integrador ejecutado correctamente")
            
            # Verificar si generó archivos de salida
            results_file = Path("noesis_integration_results.json")
            if results_file.exists():
                with open(results_file) as f:
                    data = json.load(f)
                    if "sabio" in data:
                        sabio_status = data["sabio"].get("overall", {}).get("status", "unknown")
                        print(f"   Estado SABIO en integrador: {sabio_status}")
                        return sabio_status != "unknown"
            
            return True
        else:
            print(f"⚠️ Integrador salió con código: {result.returncode}")
            print(f"   stderr: {result.stderr[:200]}")
            return False
    except subprocess.TimeoutExpired:
        print(f"❌ Integrador timeout después de 120s")
        return False
    except Exception as e:
        print(f"❌ Error ejecutando integrador: {e}")
        return False

def main():
    print("=" * 60)
    print("🔍 DIAGNÓSTICO SABIO ∞³")
    print("=" * 60)
    
    checks = {
        "workflows": check_workflow_exists(),
        "verify_script": check_verify_script(),
        "integrator_script": check_integrator_script(),
        "dependencies": check_dependencies(),
        "test_verify": test_verify_script(),
        "test_integrator": test_integrator()
    }
    
    print("\n" + "=" * 60)
    print("📊 RESUMEN")
    print("=" * 60)
    
    all_ok = True
    for name, ok in checks.items():
        status = "✅" if ok else "❌"
        print(f"{status} {name}")
        all_ok = all_ok and ok
    
    print("=" * 60)
    
    if all_ok:
        print("\n✅ TODO OK - SABIO debería funcionar correctamente")
        print("   El estado 'desconocido' debería desaparecer en próximas ejecuciones")
    else:
        print("\n❌ PROBLEMAS DETECTADOS")
        print("   Revisar logs arriba para más detalles")
    
    return 0 if all_ok else 1

if __name__ == "__main__":
    sys.exit(main())
