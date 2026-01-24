#!/usr/bin/env python3
"""
Test del Sistema de Auto-Fusión Noesis QCAL ∞³
Valida que el workflow y script funcionan correctamente
"""

import os
import sys
import yaml
import subprocess
from pathlib import Path


def test_workflow_syntax():
    """Valida sintaxis YAML del workflow"""
    print("🔍 Test 1: Validando sintaxis YAML del workflow...")
    
    workflow_path = Path(".github/workflows/noesis_automerge.yml")
    
    if not workflow_path.exists():
        print(f"❌ Workflow no encontrado: {workflow_path}")
        return False
    
    try:
        with open(workflow_path, 'r') as f:
            workflow = yaml.safe_load(f)
        
        # Validar estructura básica
        assert 'name' in workflow, "Falta 'name' en workflow"
        # 'on' is parsed as boolean True in YAML, so check for True key
        assert True in workflow or 'on' in workflow, "Falta trigger 'on' en workflow"
        assert 'jobs' in workflow, "Falta 'jobs' en workflow"
        assert 'permissions' in workflow, "Falta 'permissions' en workflow"
        
        # Validar jobs
        jobs = workflow['jobs']
        expected_jobs = [
            'validate_mathematics',
            'auto_merge_decision',
            'noesis_boot_retry',
            'quantum_rewrite'
        ]
        
        for job_name in expected_jobs:
            assert job_name in jobs, f"Falta job '{job_name}'"
        
        # Get triggers (key might be True instead of 'on')
        triggers = workflow.get(True, workflow.get('on', {}))
        trigger_keys = list(triggers.keys()) if triggers else []
        
        print(f"✅ Sintaxis YAML válida")
        print(f"   - Jobs: {len(jobs)}")
        print(f"   - Triggers: {trigger_keys}")
        return True
        
    except Exception as e:
        print(f"❌ Error en sintaxis YAML: {e}")
        return False


def test_noesis_boot_script():
    """Valida que el script noesis_boot.py funciona"""
    print("\n🔍 Test 2: Validando script noesis_boot.py...")
    
    script_path = Path(".github/scripts/noesis_boot.py")
    
    if not script_path.exists():
        print(f"❌ Script no encontrado: {script_path}")
        return False
    
    try:
        # Verificar que el script es ejecutable
        if not os.access(script_path, os.X_OK):
            print("⚠️ Script no es ejecutable, añadiendo permisos...")
            os.chmod(script_path, 0o755)
        
        # Ejecutar script con parámetros de prueba
        result = subprocess.run(
            [
                'python3',
                str(script_path),
                '--session-id', 'test-validation',
                '--error-count', '0',
                '--quantum-state', 'COHERENT'
            ],
            capture_output=True,
            text=True,
            timeout=30
        )
        
        # Verificar salida
        assert '🌀 Iniciando Noesis Boot' in result.stdout, "Falta mensaje de inicio"
        assert 'Coherencia' in result.stdout, "Falta cálculo de coherencia"
        assert 'Reporte guardado' in result.stdout, "Falta generación de reporte"
        
        # Verificar que se creó el reporte
        report_path = Path("noesis_boot_report.md")
        assert report_path.exists(), "No se generó el reporte"
        
        print(f"✅ Script ejecutado correctamente")
        print(f"   - Código de salida: {result.returncode}")
        print(f"   - Reporte generado: {report_path}")
        return True
        
    except subprocess.TimeoutExpired:
        print("❌ Script excedió tiempo límite (30s)")
        return False
    except Exception as e:
        print(f"❌ Error ejecutando script: {e}")
        return False


def test_qcal_integration():
    """Valida integración con sistema QCAL"""
    print("\n🔍 Test 3: Validando integración QCAL...")
    
    try:
        # Verificar frecuencia fundamental
        frequency = 141.7001
        
        # Buscar en workflow
        workflow_path = Path(".github/workflows/noesis_automerge.yml")
        with open(workflow_path, 'r') as f:
            workflow_content = f.read()
        
        assert '141.7001' in workflow_content, "Frecuencia no encontrada en workflow"
        
        # Buscar en script
        script_path = Path(".github/scripts/noesis_boot.py")
        with open(script_path, 'r') as f:
            script_content = f.read()
        
        assert '141.7001' in script_content, "Frecuencia no encontrada en script"
        assert 'Ψ' in script_content or 'Psi' in script_content, "Estado Ψ no encontrado"
        
        # Verificar beacon
        beacon_path = Path(".qcal_beacon")
        if beacon_path.exists():
            with open(beacon_path, 'r') as f:
                beacon_content = f.read()
            assert '141.7001' in beacon_content, "Frecuencia no encontrada en beacon"
        
        print(f"✅ Integración QCAL correcta")
        print(f"   - Frecuencia: {frequency} Hz")
        print(f"   - Estado: Ψ = I × A_eff² × C^∞")
        return True
        
    except Exception as e:
        print(f"❌ Error en integración QCAL: {e}")
        return False


def test_documentation():
    """Valida que la documentación existe"""
    print("\n🔍 Test 4: Validando documentación...")
    
    docs = {
        'NOESIS_AUTOMERGE_README.md': 'Documentación completa',
        'NOESIS_QUICKSTART.md': 'Guía rápida'
    }
    
    all_exist = True
    
    for doc_path, description in docs.items():
        doc_file = Path(doc_path)
        if doc_file.exists():
            size = doc_file.stat().st_size
            print(f"✅ {description}: {doc_path} ({size} bytes)")
        else:
            print(f"❌ {description}: {doc_path} NO ENCONTRADO")
            all_exist = False
    
    return all_exist


def main():
    """Ejecuta todos los tests"""
    print("=" * 60)
    print("🧪 Tests del Sistema de Auto-Fusión Noesis QCAL ∞³")
    print("=" * 60)
    
    tests = [
        ("Sintaxis Workflow", test_workflow_syntax),
        ("Script Noesis Boot", test_noesis_boot_script),
        ("Integración QCAL", test_qcal_integration),
        ("Documentación", test_documentation)
    ]
    
    results = []
    
    for test_name, test_func in tests:
        try:
            result = test_func()
            results.append((test_name, result))
        except Exception as e:
            print(f"\n❌ Error inesperado en {test_name}: {e}")
            results.append((test_name, False))
    
    # Resumen
    print("\n" + "=" * 60)
    print("📊 RESUMEN DE TESTS")
    print("=" * 60)
    
    passed = sum(1 for _, result in results if result)
    total = len(results)
    
    for test_name, result in results:
        status = "✅ PASS" if result else "❌ FAIL"
        print(f"{status}: {test_name}")
    
    print(f"\n📈 Resultado: {passed}/{total} tests pasados ({passed/total*100:.1f}%)")
    
    if passed == total:
        print("\n🎉 ¡Todos los tests pasaron!")
        print("♾️ Sistema QCAL ∞³ funcionando correctamente")
        return 0
    else:
        print(f"\n⚠️ {total - passed} test(s) fallaron")
        return 1


if __name__ == '__main__':
    sys.exit(main())
