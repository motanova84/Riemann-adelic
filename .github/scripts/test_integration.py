#!/usr/bin/env python3
"""
🧪 TEST_INTEGRATION - Pruebas de integración para expansión del sistema
"""

import sys
import subprocess
import json
from pathlib import Path
from datetime import datetime

def run_command(cmd, description):
    """Ejecuta comando y maneja resultado"""
    print(f"🧪 {description}...")
    try:
        result = subprocess.run(
            cmd,
            shell=True,
            capture_output=True,
            text=True,
            timeout=30
        )
        
        if result.returncode == 0:
            print(f"✅ {description}: OK")
            return True, result.stdout
        else:
            print(f"❌ {description}: FAILED")
            print(f"   Error: {result.stderr[:200]}")
            return False, result.stderr
    except subprocess.TimeoutExpired:
        print(f"⏰ {description}: TIMEOUT")
        return False, "Timeout"
    except Exception as e:
        print(f"💥 {description}: ERROR - {str(e)}")
        return False, str(e)

def test_agents():
    """Prueba los nuevos agentes especializados"""
    print("\n" + "="*60)
    print("🤖 PRUEBAS DE AGENTES ESPECIALIZADOS")
    print("="*60)
    
    tests = [
        # QCAL Prover
        ("python .github/agents/specialized/qcal_prover.py --help", 
         "QCAL Prover - Ayuda"),
        
        ("python .github/agents/specialized/qcal_prover.py --repo . --frequency=141.7001 --output=/tmp/test_qcal_prover.json",
         "QCAL Prover - Validación básica"),
        
        # Axiom Emitter
        ("python .github/agents/specialized/axiom_emitter.py --help",
         "Axiom Emitter - Ayuda"),
         
        ("python .github/agents/specialized/axiom_emitter.py --repo . --frequency=141.7001",
         "Axiom Emitter - Generación básica"),
        
        # Code Synthesizer
        ("python .github/agents/specialized/code_synthesizer.py --help",
         "Code Synthesizer - Ayuda"),
         
        ("python .github/agents/specialized/code_synthesizer.py --repo . --frequency=141.7001",
         "Code Synthesizer - Síntesis básica"),
    ]
    
    results = []
    for cmd, desc in tests:
        success, output = run_command(cmd, desc)
        results.append((desc, success, output))
    
    return all(success for _, success, _ in results), results

def test_dashboard():
    """Prueba el dashboard web"""
    print("\n" + "="*60)
    print("🌐 PRUEBAS DEL DASHBOARD WEB")
    print("="*60)
    
    tests = [
        # Verificar archivos del dashboard
        ("ls -la dashboard/", "Dashboard - Estructura de archivos"),
        ("test -f dashboard/app.py", "Dashboard - App principal"),
        ("test -f dashboard/templates/index.html", "Dashboard - Template HTML"),
        ("test -f dashboard/static/dashboard.js", "Dashboard - JavaScript"),
        ("test -f dashboard/requirements.txt", "Dashboard - Dependencias"),
        
        # Verificar contenido
        ("python3 -c \"import flask\" 2>/dev/null && echo 'Flask disponible' || echo 'Flask no disponible'",
         "Dashboard - Dependencias de Python"),
    ]
    
    results = []
    for cmd, desc in tests:
        success, output = run_command(cmd, desc)
        results.append((desc, success, output))
    
    return all(success for _, success, _ in results), results

def test_notifications():
    """Prueba el sistema de notificaciones"""
    print("\n" + "="*60)
    print("🔔 PRUEBAS DEL SISTEMA DE NOTIFICACIONES")
    print("="*60)
    
    tests = [
        # Verificar archivos de notificaciones
        ("ls -la .github/scripts/notifications/", "Notificaciones - Estructura"),
        ("test -f .github/scripts/notifications/discord_notifier.py", "Discord Notifier"),
        ("test -f .github/scripts/notifications/slack_notifier.py", "Slack Notifier"),
        ("test -f .github/scripts/notifications/notification_manager.py", "Notification Manager"),
        
        # Pruebas de ayuda
        ("python .github/scripts/notifications/notification_manager.py --help",
         "Notification Manager - Ayuda"),
    ]
    
    results = []
    for cmd, desc in tests:
        success, output = run_command(cmd, desc)
        results.append((desc, success, output))
    
    return all(success for _, success, _ in results), results

def test_lean_analysis():
    """Prueba análisis Lean expandido"""
    print("\n" + "="*60)
    print("📚 PRUEBAS DE ANÁLISIS LEAN EXPANDIDO")
    print("="*60)
    
    tests = [
        # Verificar archivos de análisis Lean
        ("ls -la .github/scripts/lean/", "Lean Analysis - Estructura"),
        ("test -f .github/scripts/lean/lean_dependency_analyzer.py", "Lean Dependency Analyzer"),
        ("test -f .github/scripts/lean/requirements.txt", "Lean Analysis - Dependencias"),
        
        # Pruebas de ayuda
        ("python .github/scripts/lean/lean_dependency_analyzer.py --help",
         "Lean Dependency Analyzer - Ayuda"),
    ]
    
    results = []
    for cmd, desc in tests:
        success, output = run_command(cmd, desc)
        results.append((desc, success, output))
    
    return all(success for _, success, _ in results), results

def verify_file_creation():
    """Verifica que se hayan creado los archivos correctamente"""
    print("\n" + "="*60)
    print("📁 VERIFICACIÓN DE ARCHIVOS CREADOS")
    print("="*60)
    
    expected_files = [
        # Agentes especializados
        ".github/agents/specialized/qcal_prover.py",
        ".github/agents/specialized/axiom_emitter.py", 
        ".github/agents/specialized/code_synthesizer.py",
        
        # Dashboard
        "dashboard/app.py",
        "dashboard/templates/index.html",
        "dashboard/static/dashboard.js",
        "dashboard/requirements.txt",
        
        # Notificaciones
        ".github/scripts/notifications/discord_notifier.py",
        ".github/scripts/notifications/slack_notifier.py",
        ".github/scripts/notifications/notification_manager.py",
        
        # Análisis Lean
        ".github/scripts/lean/lean_dependency_analyzer.py",
        ".github/scripts/lean/requirements.txt",
    ]
    
    results = []
    for file_path in expected_files:
        path = Path(file_path)
        exists = path.exists()
        results.append((file_path, exists))
        
        if exists:
            print(f"✅ {file_path}: OK")
        else:
            print(f"❌ {file_path}: NO EXISTE")
    
    return all(exists for _, exists in results), results

def generate_report(all_results):
    """Genera reporte de pruebas"""
    print("\n" + "="*60)
    print("📋 REPORTE DE PRUEBAS DE INTEGRACIÓN")
    print("="*60)
    
    report = {
        "timestamp": datetime.utcnow().isoformat(),
        "system": "QCAL ∞³ Expansion Integration Tests",
        "frequency": 141.7001,
        "tests": {}
    }
    
    # Ejecutar todas las categorías
    categories = [
        ("file_creation", verify_file_creation),
        ("agents", test_agents),
        ("dashboard", test_dashboard),
        ("notifications", test_notifications),
        ("lean_analysis", test_lean_analysis),
    ]
    
    overall_success = True
    
    for category_name, test_func in categories:
        print(f"\n📊 {category_name.upper()}:")
        
        success, results = test_func()
        
        # Handle different result formats
        if category_name == "file_creation":
            total_tests = len(results)
            passed = sum(1 for _, s in results if s)
        else:
            total_tests = len(results)
            passed = sum(1 for _, s, _ in results if s)
        
        report["tests"][category_name] = {
            "success": success,
            "total_tests": total_tests,
            "passed": passed,
        }
        
        if not success:
            overall_success = False
        
        status = "✅ PASS" if success else "❌ FAIL"
        print(f"   Resultado: {status}")
    
    # Mostrar resumen
    print("\n" + "="*60)
    print("🎯 RESUMEN GENERAL")
    print("="*60)
    
    total_tests = sum(cat["total_tests"] for cat in report["tests"].values())
    total_passed = sum(cat["passed"] for cat in report["tests"].values())
    
    print(f"📊 Total pruebas: {total_tests}")
    print(f"✅ Pruebas pasadas: {total_passed}")
    print(f"❌ Pruebas falladas: {total_tests - total_passed}")
    print(f"📈 Porcentaje de éxito: {(total_passed/total_tests*100):.1f}%")
    
    if overall_success:
        print("\n🎉 ¡TODAS LAS PRUEBAS DE INTEGRACIÓN PASARON!")
        print("🚀 Sistema de expansión implementado exitosamente")
    else:
        print("\n⚠️  Algunas pruebas fallaron. Revisar detalles arriba.")
    
    # Guardar reporte
    report_file = "integration_test_report.json"
    with open(report_file, 'w', encoding='utf-8') as f:
        json.dump(report, f, indent=2, ensure_ascii=False)
    
    print(f"\n📄 Reporte guardado: {report_file}")
    
    return overall_success

def main():
    """Función principal"""
    print("🧪 INICIANDO PRUEBAS DE INTEGRACIÓN - EXPANSIÓN QCAL ∞³")
    print("="*60)
    print(f"📅 Fecha: {datetime.utcnow().strftime('%Y-%m-%d %H:%M UTC')}")
    print(f"📡 Frecuencia: 141.7001 Hz")
    print("="*60)
    
    # Ejecutar todas las pruebas
    success = generate_report(None)
    
    # Mostrar instrucciones de uso
    print("\n" + "="*60)
    print("🚀 INSTRUCCIONES DE USO - SISTEMA EXPANDIDO")
    print("="*60)
    
    instructions = """
📋 COMPONENTES IMPLEMENTADOS:

1. 🤖 AGENTES ESPECIALIZADOS:
   • QCAL Prover: python .github/agents/specialized/qcal_prover.py
   • Axiom Emitter: python .github/agents/specialized/axiom_emitter.py  
   • Code Synthesizer: python .github/agents/specialized/code_synthesizer.py

2. 🌐 DASHBOARD WEB:
   • Instalar dependencias: pip install -r dashboard/requirements.txt
   • Ejecutar: python dashboard/app.py
   • Acceder: http://localhost:5000

3. 🔔 SISTEMA DE NOTIFICACIONES:
   • Configurar webhooks en variables de entorno:
     - DISCORD_WEBHOOK_URL
     - SLACK_WEBHOOK_URL
   • Usar: python .github/scripts/notifications/notification_manager.py

4. 📚 ANÁLISIS LEAN EXPANDIDO:
   • Instalar dependencias: pip install -r .github/scripts/lean/requirements.txt
   • Ejecutar: python .github/scripts/lean/lean_dependency_analyzer.py

🎯 PRÓXIMOS PASOS:
1. Configurar webhooks para notificaciones
2. Ejecutar dashboard para monitoreo en tiempo real
3. Ejecutar análisis Lean para optimización
4. Integrar agentes en workflow principal

📈 SISTEMA EXPANDIDO LISTO PARA:
• Monitoreo visual en tiempo real
• Notificaciones automáticas
• Análisis profundo de dependencias
• Validación matemática formal
• Generación automática de código
"""
    
    print(instructions)
    
    # Salir con código apropiado
    sys.exit(0 if success else 1)

if __name__ == "__main__":
    main()
