#!/usr/bin/env python3
"""
🧪 TEST ORCHESTRATION - Prueba del Sistema de Orquestación QCAL ∞³
Verifica que todos los componentes funcionen correctamente
"""

import subprocess
import sys
from pathlib import Path
from datetime import datetime


class OrchestrationTester:
    """Probador del sistema de orquestación"""
    
    def __init__(self):
        self.root_path = Path.cwd()
        self.results = {
            "timestamp": datetime.now().isoformat(),
            "tests": {},
            "passed": 0,
            "failed": 0
        }
    
    def test_agent_exists(self, agent_name):
        """Verifica que un agente existe"""
        agent_path = self.root_path / ".github" / "agents" / agent_name
        exists = agent_path.exists()
        
        self.results["tests"][f"agent_{agent_name}_exists"] = exists
        if exists:
            self.results["passed"] += 1
            print(f"  ✅ Agente {agent_name} encontrado")
        else:
            self.results["failed"] += 1
            print(f"  ❌ Agente {agent_name} no encontrado")
        
        return exists
    
    def test_agent_executable(self, agent_name):
        """Verifica que un agente sea ejecutable"""
        try:
            result = subprocess.run(
                [sys.executable, f".github/agents/{agent_name}", "--help"],
                capture_output=True,
                timeout=5,
                cwd=self.root_path
            )
            success = result.returncode == 0
            
            self.results["tests"][f"agent_{agent_name}_executable"] = success
            if success:
                self.results["passed"] += 1
                print(f"  ✅ Agente {agent_name} ejecutable")
            else:
                self.results["failed"] += 1
                print(f"  ❌ Agente {agent_name} no ejecutable")
            
            return success
        except Exception as e:
            self.results["tests"][f"agent_{agent_name}_executable"] = False
            self.results["failed"] += 1
            print(f"  ❌ Error ejecutando {agent_name}: {e}")
            return False
    
    def test_script_exists(self, script_name):
        """Verifica que un script existe"""
        script_path = self.root_path / ".github" / "scripts" / script_name
        exists = script_path.exists()
        
        self.results["tests"][f"script_{script_name}_exists"] = exists
        if exists:
            self.results["passed"] += 1
            print(f"  ✅ Script {script_name} encontrado")
        else:
            self.results["failed"] += 1
            print(f"  ❌ Script {script_name} no encontrado")
        
        return exists
    
    def test_workflow_exists(self, workflow_name):
        """Verifica que un workflow existe"""
        workflow_path = self.root_path / ".github" / "workflows" / workflow_name
        exists = workflow_path.exists()
        
        self.results["tests"][f"workflow_{workflow_name}_exists"] = exists
        if exists:
            self.results["passed"] += 1
            print(f"  ✅ Workflow {workflow_name} encontrado")
        else:
            self.results["failed"] += 1
            print(f"  ❌ Workflow {workflow_name} no encontrado")
        
        return exists
    
    def test_directory_exists(self, dir_name):
        """Verifica que un directorio existe"""
        dir_path = self.root_path / dir_name
        exists = dir_path.exists() and dir_path.is_dir()
        
        self.results["tests"][f"directory_{dir_name}_exists"] = exists
        if exists:
            self.results["passed"] += 1
            print(f"  ✅ Directorio {dir_name} encontrado")
        else:
            self.results["failed"] += 1
            print(f"  ❌ Directorio {dir_name} no encontrado")
        
        return exists
    
    def run_all_tests(self):
        """Ejecuta todas las pruebas"""
        print("🧪 TEST ORCHESTRATION - Iniciando pruebas...")
        print("=" * 60)
        print()
        
        # Test agentes
        print("🤖 Probando agentes...")
        self.test_agent_exists("noesis88.py")
        self.test_agent_executable("noesis88.py")
        self.test_agent_exists("metrics_collector.py")
        self.test_agent_executable("metrics_collector.py")
        self.test_agent_exists("coherence_validator.py")
        self.test_agent_executable("coherence_validator.py")
        print()
        
        # Test scripts
        print("📜 Probando scripts...")
        self.test_script_exists("analyze_and_adjust.sh")
        self.test_script_exists("optimize_qcal_density.sh")
        print()
        
        # Test workflows
        print("⚙️  Probando workflows...")
        self.test_workflow_exists("orchestrator.yaml")
        print()
        
        # Test directorios
        print("📁 Probando directorios...")
        self.test_directory_exists("reports")
        self.test_directory_exists("metrics")
        self.test_directory_exists("validation")
        self.test_directory_exists("src/constants")
        print()
        
        # Resumen
        print("=" * 60)
        print("📊 RESUMEN DE PRUEBAS")
        print("=" * 60)
        print(f"✅ Pruebas exitosas: {self.results['passed']}")
        print(f"❌ Pruebas fallidas: {self.results['failed']}")
        print(f"📊 Total: {self.results['passed'] + self.results['failed']}")
        print()
        
        if self.results['failed'] == 0:
            print("🎉 TODAS LAS PRUEBAS PASARON")
            print("✅ Sistema de orquestación QCAL ∞³ verificado")
            return 0
        else:
            print("⚠️  ALGUNAS PRUEBAS FALLARON")
            print(f"   Verificar {self.results['failed']} componente(s)")
            return 1


def main():
    """Función principal"""
    tester = OrchestrationTester()
    return tester.run_all_tests()


if __name__ == "__main__":
    sys.exit(main())
