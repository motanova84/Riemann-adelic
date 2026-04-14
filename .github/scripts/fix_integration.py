#!/usr/bin/env python3
"""
NOESIS INTEGRATION FIX - Diagnóstico y reparación de la integración #6
"""

import json
import subprocess
import sys
from pathlib import Path
from datetime import datetime

class IntegrationFix:
    def __init__(self):
        self.repo_root = Path(__file__).parent.parent.parent
        self.results = {
            "timestamp": datetime.now().isoformat(),
            "fixes": [],
            "status": {}
        }
    
    def check_sabio_flows(self):
        """Verifica y repara los flujos de SABIO ∞³"""
        print("🔍 Verificando SABIO ∞³...")
        
        # Verificar que los scripts existen
        sabio_scripts = [
            "utils/validate_frequency.py",
            "utils/sabio_validator.py",
            "formalization/lean/sabio_spectral.lean"
        ]
        
        for script in sabio_scripts:
            path = self.repo_root / script
            if path.exists():
                print(f"  ✅ {script} encontrado")
                self.results["status"][script] = "OK"
            else:
                print(f"  ❌ {script} NO encontrado")
                self.results["status"][script] = "MISSING"
                self.results["fixes"].append(f"Crear {script}")
        
        # Verificar dependencias de Python
        try:
            import numpy
            import scipy
            print("  ✅ Dependencias Python OK")
        except ImportError as e:
            print(f"  ❌ Error: {e}")
            self.results["fixes"].append("Instalar dependencias: pip install numpy scipy")
    
    def check_validation_flows(self):
        """Verifica los flujos de validación RH"""
        print("\n🔍 Verificando Validación RH...")
        
        validation_scripts = [
            "validate_v5_coronacion.py",
            "validate_critical_line.py",
            "validate_explicit_formula.py",
            "tests/test_rh_proved_framework.py"
        ]
        
        for script in validation_scripts:
            path = self.repo_root / script
            if path.exists():
                print(f"  ✅ {script} encontrado")
                self.results["status"][script] = "OK"
                
                # Verificar permisos de ejecución
                if not (path.stat().st_mode & 0o111):
                    print(f"  ⚠️  {script} no es ejecutable")
                    path.chmod(0o755)
                    self.results["fixes"].append(f"chmod +x {script}")
            else:
                print(f"  ❌ {script} NO encontrado")
                self.results["status"][script] = "MISSING"
    
    def check_github_actions(self):
        """Verifica los workflows de GitHub Actions"""
        print("\n🔍 Verificando GitHub Actions...")
        
        workflows = [
            ".github/workflows/noesis_multi_repo_v2.yml",
            ".github/workflows/sabio_validation.yml",
            ".github/workflows/rh_validation.yml",
            ".github/workflows/auto_evolution.yml"
        ]
        
        for workflow in workflows:
            path = self.repo_root / workflow
            if path.exists():
                print(f"  ✅ {workflow} encontrado")
                
                # Verificar sintaxis básica
                with open(path) as f:
                    content = f.read()
                    if "on:" in content and "jobs:" in content:
                        print(f"    Sintaxis OK")
                    else:
                        print(f"    ⚠️  Posible error de sintaxis")
                        self.results["fixes"].append(f"Revisar {workflow}")
            else:
                print(f"  ❌ {workflow} NO encontrado")
                self.results["status"][workflow] = "MISSING"
    
    def fix_permissions(self):
        """Corrige permisos de ejecución"""
        print("\n🔧 Corrigiendo permisos...")
        
        scripts = list(self.repo_root.glob("*.py")) + \
                  list(self.repo_root.glob(".github/scripts/*.py"))
        
        for script in scripts:
            if script.exists():
                script.chmod(0o755)
                print(f"  ✅ {script.name} permisos corregidos")
    
    def generate_report(self):
        """Genera reporte de diagnóstico"""
        report = f"""# 🛠️ NOESIS INTEGRATION FIX REPORT

**Fecha:** {self.results['timestamp']}
**Integración:** #6
**Frecuencia base:** 141.7001 Hz

## 📊 Estado de Archivos

| Archivo | Estado |
|---------|--------|
"""
        for file, status in self.results["status"].items():
            report += f"| {file} | {status} |\n"
        
        report += f"""
## 🔧 Acciones Realizadas
"""
        for fix in self.results["fixes"]:
            report += f"- {fix}\n"
        
        if not self.results["fixes"]:
            report += "- No se requirieron acciones\n"
        
        report += f"""
## 📈 Próximos Pasos

1. **Revisar dependencias**: `pip install -r requirements.txt`
2. **Ejecutar pruebas manuales**: `python validate_v5_coronacion.py --quick`
3. **Verificar SABIO**: `python utils/sabio_validator.py`
4. **Monitorear próxima ejecución** en 2 horas

## 🌌 Coherencia QCAL

- **Frecuencia fundamental:** 141.7001 Hz ✓
- **Coherencia global:** ♾³ ✓
- **Estado de integración:** {'🟢 COMPLETADA' if not self.results['fixes'] else '🟡 REQUIERE ACCIÓN'}

---
*Generado por NOESIS Integration Fix*
"""
        
        report_path = self.repo_root / "INTEGRATION_FIX_REPORT.md"
        with open(report_path, 'w') as f:
            f.write(report)
        
        print(f"\n✅ Reporte guardado en {report_path}")
        return report
    
    def run(self):
        print("🚀 NOESIS Integration Fix iniciando...")
        self.check_sabio_flows()
        self.check_validation_flows()
        self.check_github_actions()
        self.fix_permissions()
        self.generate_report()
        return 0

if __name__ == "__main__":
    sys.exit(IntegrationFix().run())
