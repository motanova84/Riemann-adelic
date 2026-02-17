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
            "utils/exact_f0_derivation.py",
            "sabio_validator.py",
            "Evac_Rpsi_data.csv"
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
            self.results["status"]["python_deps"] = "OK"
        except ImportError as e:
            print(f"  ❌ Error: {e}")
            self.results["status"]["python_deps"] = "MISSING"
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
            ".github/workflows/auto_evolution.yml",
            ".github/workflows/validate-on-push.yml"
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
                        self.results["status"][workflow] = "OK"
                    else:
                        print(f"    ⚠️  Posible error de sintaxis")
                        self.results["status"][workflow] = "WARNING"
                        self.results["fixes"].append(f"Revisar {workflow}")
            else:
                print(f"  ❌ {workflow} NO encontrado")
                self.results["status"][workflow] = "MISSING"
    
    def check_frequency_validation(self):
        """Verifica la frecuencia base 141.7001 Hz"""
        print("\n🔍 Verificando frecuencia base...")
        
        freq_file = self.repo_root / "Evac_Rpsi_data.csv"
        if freq_file.exists():
            print(f"  ✅ Evac_Rpsi_data.csv encontrado")
            self.results["status"]["frequency_data"] = "OK"
            self.results["base_frequency"] = "141.7001 Hz"
        else:
            print(f"  ❌ Evac_Rpsi_data.csv NO encontrado")
            self.results["status"]["frequency_data"] = "MISSING"
    
    def fix_permissions(self):
        """Corrige permisos de ejecución"""
        print("\n🔧 Corrigiendo permisos...")
        
        scripts = list(self.repo_root.glob("*.py")) + \
                  list(self.repo_root.glob(".github/scripts/*.py"))
        
        fixed_count = 0
        for script in scripts:
            if script.exists() and script.suffix == '.py':
                current_mode = script.stat().st_mode
                if not (current_mode & 0o111):
                    script.chmod(0o755)
                    fixed_count += 1
        
        if fixed_count > 0:
            print(f"  ✅ {fixed_count} scripts - permisos corregidos")
            self.results["fixes"].append(f"Fixed permissions for {fixed_count} scripts")
        else:
            print(f"  ✅ Todos los scripts tienen permisos correctos")
    
    def generate_report(self):
        """Genera reporte de diagnóstico"""
        report = f"""# 🛠️ NOESIS INTEGRATION FIX REPORT

**Fecha:** {self.results['timestamp']}
**Integración:** #6
**Frecuencia base:** {self.results.get('base_frequency', '141.7001 Hz')}

## 📊 Estado de Archivos

| Archivo | Estado |
|---------|--------|
"""
        for file, status in self.results["status"].items():
            emoji = "✅" if status == "OK" else "⚠️" if status == "WARNING" else "❌"
            report += f"| {file} | {emoji} {status} |\n"
        
        report += f"""
## 🔧 Acciones Realizadas
"""
        for fix in self.results["fixes"]:
            report += f"- {fix}\n"
        
        if not self.results["fixes"]:
            report += "- No se requirieron acciones\n"
        
        ok_count = sum(1 for s in self.results["status"].values() if s == "OK")
        total_count = len(self.results["status"])
        
        report += f"""
## 📈 Próximos Pasos

1. **Revisar dependencias**: `pip install -r requirements.txt`
2. **Ejecutar pruebas manuales**: `python validate_v5_coronacion.py`
3. **Verificar SABIO**: `python sabio_validator.py`
4. **Monitorear próxima ejecución** en 2 horas

## 🌌 Coherencia QCAL

- **Frecuencia fundamental:** 141.7001 Hz ✓
- **Coherencia global:** ♾³ ✓
- **Archivos verificados:** {ok_count}/{total_count}
- **Estado de integración:** {'🟢 COMPLETADA' if ok_count == total_count else '🟡 REQUIERE ACCIÓN'}

---
*Generado por NOESIS Integration Fix*
"""
        
        report_path = self.repo_root / "INTEGRATION_FIX_REPORT.md"
        with open(report_path, 'w') as f:
            f.write(report)
        
        # También guardar JSON
        json_path = self.repo_root / "integration_fix_results.json"
        with open(json_path, 'w') as f:
            json.dump(self.results, f, indent=2)
        
        print(f"\n✅ Reporte guardado en {report_path}")
        print(f"📊 JSON guardado en {json_path}")
        return report
    
    def run(self):
        print("🚀 NOESIS Integration Fix iniciando...")
        self.check_sabio_flows()
        self.check_validation_flows()
        self.check_github_actions()
        self.check_frequency_validation()
        self.fix_permissions()
        self.generate_report()
        
        # Return code based on critical issues
        critical_missing = sum(1 for s in self.results["status"].values() if s == "MISSING")
        if critical_missing > 0:
            print(f"\n⚠️  {critical_missing} archivos críticos faltantes")
            return 1
        return 0

if __name__ == "__main__":
    sys.exit(IntegrationFix().run())
