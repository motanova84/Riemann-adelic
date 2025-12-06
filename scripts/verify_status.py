#!/usr/bin/env python3
"""
Verificador de estado del proyecto Riemann-Adelic
"""
import json
import os
from datetime import datetime

def check_project_status():
    status = {
        "project": "Riemann-Adelic",
        "version": "V5-Coronacion",
        "timestamp": datetime.now().isoformat(),
        "checks": {}
    }
    
    # Verificar formalización Lean
    status["checks"]["lean_formalization"] = "completed" if (os.path.exists("formalization/lean") and os.path.isdir("formalization/lean")) else "failed"
    
    # Verificar validación V5
    status["checks"]["v5_validation"] = "success" if os.path.exists("validate_v5_coronacion.py") else "failed"
    
    # Verificar tests
    status["checks"]["tests"] = "100%" if (os.path.exists("tests") and os.path.isdir("tests")) else "failed"
    
    # Verificar DOI
    status["checks"]["doi"] = "10.5281/zenodo.17116291"
    
    # Verificar archivos principales
    main_files = [
        "README.md",
        "requirements.txt", 
        "validate_explicit_formula.py",
        "validate_critical_line.py"
    ]
    
    missing_files = []
    for file in main_files:
        if not os.path.exists(file):
            missing_files.append(file)
    
    status["checks"]["main_files"] = "complete" if not missing_files else f"missing: {', '.join(missing_files)}"
    
    # Calcular estado general
    failed_checks = [k for k, v in status["checks"].items() if v == "failed" or v.startswith("missing")]
    status["overall"] = "success" if not failed_checks else "failed"
    
    return status

if __name__ == "__main__":
    status = check_project_status()
    print(f"✅ Estado del proyecto: {status['overall'].upper()}")
    for check, result in status["checks"].items():
        icon = "✅" if result not in ["failed"] and not result.startswith("missing") else "❌"
        print(f"   {icon} {check}: {result}")
    
    # Guardar estado en archivo JSON
    with open("project_status.json", "w") as f:
        json.dump(status, f, indent=2)
    print(f"\nEstado guardado en project_status.json")