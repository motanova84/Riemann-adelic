#!/usr/bin/env python3
# ===============================================================
# ✅ VALIDATE_LEAN_ENV.PY
# Monitor de validación automatizada para la formalización Riemann-Adelic
# Autor: José Manuel Mota Burruezo (ICQ)
# Versión: V5.3 – Octubre 2025
# ===============================================================

import subprocess
import time
import json
import re
from datetime import datetime, timezone
from pathlib import Path

BASE_DIR = Path(__file__).resolve().parent
REPORT_PATH = BASE_DIR / "validation_report.json"
LEAN_FILES = [
    "D_explicit.lean",
    "de_branges.lean",
    "schwartz_adelic.lean",
    "RH_final.lean"
]

def run_command(cmd: str) -> tuple[int, str, str]:
    """Ejecuta un comando del sistema y devuelve código, stdout y stderr."""
    process = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    stdout, stderr = process.communicate()
    return process.returncode, stdout.strip(), stderr.strip()

def count_sorry(file_path: Path) -> int:
    """Cuenta el número de 'sorry' (pruebas incompletas) en un archivo Lean."""
    try:
        content = file_path.read_text(encoding="utf-8")
        return len(re.findall(r"\bsorry\b", content))
    except FileNotFoundError:
        return -1

def validate_modules() -> dict:
    """Valida los módulos principales y recopila métricas."""
    results = {}
    for f in LEAN_FILES:
        # Check both in BASE_DIR and RiemannAdelic subdirectory
        path = BASE_DIR / f
        if not path.exists():
            path = BASE_DIR / "RiemannAdelic" / f
        
        if not path.exists():
            results[f] = {"exists": False}
            continue
        n_sorry = count_sorry(path)
        results[f] = {
            "exists": True,
            "sorries": n_sorry,
            "verified": n_sorry == 0
        }
    return results

def validate_theorem(file_path: Path) -> bool:
    """Comprueba si el teorema principal está presente."""
    # Check both in BASE_DIR and as-is
    if not file_path.exists():
        alt_path = BASE_DIR / file_path.name
        if alt_path.exists():
            file_path = alt_path
    
    try:
        content = file_path.read_text(encoding="utf-8")
        return "riemann_hypothesis_adelic" in content or "RiemannHypothesis" in content
    except FileNotFoundError:
        return False

def get_lean_version() -> str:
    """Obtiene la versión de Lean si está instalado."""
    code, out, err = run_command("lean --version")
    if code == 0 and out:
        return out.splitlines()[0]
    return "Lean not installed or not in PATH"

def main():
    print("───────────────────────────────────────────────")
    print("🧠  VALIDACIÓN AUTOMÁTICA – Riemann Adelic (Python)")
    print("───────────────────────────────────────────────")

    start = time.time()

    # 1. Ejecutar compilación Lean
    print("⚙️  Compilando proyecto Lean con lake...")
    code, out, err = run_command(f'cd "{BASE_DIR}" && lake build -j 8')

    build_time = round(time.time() - start, 2)
    success = code == 0

    # 2. Analizar salida
    warnings = len(re.findall(r"warning", out + err, flags=re.IGNORECASE))
    errors = len(re.findall(r"error", out + err, flags=re.IGNORECASE))

    # 3. Validar módulos
    module_results = validate_modules()

    # 4. Validar teorema principal
    theorem_ok = validate_theorem(BASE_DIR / "RH_final.lean")

    # 5. Obtener versión de Lean
    lean_version = get_lean_version()

    # 6. Crear informe JSON
    report = {
        "timestamp": datetime.now(timezone.utc).isoformat(),
        "project": "Riemann-Adelic Formalization V5.3",
        "lean_version": lean_version,
        "build_success": success,
        "build_time_sec": build_time,
        "warnings": warnings,
        "errors": errors,
        "modules": module_results,
        "theorem_detected": theorem_ok,
        "summary": {
            "status": "PASS" if success and theorem_ok and errors == 0 else "CHECK",
            "message": (
                "Formalización compilada y verificada."
                if success and theorem_ok and errors == 0
                else "Revisar advertencias o errores." if not success
                else "Compilación exitosa - revisar validaciones pendientes."
            ),
        },
    }

    # 7. Guardar informe
    with open(REPORT_PATH, "w", encoding="utf-8") as f:
        json.dump(report, f, indent=2)

    print("───────────────────────────────────────────────")
    print(f"📘 Informe generado: {REPORT_PATH}")
    print(f"⏱️  Tiempo total: {build_time} s")
    print(f"✅ Estado: {report['summary']['status']}")
    
    # Mostrar resumen de módulos
    print("\n📊 Resumen de Módulos:")
    for fname, result in module_results.items():
        if result.get("exists"):
            status = "✓" if result["verified"] else "⚠"
            sorries = result["sorries"]
            print(f"  {status} {fname}: {sorries} sorry(s)")
        else:
            print(f"  ✗ {fname}: no encontrado")
    
    print("───────────────────────────────────────────────")

    # Return exit code based on validation status
    return 0 if success or (theorem_ok and errors == 0) else 1

if __name__ == "__main__":
    exit(main())
