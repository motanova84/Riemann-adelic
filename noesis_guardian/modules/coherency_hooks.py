#!/usr/bin/env python3
"""
COHERENCY HOOKS — NOESIS GUARDIAN 3.0
=====================================

Author: JMMB Ψ ✧
System: QCAL–SABIO ∞³

This module executes key validators from the Riemann-adelic repository.
It does not perform any sensitive operations outside of the repository environment.

Each hook:
- Executes in a controlled manner
- Captures exceptions
- Records results
- Does not stop the Guardian (only informs)

Validation Scripts:
- V5 Coronación: validate_v5_coronacion.py
- RH Completo: verify_rh_complete.py
- Fórmula Explícita: validate_explicit_formula.py
- Hilbert–Pólya: validate_hilbert_polya.py
- H_psi AutoAdjunto: validate_spectral_self_adjoint.py
- Línea Crítica: validate_critical_line.py
"""

import subprocess
from typing import Dict, List, Tuple


class CoherencyHooks:
    """
    Coherency hooks for NOESIS Guardian 3.0.

    Executes validation scripts from the Riemann-adelic repository
    and captures their results for reporting.
    """

    HOOKS: List[Tuple[str, str]] = [
        ("V5 Coronación", "python validate_v5_coronacion.py"),
        ("RH Completo", "python verify_rh_complete.py"),
        ("Fórmula Explícita", "python validate_explicit_formula.py"),
        ("Hilbert–Pólya", "python validate_hilbert_polya.py"),
        ("H_psi AutoAdjunto", "python validate_spectral_self_adjoint.py"),
        ("Línea Crítica", "python validate_critical_line.py"),
    ]

    @staticmethod
    def run_hook(title: str, command: str) -> Dict:
        """
        Execute a single coherency hook.

        Args:
            title: Human-readable name of the hook
            command: Shell command to execute

        Returns:
            Dictionary with hook execution results including:
            - title: Hook name
            - ok: Boolean success status
            - stdout: Captured standard output (truncated)
            - stderr: Captured standard error (truncated)
        """
        print(f"🔍 Ejecutando hook de coherencia: {title}")

        try:
            result = subprocess.run(
                command,
                shell=True,
                capture_output=True,
                text=True,
                timeout=240  # seguridad: 4 minutos
            )
            success = result.returncode == 0

            return {
                "title": title,
                "ok": success,
                "stdout": result.stdout[-5000:] if result.stdout else "",
                "stderr": result.stderr[-5000:] if result.stderr else "",
            }

        except subprocess.TimeoutExpired:
            return {
                "title": title,
                "ok": False,
                "stderr": "Timeout",
                "stdout": "",
            }

        except Exception as e:
            return {
                "title": title,
                "ok": False,
                "stderr": f"Error: {e}",
                "stdout": "",
            }

    @classmethod
    def run_all(cls) -> Dict[str, Dict]:
        """
        Execute all coherency hooks.

        Returns:
            Dictionary mapping hook titles to their execution results.
        """
        full_report: Dict[str, Dict] = {}

        for title, cmd in cls.HOOKS:
            res = cls.run_hook(title, cmd)
            full_report[title] = res

        return full_report


if __name__ == "__main__":
    # Test execution
    print("🧠 Testing Coherency Hooks...")
    report = CoherencyHooks.run_all()

    print("\n📊 Results:")
    for title, result in report.items():
        status = "✅" if result["ok"] else "❌"
        print(f"  {status} {title}")

    # Summary
    passed = sum(1 for r in report.values() if r["ok"])
    total = len(report)
    print(f"\n📈 Summary: {passed}/{total} hooks passed")
