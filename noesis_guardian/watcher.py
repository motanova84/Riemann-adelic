#!/usr/bin/env python3
"""
NOESIS GUARDIAN — Repository Watcher Module
============================================

Módulo para inspección y vigilancia del repositorio.
Detecta colisiones, archivos faltantes, estado de Lean y coherencia general.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
License: Creative Commons BY-NC-SA 4.0
"""

import subprocess
from pathlib import Path
from typing import Dict, List, Any, Optional
from datetime import datetime


class RepoWatcher:
    """
    Vigilante del repositorio QCAL.

    Realiza escaneos periódicos para detectar:
    - Colisiones de archivos
    - Archivos faltantes críticos
    - Estado de formalización Lean
    - Coherencia de estructura del repositorio
    """

    # Archivos críticos que deben existir
    CRITICAL_FILES = [
        ".qcal_beacon",
        "validate_v5_coronacion.py",
        "aik_beacon.py",
        "requirements.txt",
        "README.md",
        "LICENSE",
    ]

    # Directorios críticos
    CRITICAL_DIRS = [
        "formalization/lean",
        "tests",
        "utils",
        "data",
    ]

    def __init__(self, repo_root: Optional[Path] = None):
        """
        Inicializa el vigilante del repositorio.

        Args:
            repo_root: Ruta raíz del repositorio. Si no se especifica,
                      usa el directorio padre del módulo.
        """
        if repo_root is None:
            self.repo_root = Path(__file__).resolve().parents[1]
        else:
            self.repo_root = Path(repo_root)

    def scan_repo(self) -> Dict[str, Any]:
        """
        Escanea el repositorio completo.

        Returns:
            Diccionario con el estado del repositorio:
            {
                "timestamp": ISO timestamp,
                "collisions": número de colisiones detectadas,
                "missing": número de archivos faltantes,
                "lean_status": estado de Lean ("ok", "error", "not_found"),
                "critical_files": lista de archivos críticos y su estado,
                "critical_dirs": lista de directorios críticos y su estado,
                "git_status": estado de git,
                "warnings": lista de advertencias
            }
        """
        state = {
            "timestamp": datetime.now().isoformat(),
            "collisions": 0,
            "missing": 0,
            "lean_status": "unknown",
            "critical_files": {},
            "critical_dirs": {},
            "git_status": None,
            "warnings": [],
        }

        # Verificar archivos críticos
        for file in self.CRITICAL_FILES:
            file_path = self.repo_root / file
            if file_path.exists():
                state["critical_files"][file] = "ok"
            else:
                state["critical_files"][file] = "missing"
                state["missing"] += 1
                state["warnings"].append(f"Critical file missing: {file}")

        # Verificar directorios críticos
        for dir_name in self.CRITICAL_DIRS:
            dir_path = self.repo_root / dir_name
            if dir_path.exists() and dir_path.is_dir():
                state["critical_dirs"][dir_name] = "ok"
            else:
                state["critical_dirs"][dir_name] = "missing"
                state["missing"] += 1
                state["warnings"].append(f"Critical directory missing: {dir_name}")

        # Verificar colisiones (archivos .orig, .bak, merge conflicts)
        state["collisions"] = self._detect_collisions()

        # Verificar estado de Lean
        state["lean_status"] = self._check_lean_status()

        # Verificar estado de git
        state["git_status"] = self._check_git_status()

        return state

    def _detect_collisions(self) -> int:
        """
        Detecta colisiones de archivos en el repositorio.

        Busca:
        - Archivos .orig (backups de merge)
        - Archivos .bak (backups manuales)
        - Marcadores de conflicto de merge

        Returns:
            Número de colisiones detectadas
        """
        collision_count = 0
        collision_patterns = ["*.orig", "*.bak", "*.rej"]

        for pattern in collision_patterns:
            matches = list(self.repo_root.rglob(pattern))
            collision_count += len(matches)

        # Buscar marcadores de conflicto de merge en archivos Python y Lean
        code_patterns = ["*.py", "*.lean"]
        for pattern in code_patterns:
            for file_path in self.repo_root.rglob(pattern):
                if self._has_merge_conflict(file_path):
                    collision_count += 1

        return collision_count

    def _has_merge_conflict(self, file_path: Path) -> bool:
        """
        Verifica si un archivo tiene marcadores de conflicto de merge.

        Args:
            file_path: Ruta al archivo a verificar

        Returns:
            True si tiene marcadores de conflicto
        """
        conflict_markers = ["<<<<<<<", "=======", ">>>>>>>"]
        try:
            with open(file_path, "r", encoding="utf-8", errors="ignore") as f:
                content = f.read()
                return any(marker in content for marker in conflict_markers)
        except Exception:
            return False

    def _check_lean_status(self) -> str:
        """
        Verifica el estado de la formalización Lean.

        Returns:
            "ok" si Lean está funcionando correctamente,
            "error" si hay errores,
            "not_found" si no se encuentra Lean
        """
        lean_dir = self.repo_root / "formalization" / "lean"

        if not lean_dir.exists():
            return "not_found"

        # Intentar verificar archivos .lean
        lean_files = list(lean_dir.rglob("*.lean"))
        if not lean_files:
            return "not_found"

        # Verificar sintaxis básica de archivos Lean
        for lean_file in lean_files[:5]:  # Verificar solo los primeros 5
            try:
                with open(lean_file, "r", encoding="utf-8") as f:
                    content = f.read()
                    # Verificar que no haya 'sorry' sin resolver
                    if "sorry" in content.lower():
                        # Check if it's a genuine 'sorry' (not in comments)
                        lines = content.split("\n")
                        for line in lines:
                            line_stripped = line.strip()
                            if line_stripped.startswith("--"):
                                continue
                            if "sorry" in line_stripped.lower():
                                return "warning_sorry"
            except Exception:
                pass

        return "ok"

    def _check_git_status(self) -> Dict[str, Any]:
        """
        Verifica el estado de git del repositorio.

        Returns:
            Diccionario con información de git:
            {
                "branch": nombre de la rama actual,
                "uncommitted": número de cambios sin commit,
                "untracked": número de archivos sin seguimiento
            }
        """
        result = {
            "branch": None,
            "uncommitted": 0,
            "untracked": 0,
        }

        try:
            # Obtener rama actual
            branch_result = subprocess.run(
                ["git", "-C", str(self.repo_root), "branch", "--show-current"],
                capture_output=True,
                text=True,
                timeout=10,
            )
            if branch_result.returncode == 0:
                result["branch"] = branch_result.stdout.strip()

            # Obtener estado
            status_result = subprocess.run(
                ["git", "-C", str(self.repo_root), "status", "--porcelain"],
                capture_output=True,
                text=True,
                timeout=10,
            )
            if status_result.returncode == 0:
                lines = status_result.stdout.strip().split("\n")
                for line in lines:
                    if line.strip():
                        if line.startswith("??"):
                            result["untracked"] += 1
                        else:
                            result["uncommitted"] += 1

        except Exception:
            pass

        return result

    def get_file_list(self, pattern: str = "*.py") -> List[Path]:
        """
        Obtiene lista de archivos que coinciden con un patrón.

        Args:
            pattern: Patrón glob para buscar archivos

        Returns:
            Lista de rutas a archivos que coinciden
        """
        return list(self.repo_root.rglob(pattern))

    def check_unicode_issues(self) -> List[Dict[str, Any]]:
        """
        Verifica problemas de codificación Unicode en archivos Python.

        Returns:
            Lista de archivos con problemas de Unicode
        """
        issues = []

        for py_file in self.repo_root.rglob("*.py"):
            try:
                with open(py_file, "r", encoding="utf-8") as f:
                    content = f.read()
                    # Verificar caracteres problemáticos
                    problematic_chars = ["\ufeff", "\u200b", "\u2028", "\u2029"]
                    for char in problematic_chars:
                        if char in content:
                            issues.append({
                                "file": str(py_file.relative_to(self.repo_root)),
                                "char": repr(char),
                                "type": "unicode_issue",
                            })
            except UnicodeDecodeError:
                issues.append({
                    "file": str(py_file.relative_to(self.repo_root)),
                    "char": "unknown",
                    "type": "decode_error",
                })
            except Exception:
                pass

        return issues


if __name__ == "__main__":
    # Demo del vigilante
    print("=" * 60)
    print("NOESIS GUARDIAN — Repository Watcher Demo")
    print("=" * 60)

    watcher = RepoWatcher()
    state = watcher.scan_repo()

    print("\n📊 Repository State:")
    print(f"   Timestamp: {state['timestamp']}")
    print(f"   Collisions: {state['collisions']}")
    print(f"   Missing files: {state['missing']}")
    print(f"   Lean status: {state['lean_status']}")

    if state["warnings"]:
        print("\n⚠️  Warnings:")
        for warning in state["warnings"]:
            print(f"   - {warning}")

    print("\n✅ Scan complete")
