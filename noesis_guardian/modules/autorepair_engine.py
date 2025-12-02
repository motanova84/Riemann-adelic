"""
Auto-repair engine module for Noesis Guardian 3.0.

Provides lightweight automatic repair of repository structure.
"""

import os
from typing import Dict
#!/usr/bin/env python3
"""
NOESIS GUARDIAN 3.0 — Auto Repair Engine Module

Provides automatic repair capabilities for basic repository structure issues.

Author: José Manuel Mota Burruezo (JMMB Ψ ✧)
"""

import os
from typing import Dict, List

# Known directory paths in the repository
KNOWN_DIRECTORIES: List[str] = [
    "formalization",
    "tests",
    "noesis_guardian",
    "noesis_guardian/logs",
    "noesis_guardian/modules",
    "noesis_guardian/panel",
    "data",
    "docs",
    "utils",
]


class AutoRepairEngine:
    """
    Motor de autoreparación ligera.

    Importante: aquí solo hacemos cosas inocuas:
    - crear archivos vacíos con encabezado
    No toca Lean, ni prueba nada, salvo que tú lo amplíes.
    """

    def repair(self, repo_state: Dict) -> None:
        """
        Repair missing structure in the repository.

        Args:
            repo_state: Dictionary containing 'missing' list of paths.
        """
        print("🔧 AutoRepairEngine: reparando estructura mínima…")
        for path in repo_state.get("missing", []):
            # Security check: prevent path traversal attacks
            if ".." in path or os.path.isabs(path):
                print(f"   ⚠️ ruta insegura rechazada: {path}")
                continue
            try:
                # Ensure parent directory exists for nested paths
                parent_dir = os.path.dirname(path)
                if parent_dir:
                    os.makedirs(parent_dir, exist_ok=True)
                with open(path, "w") as f:
                    f.write(f"# Auto-regenerado por Noesis Guardian 3.0: {path}\n")
                print(f"   → creado {path}")
            except Exception as e:
                print(f"   ⚠️ no se pudo crear {path}: {e}")
    Automatic repository structure repair component.

    Handles regeneration of missing critical files with minimal content
    to restore repository structure integrity.
    """

    def __init__(self) -> None:
        """Initialize the repair engine with known directories."""
        self.known_directories = set(KNOWN_DIRECTORIES)

    def _is_directory(self, path: str) -> bool:
        """
        Determine if a path refers to a directory.

        Args:
            path: Path to check.

        Returns:
            True if path is a directory, False if it's a file.
        """
        # Explicit directory markers
        if path.endswith("/"):
            return True

        # Check against known directories
        if path in self.known_directories:
            return True

        # If the path has no file extension and doesn't look like a file
        # with common README/LICENSE/etc patterns, treat as directory
        base = os.path.basename(path)
        known_extensionless_files = {
            "README", "LICENSE", "CHANGELOG", "CONTRIBUTING",
            "Makefile", "Dockerfile", ".gitignore", ".gitkeep",
        }
        if base in known_extensionless_files:
            return False

        # Check for file extension
        _, ext = os.path.splitext(path)
        return ext == ""

    def repair(self, repo_state: Dict[str, object]) -> bool:
        """
        Repair missing repository structure elements.

        Args:
            repo_state: Dictionary containing repository state information,
                        including a 'missing' key with list of missing paths.

        Returns:
            True if repair was successful, False otherwise.
        """
        print("🔧 Reparando estructura mínima...")

        for missing_path in repo_state.get("missing", []):
            try:
                if self._is_directory(missing_path):
                    # It's a directory
                    os.makedirs(missing_path, exist_ok=True)
                    print(f"   → Directorio creado: {missing_path}")
                else:
                    # It's a file - create parent directories if needed
                    parent_dir = os.path.dirname(missing_path)
                    if parent_dir:
                        os.makedirs(parent_dir, exist_ok=True)
                    with open(missing_path, "w") as f:
                        f.write(f"# Auto-regenerado: {missing_path}\n")
                    print(f"   → Archivo regenerado: {missing_path}")
            except Exception as e:
                print(f"   ⚠️ Error al reparar {missing_path}: {e}")
                return False

        return True
