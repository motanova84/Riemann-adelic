"""
Auto-repair engine module for Noesis Guardian 3.0.

Provides lightweight automatic repair of repository structure.
"""

import os
from typing import Dict


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
