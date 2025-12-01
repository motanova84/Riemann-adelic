#!/usr/bin/env python3
"""
NOESIS GUARDIAN 3.0 — Auto Repair Engine Module

Provides automatic repair capabilities for basic repository structure issues.

Author: José Manuel Mota Burruezo (JMMB Ψ ✧)
"""

import os
from typing import Dict


class AutoRepairEngine:
    """
    Automatic repository structure repair component.

    Handles regeneration of missing critical files with minimal content
    to restore repository structure integrity.
    """

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
                if missing_path.endswith("/") or not os.path.splitext(missing_path)[1]:
                    # It's a directory
                    os.makedirs(missing_path, exist_ok=True)
                    print(f"   → Directorio creado: {missing_path}")
                else:
                    # It's a file
                    with open(missing_path, "w") as f:
                        f.write(f"# Auto-regenerado: {missing_path}\n")
                    print(f"   → Archivo regenerado: {missing_path}")
            except Exception as e:
                print(f"   ⚠️ Error al reparar {missing_path}: {e}")
                return False

        return True
