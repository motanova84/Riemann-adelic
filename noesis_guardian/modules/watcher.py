"""
Repository watcher module for Noesis Guardian 3.0.

Provides simple structure scanning of the repository.
"""

import os
from typing import Dict, List


class RepoWatcher:
    """Escaneo muy simple de estructura mínima esperada."""

    def __init__(self) -> None:
        """Initialize the watcher with expected paths."""
        self.expected_paths: List[str] = [
            "README.md",
            "pyproject.toml",
            "formalization",
            "tests",
        ]

    def scan(self) -> Dict:
        """
        Scan the repository for expected paths.

        Returns:
            Dict with 'missing' list and 'errors' boolean.
        """
        missing: List[str] = []
        for path in self.expected_paths:
            if not os.path.exists(path):
                missing.append(path)

        return {
            "missing": missing,
            "errors": bool(missing),
        }
