"""
Repository watcher module for Noesis Guardian 3.0.

Provides simple structure scanning of the repository.

Author: Jose Manuel Mota Burruezo (JMMB)
"""

import os
from typing import Dict, List


class RepoWatcher:
    """
    Repository structure monitoring component.

    Scans the repository for expected files and directories,
    reporting any that are missing.
    """

    def __init__(self) -> None:
        """Initialize the watcher with expected repository structure."""
        self.expected_files: List[str] = [
            "README.md",
            "pyproject.toml",
            "formalization",
            "tests",
        ]

    def scan(self) -> Dict[str, object]:
        """
        Scan the repository for expected files and directories.

        Returns:
            Dictionary containing:
                - missing: List of missing file/directory paths
                - errors: Boolean indicating if there are any missing items
        """
        missing: List[str] = []

        for expected in self.expected_files:
            if not os.path.exists(expected):
                missing.append(expected)

        return {
            "missing": missing,
            "errors": len(missing) > 0,
        }
