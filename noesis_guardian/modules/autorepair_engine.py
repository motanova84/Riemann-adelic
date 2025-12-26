"""
Auto-repair engine module for Noesis Guardian 3.0.

Provides lightweight automatic repair of repository structure.

Author: Jose Manuel Mota Burruezo (JMMB)
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
            True if path is a directory, False if it is a file.
        """
        # Explicit directory markers
        if path.endswith("/"):
            return True

        # Check against known directories
        if path in self.known_directories:
            return True

        # If the path has no file extension and does not look like a file
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
        print("Repairing minimal structure...")

        for missing_path in repo_state.get("missing", []):
            # Security check: prevent path traversal attacks
            if ".." in missing_path or os.path.isabs(missing_path):
                print(f"   Warning: insecure path rejected: {missing_path}")
                continue
            try:
                if self._is_directory(missing_path):
                    # It is a directory
                    os.makedirs(missing_path, exist_ok=True)
                    print(f"   -> Directory created: {missing_path}")
                else:
                    # It is a file - create parent directories if needed
                    parent_dir = os.path.dirname(missing_path)
                    if parent_dir:
                        os.makedirs(parent_dir, exist_ok=True)
                    with open(missing_path, "w") as f:
                        f.write(f"# Auto-regenerated: {missing_path}\n")
                    print(f"   -> File regenerated: {missing_path}")
            except Exception as e:
                print(f"   Warning: Error repairing {missing_path}: {e}")
                return False

        return True
