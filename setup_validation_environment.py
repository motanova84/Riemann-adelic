"""Utility helpers to prepare the validation workspace.

This module centralises the optional setup steps required by the
numerical validation utilities that live in :mod:`validation`.  The
functions are intentionally conservative so that running the script is
idempotent and safe inside CI pipelines.
"""
from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path
from typing import Iterable, List

DEFAULT_PACKAGES: List[str] = [
    "mpmath>=1.3.0",
    "numpy>=1.24.0",
    "scipy>=1.10.0",
    "sympy>=1.12.0",
    "pandas>=2.0.0",
    "matplotlib>=3.7.0",
    "seaborn>=0.12.0",
    "plotly>=5.14.0",
    "jupyter>=1.0.0",
    "ipywidgets>=8.0.0",
]

DIRECTORIES: List[Path] = [
    Path("data/validation/rh_critical_line"),
    Path("data/validation/ds_equiv_xi"),
    Path("data/validation/non_vanishing"),
    Path("data/validation/certificates"),
    Path("data/validation/logs"),
    Path("data/validation/results"),
    Path("logs/validation"),
    Path("reports/rh_ds_validation"),
    Path("notebooks/validation"),
    Path("scripts/validation"),
]


def install_dependencies(packages: Iterable[str] = DEFAULT_PACKAGES) -> None:
    """Install validation dependencies using :mod:`pip`.

    The helper reports success or failure for each package but does not
    abort the process when an installation fails.  This behaviour keeps
    the function friendly for local development where some packages may
    already be present or intentionally skipped.
    """

    python = sys.executable
    for package in packages:
        try:
            subprocess.check_call([python, "-m", "pip", "install", package])
            print(f"✅ Installed {package}")
        except subprocess.CalledProcessError:
            print(f"❌ Failed to install {package}")


def setup_directories(paths: Iterable[Path] = DIRECTORIES) -> None:
    """Ensure that every directory required by the validation suite exists."""

    for path in paths:
        path.mkdir(parents=True, exist_ok=True)
        print(f"📁 Ensured directory exists: {path}")


def write_environment_manifest(packages: Iterable[str]) -> None:
    """Persist a manifest describing the configuration that was applied."""

    manifest_path = Path("data/validation/environment_manifest.json")
    manifest_path.parent.mkdir(parents=True, exist_ok=True)

    manifest = {
        "packages": list(packages),
        "python": sys.version,
        "cwd": os.getcwd(),
    }

    manifest_path.write_text(json.dumps(manifest, indent=2))
    print(f"📝 Wrote environment manifest to {manifest_path}")


def download_reference_data() -> None:
    """Placeholder hook that documents where reference data can be added.

    The project currently relies on the `mpmath` implementation to
    generate zeta zeros on demand.  Teams that have access to Odlyzko's
    pre-computed datasets can extend this function to download and cache
    the files inside ``data/external``.
    """

    external_dir = Path("data/external")
    external_dir.mkdir(parents=True, exist_ok=True)
    (external_dir / "README.txt").write_text(
        "Reference data can be placed in this directory.\n"
        "Populate it with Odlyzko zero tables or other artefacts as\n"
        "required for higher precision experiments.\n"
    )
    print(f"📥 Prepared data directory at {external_dir}")


def main() -> None:
    install_dependencies()
    setup_directories()
    download_reference_data()
    write_environment_manifest(DEFAULT_PACKAGES)
    print("🎉 Validation environment ready")


if __name__ == "__main__":
    main()
