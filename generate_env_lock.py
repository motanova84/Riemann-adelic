#!/usr/bin/env python3
"""
Generate ENV.lock from current environment.

This script creates a comprehensive ENV.lock file that includes:
1. All packages from requirements-lock.txt (CI/CD dependencies)
2. Additional system packages and dependencies

The ENV.lock file serves as a snapshot of the complete environment
for maximum reproducibility.

Usage:
    python generate_env_lock.py [--from-freeze] [--output ENV.lock]
"""

import argparse
import re
import subprocess
import sys
from pathlib import Path
from typing import Dict, Set


def parse_requirements_file(filepath: Path) -> Dict[str, str]:
    """Parse requirements file and return dict of package:version."""
    packages = {}
    
    with open(filepath, 'r') as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith('#'):
                continue
            
            match = re.match(r'^([a-zA-Z0-9_-]+)\s*==\s*([^\s;]+)', line)
            if match:
                pkg_name, version = match.groups()
                packages[pkg_name.lower()] = version
    
    return packages


def get_pip_freeze() -> Dict[str, str]:
    """Get all installed packages from pip freeze."""
    try:
        result = subprocess.run(
            [sys.executable, '-m', 'pip', 'freeze'],
            capture_output=True,
            text=True,
            check=True
        )
        
        packages = {}
        for line in result.stdout.splitlines():
            if '==' in line:
                pkg, version = line.split('==', 1)
                packages[pkg.lower()] = version.strip()
        
        return packages
        
    except subprocess.CalledProcessError as e:
        print(f"Error running pip freeze: {e}", file=sys.stderr)
        return {}


def generate_env_lock(
    requirements_lock_path: Path,
    output_path: Path,
    use_pip_freeze: bool = False
):
    """
    Generate ENV.lock file.
    
    Args:
        requirements_lock_path: Path to requirements-lock.txt
        output_path: Path to output ENV.lock
        use_pip_freeze: If True, use pip freeze; otherwise use requirements-lock.txt
    """
    
    if use_pip_freeze:
        print("📦 Generating ENV.lock from pip freeze...")
        packages = get_pip_freeze()
        source = "pip freeze"
    else:
        print("📦 Generating ENV.lock from requirements-lock.txt...")
        packages = parse_requirements_file(requirements_lock_path)
        source = "requirements-lock.txt"
    
    if not packages:
        print("❌ No packages found!", file=sys.stderr)
        return False
    
    # Sort packages alphabetically
    sorted_packages = sorted(packages.items())
    
    # Write ENV.lock
    with open(output_path, 'w') as f:
        f.write("# Environment Lock File\n")
        f.write("# Auto-generated - DO NOT edit manually\n")
        f.write(f"# Source: {source}\n")
        f.write(f"# Python version: {sys.version_info.major}.{sys.version_info.minor}\n")
        f.write("#\n")
        f.write("# This file contains the complete package environment for reproducibility.\n")
        f.write("# It includes all packages required by requirements-lock.txt plus their\n")
        f.write("# transitive dependencies.\n")
        f.write("#\n")
        f.write("# To verify integrity:\n")
        f.write("#   python verify_environment_integrity.py\n")
        f.write("#\n")
        f.write("# To regenerate:\n")
        f.write("#   python generate_env_lock.py\n")
        f.write("\n")
        
        for pkg, version in sorted_packages:
            f.write(f"{pkg}=={version}\n")
    
    print(f"✅ ENV.lock generated with {len(packages)} packages")
    print(f"   Output: {output_path}")
    return True


def main():
    """Main entry point."""
    parser = argparse.ArgumentParser(
        description="Generate ENV.lock file for environment reproducibility"
    )
    parser.add_argument(
        "--from-freeze",
        action="store_true",
        help="Generate from pip freeze instead of requirements-lock.txt"
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("ENV.lock"),
        help="Output file path (default: ENV.lock)"
    )
    
    args = parser.parse_args()
    
    repo_root = Path(__file__).parent.resolve()
    requirements_lock = repo_root / "requirements-lock.txt"
    output_path = repo_root / args.output
    
    if not requirements_lock.exists() and not args.from_freeze:
        print(f"❌ requirements-lock.txt not found: {requirements_lock}", file=sys.stderr)
        print("   Use --from-freeze to generate from current environment", file=sys.stderr)
        return 1
    
    success = generate_env_lock(
        requirements_lock,
        output_path,
        use_pip_freeze=args.from_freeze
    )
    
    return 0 if success else 1


if __name__ == "__main__":
    sys.exit(main())
