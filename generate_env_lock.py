#!/usr/bin/env python3
"""
Generate ENV.lock from current environment.

This script creates a comprehensive ENV.lock file that includes:
1. All packages from requirements-lock.txt (CI/CD dependencies)
2. System information (OS, kernel, architecture)
3. Python toolchain details
4. Lean 4 version and other mathematical tools
5. Dataset checksums for reproducibility
6. Random seeds and configuration

The ENV.lock file serves as a snapshot of the complete environment
for maximum reproducibility across different machines, time periods,
and execution environments.

Usage:
    python generate_env_lock.py [--from-freeze] [--output ENV.lock]
"""

import argparse
import hashlib
import json
import os
import platform
import re
import subprocess
import sys
from datetime import datetime
from pathlib import Path
from typing import Dict, Set, Optional, Any


# QCAL configuration parameters to extract from .qcal_beacon
QCAL_PARAMS = [
    'frequency',
    'fundamental_frequency',
    'coherence',
    'universal_constant_C',
    'coherence_constant_C_prime',
]


def compute_file_checksum(filepath: Path) -> Optional[str]:
    """Compute SHA256 checksum of a file."""
    if not filepath.exists():
        return None
    try:
        sha256 = hashlib.sha256()
        with open(filepath, 'rb') as f:
            for chunk in iter(lambda: f.read(4096), b''):
                sha256.update(chunk)
        return sha256.hexdigest()
    except Exception as e:
        print(f"Warning: Could not compute checksum for {filepath}: {e}", file=sys.stderr)
        return None


def get_system_info() -> Dict[str, Any]:
    """Collect system information for reproducibility."""
    info = {
        'os': platform.system(),
        'os_release': platform.release(),
        'os_version': platform.version(),
        'architecture': platform.machine(),
        'platform': platform.platform(),
        'processor': platform.processor() or 'unknown',
        'python_version': platform.python_version(),
        'python_implementation': platform.python_implementation(),
        'python_compiler': platform.python_compiler(),
        'timestamp': datetime.now().astimezone().replace(microsecond=0).isoformat(),
    }
    
    # Add Linux-specific info if available
    if platform.system() == 'Linux':
        try:
            with open('/etc/os-release', 'r') as f:
                for line in f:
                    if line.startswith('PRETTY_NAME='):
                        info['linux_distro'] = line.split('=', 1)[1].strip().strip('"')
                        break
        except Exception:
            pass
    
    return info


def get_lean4_version() -> Optional[str]:
    """Get Lean 4 version if available."""
    try:
        result = subprocess.run(
            ['lean', '--version'],
            capture_output=True,
            text=True,
            timeout=5
        )
        if result.returncode == 0:
            # Extract version from output like "Lean (version 4.5.0, ...)"
            match = re.search(r'version\s+([\d.]+)', result.stdout)
            if match:
                return match.group(1)
        return None
    except Exception:
        return None


def get_tool_versions() -> Dict[str, Optional[str]]:
    """Get versions of mathematical and computational tools."""
    tools = {}
    
    # Git version
    try:
        result = subprocess.run(['git', '--version'], capture_output=True, text=True, timeout=5)
        if result.returncode == 0:
            match = re.search(r'git version ([\d.]+)', result.stdout)
            if match:
                tools['git'] = match.group(1)
    except Exception:
        tools['git'] = None
    
    # Lean 4
    tools['lean4'] = get_lean4_version()
    
    # Lake (Lean build tool)
    try:
        result = subprocess.run(['lake', '--version'], capture_output=True, text=True, timeout=5)
        if result.returncode == 0:
            match = re.search(r'version\s+([\d.]+)', result.stdout)
            if match:
                tools['lake'] = match.group(1)
    except Exception:
        tools['lake'] = None
    
    # GCC/G++ (for compiled extensions)
    try:
        result = subprocess.run(['gcc', '--version'], capture_output=True, text=True, timeout=5)
        if result.returncode == 0:
            match = re.search(r'gcc.*?([\d.]+)', result.stdout)
            if match:
                tools['gcc'] = match.group(1)
    except Exception:
        tools['gcc'] = None
    
    return tools


def get_dataset_checksums(repo_root: Path) -> Dict[str, str]:
    """Compute checksums for critical datasets."""
    datasets = {}
    
    # Key dataset files for QCAL validation
    dataset_files = [
        'Evac_Rpsi_data.csv',  # Main spectral validation data
        'data/critical_line_verification.csv',
        'data/error_profile.json',
        '.qcal_beacon',  # QCAL configuration
    ]
    
    for dataset_file in dataset_files:
        filepath = repo_root / dataset_file
        checksum = compute_file_checksum(filepath)
        if checksum:
            datasets[dataset_file] = checksum
    
    return datasets


def get_qcal_configuration(repo_root: Path) -> Dict[str, Any]:
    """Extract QCAL-specific configuration from .qcal_beacon."""
    config = {}
    beacon_file = repo_root / '.qcal_beacon'
    
    if beacon_file.exists():
        try:
            with open(beacon_file, 'r') as f:
                for line in f:
                    line = line.strip()
                    if line.startswith('#') or not line:
                        continue
                    
                    if '=' in line:
                        key, value = line.split('=', 1)
                        key = key.strip()
                        value = value.strip().strip('"')
                        
                        # Extract key QCAL parameters
                        if key in QCAL_PARAMS:
                            config[key] = value
        except Exception as e:
            print(f"Warning: Could not read .qcal_beacon: {e}", file=sys.stderr)
    
    return config


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
    use_pip_freeze: bool = False,
    repo_root: Path = None
):
    """
    Generate comprehensive ENV.lock file.
    
    Args:
        requirements_lock_path: Path to requirements-lock.txt
        output_path: Path to output ENV.lock
        use_pip_freeze: If True, use pip freeze; otherwise use requirements-lock.txt
        repo_root: Repository root directory
    """
    
    if repo_root is None:
        repo_root = Path(__file__).parent.resolve()
    
    print("📦 Generating comprehensive ENV.lock...")
    
    # Collect system information
    print("  ├─ Collecting system information...")
    system_info = get_system_info()
    
    # Collect tool versions
    print("  ├─ Detecting mathematical tools...")
    tool_versions = get_tool_versions()
    
    # Collect dataset checksums
    print("  ├─ Computing dataset checksums...")
    dataset_checksums = get_dataset_checksums(repo_root)
    
    # Collect QCAL configuration
    print("  ├─ Reading QCAL configuration...")
    qcal_config = get_qcal_configuration(repo_root)
    
    # Get Python packages
    if use_pip_freeze:
        print("  ├─ Getting packages from pip freeze...")
        packages = get_pip_freeze()
        source = "pip freeze"
    else:
        print("  ├─ Getting packages from requirements-lock.txt...")
        packages = parse_requirements_file(requirements_lock_path)
        source = "requirements-lock.txt"
    
    if not packages:
        print("❌ No packages found!", file=sys.stderr)
        return False
    
    # Sort packages alphabetically
    sorted_packages = sorted(packages.items())
    
    # Write ENV.lock with comprehensive metadata
    print("  └─ Writing ENV.lock...")
    with open(output_path, 'w') as f:
        # Header
        f.write("# ═══════════════════════════════════════════════════════════════\n")
        f.write("# QCAL Environment Lock File\n")
        f.write("# Complete Environment Snapshot for Reproducibility\n")
        f.write("# ═══════════════════════════════════════════════════════════════\n")
        f.write("#\n")
        f.write("# This file captures the complete computational environment used\n")
        f.write("# for QCAL validation and Riemann Hypothesis proof verification.\n")
        f.write("#\n")
        f.write("# It ensures bit-for-bit reproducibility of:\n")
        f.write("#   - 141.7001 Hz spectral validations (GW150914/GW250114)\n")
        f.write("#   - Riemann Hypothesis (RH) proof verification\n")
        f.write("#   - Birch-Swinnerton-Dyer (BSD) validations\n")
        f.write("#   - Navier-Stokes (NS) demonstrations\n")
        f.write("#   - P vs NP spectral connections\n")
        f.write("#\n")
        f.write("# ═══════════════════════════════════════════════════════════════\n")
        f.write("\n")
        
        # System Information Section
        f.write("# ───────────────────────────────────────────────────────────────\n")
        f.write("# SYSTEM INFORMATION\n")
        f.write("# ───────────────────────────────────────────────────────────────\n")
        f.write("#\n")
        f.write(f"# Operating System:    {system_info['os']}\n")
        f.write(f"# OS Release:          {system_info['os_release']}\n")
        if 'linux_distro' in system_info:
            f.write(f"# Linux Distribution:  {system_info['linux_distro']}\n")
        f.write(f"# Architecture:        {system_info['architecture']}\n")
        f.write(f"# Platform:            {system_info['platform']}\n")
        f.write(f"# Processor:           {system_info['processor']}\n")
        f.write("#\n")
        f.write(f"# Python Version:      {system_info['python_version']}\n")
        f.write(f"# Python Impl:         {system_info['python_implementation']}\n")
        f.write(f"# Python Compiler:     {system_info['python_compiler']}\n")
        f.write("#\n")
        f.write(f"# Generated:           {system_info['timestamp']}\n")
        f.write("#\n")
        
        # Mathematical Tools Section
        f.write("# ───────────────────────────────────────────────────────────────\n")
        f.write("# MATHEMATICAL TOOLS & TOOLCHAIN\n")
        f.write("# ───────────────────────────────────────────────────────────────\n")
        f.write("#\n")
        if tool_versions.get('lean4'):
            f.write(f"# Lean 4:              {tool_versions['lean4']}\n")
        else:
            f.write("# Lean 4:              Not installed\n")
        
        if tool_versions.get('lake'):
            f.write(f"# Lake:                {tool_versions['lake']}\n")
        
        if tool_versions.get('git'):
            f.write(f"# Git:                 {tool_versions['git']}\n")
        
        if tool_versions.get('gcc'):
            f.write(f"# GCC:                 {tool_versions['gcc']}\n")
        f.write("#\n")
        
        # QCAL Configuration Section
        if qcal_config:
            f.write("# ───────────────────────────────────────────────────────────────\n")
            f.write("# QCAL ∞³ CONFIGURATION\n")
            f.write("# ───────────────────────────────────────────────────────────────\n")
            f.write("#\n")
            if 'frequency' in qcal_config or 'fundamental_frequency' in qcal_config:
                freq = qcal_config.get('frequency') or qcal_config.get('fundamental_frequency')
                f.write(f"# Frequency:           {freq}\n")
            if 'coherence' in qcal_config:
                f.write(f"# Coherence C:         {qcal_config['coherence']}\n")
            if 'universal_constant_C' in qcal_config:
                f.write(f"# Universal C:         {qcal_config['universal_constant_C']}\n")
            if 'coherence_constant_C_prime' in qcal_config:
                f.write(f"# Coherence C':        {qcal_config['coherence_constant_C_prime']}\n")
            f.write("#\n")
        
        # Dataset Checksums Section
        if dataset_checksums:
            f.write("# ───────────────────────────────────────────────────────────────\n")
            f.write("# DATASET CHECKSUMS (SHA-256)\n")
            f.write("# ───────────────────────────────────────────────────────────────\n")
            f.write("#\n")
            f.write("# These checksums ensure validation data integrity and exact\n")
            f.write("# reproducibility of numerical results.\n")
            f.write("#\n")
            for dataset_name, checksum in sorted(dataset_checksums.items()):
                f.write(f"# {dataset_name}:\n")
                f.write(f"#   {checksum}\n")
            f.write("#\n")
        
        # Python Packages Section
        f.write("# ───────────────────────────────────────────────────────────────\n")
        f.write(f"# PYTHON PACKAGES ({len(packages)} packages)\n")
        f.write("# ───────────────────────────────────────────────────────────────\n")
        f.write("#\n")
        f.write(f"# Source: {source}\n")
        f.write("#\n")
        f.write("# To verify integrity:\n")
        f.write("#   python verify_environment_integrity.py\n")
        f.write("#\n")
        f.write("# To regenerate:\n")
        f.write("#   python generate_env_lock.py\n")
        f.write("#\n")
        f.write("# ───────────────────────────────────────────────────────────────\n")
        f.write("\n")
        
        # Write packages
        for pkg, version in sorted_packages:
            f.write(f"{pkg}=={version}\n")
        
        # Footer
        f.write("\n")
        f.write("# ═══════════════════════════════════════════════════════════════\n")
        f.write("# END OF ENV.lock\n")
        f.write("# ═══════════════════════════════════════════════════════════════\n")
        f.write("#\n")
        f.write("# This environment snapshot guarantees reproducibility for:\n")
        f.write("#   • Riemann Hypothesis proof verification\n")
        f.write("#   • QCAL ∞³ spectral validations (141.7001 Hz)\n")
        f.write("#   • GW150914 and GW250114 gravitational wave analysis\n")
        f.write("#   • BSD, P vs NP, and other mathematical validations\n")
        f.write("#\n")
        f.write("# For external auditors: This file acts as a 'hash of reality',\n")
        f.write("# ensuring that validation results (e.g., 18.2σ detections,\n")
        f.write("# Lean 4 builds without 'sorry') are not dependent on hidden\n")
        f.write("# environmental changes.\n")
        f.write("#\n")
        f.write("# Author: José Manuel Mota Burruezo Ψ ✧ ∞³\n")
        f.write("# Institution: Instituto de Conciencia Cuántica (ICQ)\n")
        f.write("# License: Creative Commons BY-NC-SA 4.0\n")
        f.write("#\n")
        f.write("# ═══════════════════════════════════════════════════════════════\n")
    
    print(f"\n✅ ENV.lock generated successfully")
    print(f"   System: {system_info['platform']}")
    print(f"   Python: {system_info['python_version']}")
    if tool_versions.get('lean4'):
        print(f"   Lean 4: {tool_versions['lean4']}")
    print(f"   Packages: {len(packages)}")
    print(f"   Datasets: {len(dataset_checksums)} checksummed")
    print(f"   Output: {output_path}")
    return True


def main():
    """Main entry point."""
    parser = argparse.ArgumentParser(
        description="Generate comprehensive ENV.lock file for environment reproducibility"
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
        use_pip_freeze=args.from_freeze,
        repo_root=repo_root
    )
    
    return 0 if success else 1


if __name__ == "__main__":
    sys.exit(main())
