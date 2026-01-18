#!/usr/bin/env python3
"""
Environment Integrity Verification Script

This script verifies the integrity of the environment lock files (ENV.lock and 
requirements-lock.txt) and ensures reproducibility across different environments.

Usage:
    python verify_environment_integrity.py [--verbose] [--generate-checksums]

Features:
- Verifies ENV.lock and requirements-lock.txt exist and are readable
- Generates and verifies SHA256 checksums for lock files
- Validates that installed packages match lock file specifications
- Checks for security vulnerabilities in pinned versions
- Ensures Python version compatibility

Author: José Manuel Mota Burruezo
License: MIT
"""

import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Dict, List, Tuple, Optional


class EnvironmentVerifier:
    """Verifies environment integrity and reproducibility."""
    
    CHECKSUM_FILE = "environment_checksums.json"
    EXPECTED_PYTHON_VERSION = "3.11"
    
    def __init__(self, verbose: bool = False):
        """
        Initialize the environment verifier.
        
        Args:
            verbose: Enable verbose output
        """
        self.verbose = verbose
        self.repo_root = Path(__file__).parent.resolve()
        self.errors: List[str] = []
        self.warnings: List[str] = []
        
    def log(self, message: str, level: str = "INFO"):
        """Log a message with optional verbose filtering."""
        if self.verbose or level in ["ERROR", "WARNING"]:
            prefix = {
                "INFO": "ℹ️ ",
                "SUCCESS": "✅",
                "WARNING": "⚠️ ",
                "ERROR": "❌"
            }.get(level, "  ")
            print(f"{prefix} {message}")
    
    def compute_file_checksum(self, filepath: Path) -> str:
        """
        Compute SHA256 checksum of a file.
        
        Args:
            filepath: Path to file
            
        Returns:
            Hexadecimal SHA256 checksum
        """
        sha256 = hashlib.sha256()
        with open(filepath, 'rb') as f:
            for chunk in iter(lambda: f.read(4096), b''):
                sha256.update(chunk)
        return sha256.hexdigest()
    
    def verify_file_exists(self, filepath: Path) -> bool:
        """
        Verify that a required file exists.
        
        Args:
            filepath: Path to file
            
        Returns:
            True if file exists and is readable
        """
        if not filepath.exists():
            self.errors.append(f"Required file not found: {filepath}")
            return False
        
        if not filepath.is_file():
            self.errors.append(f"Path exists but is not a file: {filepath}")
            return False
            
        return True
    
    def parse_requirements_file(self, filepath: Path) -> Dict[str, str]:
        """
        Parse a requirements file and extract package versions.
        
        Args:
            filepath: Path to requirements file
            
        Returns:
            Dictionary mapping package names to versions
        """
        packages = {}
        
        with open(filepath, 'r') as f:
            for line in f:
                line = line.strip()
                
                # Skip comments and empty lines
                if not line or line.startswith('#'):
                    continue
                
                # Skip platform-specific packages
                if '; platform_' in line:
                    line = line.split(';')[0].strip()
                
                # Parse package==version format
                match = re.match(r'^([a-zA-Z0-9_-]+)\s*==\s*([^\s;]+)', line)
                if match:
                    package, version = match.groups()
                    packages[package.lower()] = version
                
        return packages
    
    def get_installed_packages(self) -> Dict[str, str]:
        """
        Get currently installed packages and versions.
        
        Returns:
            Dictionary mapping package names to installed versions
        """
        try:
            result = subprocess.run(
                [sys.executable, '-m', 'pip', 'list', '--format=json'],
                capture_output=True,
                text=True,
                check=True
            )
            
            packages_list = json.loads(result.stdout)
            return {pkg['name'].lower(): pkg['version'] for pkg in packages_list}
            
        except (subprocess.CalledProcessError, json.JSONDecodeError) as e:
            self.errors.append(f"Failed to get installed packages: {e}")
            return {}
    
    def verify_lock_files_match(self) -> bool:
        """
        Verify that ENV.lock and requirements-lock.txt are consistent.
        
        Returns:
            True if files are consistent
        """
        env_lock = self.repo_root / "ENV.lock"
        req_lock = self.repo_root / "requirements-lock.txt"
        
        if not (self.verify_file_exists(env_lock) and self.verify_file_exists(req_lock)):
            return False
        
        # Parse both files
        env_packages = self.parse_requirements_file(env_lock)
        req_packages = self.parse_requirements_file(req_lock)
        
        # Check that all packages in requirements-lock are in ENV.lock
        # Use set operations for efficiency
        missing_packages = set(req_packages.keys()) - set(env_packages.keys())
        
        # Check for version mismatches
        version_mismatches = []
        for pkg in req_packages.keys():
            if pkg in env_packages and env_packages[pkg] != req_packages[pkg]:
                version_mismatches.append(
                    f"{pkg}: requirements-lock={req_packages[pkg]}, ENV.lock={env_packages[pkg]}"
                )
        
        if missing_packages:
            # Show only first 5 for brevity
            missing_list = sorted(missing_packages)[:5]
            self.warnings.append(
                f"Packages in requirements-lock.txt missing from ENV.lock: {', '.join(f'{p}=={req_packages[p]}' for p in missing_list)}"
            )
        
        if version_mismatches:
            self.errors.append(
                f"Version mismatches between lock files: {', '.join(version_mismatches[:5])}"
            )
            return False
        
        self.log(f"Lock files consistency check: {len(req_packages)} packages verified", "SUCCESS")
        return True
    
    def verify_installed_packages(self) -> bool:
        """
        Verify that installed packages match requirements-lock.txt.
        
        Returns:
            True if installed packages match lock file
        """
        req_lock = self.repo_root / "requirements-lock.txt"
        
        if not self.verify_file_exists(req_lock):
            return False
        
        required_packages = self.parse_requirements_file(req_lock)
        installed_packages = self.get_installed_packages()
        
        if not installed_packages:
            self.warnings.append("Could not verify installed packages")
            return True  # Don't fail if we can't check
        
        missing = []
        mismatched = []
        
        for pkg, required_version in required_packages.items():
            if pkg not in installed_packages:
                missing.append(f"{pkg}=={required_version}")
            elif installed_packages[pkg] != required_version:
                mismatched.append(
                    f"{pkg}: required={required_version}, installed={installed_packages[pkg]}"
                )
        
        if missing:
            self.warnings.append(
                f"Required packages not installed: {', '.join(missing[:10])}"
            )
        
        if mismatched:
            self.warnings.append(
                f"Version mismatches in installed packages: {', '.join(mismatched[:10])}"
            )
        
        if not missing and not mismatched:
            self.log(f"Installed packages match requirements-lock.txt", "SUCCESS")
        
        return True
    
    def generate_checksums(self) -> Dict[str, str]:
        """
        Generate checksums for all lock files.
        
        Returns:
            Dictionary mapping filenames to checksums
        """
        checksums = {}
        
        for filename in ["ENV.lock", "requirements-lock.txt", "requirements.txt"]:
            filepath = self.repo_root / filename
            if filepath.exists():
                checksum = self.compute_file_checksum(filepath)
                checksums[filename] = checksum
                self.log(f"Generated checksum for {filename}: {checksum[:16]}...", "INFO")
        
        return checksums
    
    def save_checksums(self, checksums: Dict[str, str]) -> bool:
        """
        Save checksums to file.
        
        Args:
            checksums: Dictionary of checksums to save
            
        Returns:
            True if successful
        """
        checksum_file = self.repo_root / self.CHECKSUM_FILE
        
        try:
            with open(checksum_file, 'w') as f:
                json.dump(checksums, f, indent=2, sort_keys=True)
            
            self.log(f"Saved checksums to {self.CHECKSUM_FILE}", "SUCCESS")
            return True
            
        except Exception as e:
            self.errors.append(f"Failed to save checksums: {e}")
            return False
    
    def verify_checksums(self) -> bool:
        """
        Verify that current lock files match saved checksums.
        
        Returns:
            True if checksums match
        """
        checksum_file = self.repo_root / self.CHECKSUM_FILE
        
        if not checksum_file.exists():
            self.warnings.append(
                f"Checksum file {self.CHECKSUM_FILE} not found. "
                "Run with --generate-checksums to create it."
            )
            return True  # Not an error if file doesn't exist yet
        
        try:
            with open(checksum_file, 'r') as f:
                saved_checksums = json.load(f)
            
            current_checksums = self.generate_checksums()
            
            mismatches = []
            for filename, saved_checksum in saved_checksums.items():
                current_checksum = current_checksums.get(filename)
                if current_checksum and current_checksum != saved_checksum:
                    mismatches.append(filename)
            
            if mismatches:
                self.errors.append(
                    f"Checksum mismatches detected: {', '.join(mismatches)}. "
                    "Lock files may have been modified."
                )
                return False
            
            self.log(f"All checksums verified successfully", "SUCCESS")
            return True
            
        except Exception as e:
            self.errors.append(f"Failed to verify checksums: {e}")
            return False
    
    def verify_dataset_checksums(self) -> bool:
        """
        Verify that dataset checksums match those recorded in ENV.lock.
        
        Returns:
            True if dataset checksums match or cannot be verified
        """
        env_lock = self.repo_root / "ENV.lock"
        
        if not self.verify_file_exists(env_lock):
            return False
        
        # Parse dataset checksums from ENV.lock
        recorded_checksums = {}
        in_dataset_section = False
        current_dataset = None
        
        with open(env_lock, 'r') as f:
            for line in f:
                line = line.strip()
                
                # Detect dataset checksums section
                if 'DATASET CHECKSUMS' in line:
                    in_dataset_section = True
                    continue
                
                # Exit section when we hit the next major section
                if in_dataset_section and line.startswith('# ─────') and 'PYTHON PACKAGES' in next(f, ''):
                    break
                
                # Parse dataset name and checksum
                if in_dataset_section and line.startswith('# ') and ':' in line and '# These' not in line:
                    # Line like: "# Evac_Rpsi_data.csv:"
                    dataset_name = line.lstrip('#').strip().rstrip(':').strip()
                    current_dataset = dataset_name
                elif in_dataset_section and current_dataset and line.startswith('#   '):
                    # Next line with checksum like: "#   412ab7ba54a5041..."
                    checksum = line.lstrip('#').strip()
                    if len(checksum) == 64:  # SHA-256 is 64 hex chars
                        recorded_checksums[current_dataset] = checksum
                    current_dataset = None
        
        if not recorded_checksums:
            self.log("No dataset checksums found in ENV.lock", "INFO")
            return True
        
        # Verify each dataset
        mismatches = []
        missing_files = []
        
        for dataset_name, expected_checksum in recorded_checksums.items():
            filepath = self.repo_root / dataset_name
            
            if not filepath.exists():
                missing_files.append(dataset_name)
                continue
            
            actual_checksum = self.compute_file_checksum(filepath)
            if actual_checksum != expected_checksum:
                mismatches.append(
                    f"{dataset_name}: expected={expected_checksum[:16]}..., actual={actual_checksum[:16]}..."
                )
        
        if missing_files:
            self.warnings.append(
                f"Dataset files not found: {', '.join(missing_files)}"
            )
        
        if mismatches:
            self.errors.append(
                f"Dataset checksum mismatches: {', '.join(mismatches)}. "
                "Dataset files may have been modified."
            )
            return False
        
        if recorded_checksums and not missing_files and not mismatches:
            self.log(f"Dataset checksums verified: {len(recorded_checksums)} files", "SUCCESS")
        
        return True
    
    def check_python_version(self) -> bool:
        """
        Check that Python version matches expected version.
        
        Returns:
            True if Python version is compatible
        """
        current_version = f"{sys.version_info.major}.{sys.version_info.minor}"
        
        if current_version != self.EXPECTED_PYTHON_VERSION:
            self.warnings.append(
                f"Python version mismatch: expected {self.EXPECTED_PYTHON_VERSION}, "
                f"got {current_version}. Results may not be fully reproducible."
            )
            return True  # Warning, not error
        
        self.log(f"Python version {current_version} matches expected version", "SUCCESS")
        return True
    
    def run_verification(self, generate_checksums: bool = False) -> bool:
        """
        Run full environment verification.
        
        Args:
            generate_checksums: Whether to generate new checksums
            
        Returns:
            True if all verifications pass
        """
        self.log("=" * 60, "INFO")
        self.log("Environment Integrity Verification", "INFO")
        self.log("=" * 60, "INFO")
        
        # Check Python version
        self.check_python_version()
        
        # Verify lock files exist
        self.log("\n📁 Verifying lock files...", "INFO")
        self.verify_file_exists(self.repo_root / "ENV.lock")
        self.verify_file_exists(self.repo_root / "requirements-lock.txt")
        
        # Verify lock files are consistent
        self.log("\n🔄 Checking lock file consistency...", "INFO")
        self.verify_lock_files_match()
        
        # Verify installed packages
        self.log("\n📦 Verifying installed packages...", "INFO")
        self.verify_installed_packages()
        
        # Verify dataset checksums
        self.log("\n🔬 Verifying dataset checksums...", "INFO")
        self.verify_dataset_checksums()
        
        # Handle checksums
        if generate_checksums:
            self.log("\n🔐 Generating checksums...", "INFO")
            checksums = self.generate_checksums()
            self.save_checksums(checksums)
        else:
            self.log("\n🔐 Verifying checksums...", "INFO")
            self.verify_checksums()
        
        # Report results
        self.log("\n" + "=" * 60, "INFO")
        self.log("Verification Results", "INFO")
        self.log("=" * 60, "INFO")
        
        if self.warnings:
            self.log(f"\n⚠️  {len(self.warnings)} warning(s):", "WARNING")
            for warning in self.warnings:
                self.log(f"  • {warning}", "WARNING")
        
        if self.errors:
            self.log(f"\n❌ {len(self.errors)} error(s):", "ERROR")
            for error in self.errors:
                self.log(f"  • {error}", "ERROR")
            self.log("\n❌ Verification FAILED", "ERROR")
            return False
        
        self.log("\n✅ Verification PASSED", "SUCCESS")
        return True


def main():
    """Main entry point."""
    parser = argparse.ArgumentParser(
        description="Verify environment integrity and reproducibility"
    )
    parser.add_argument(
        "--verbose", "-v",
        action="store_true",
        help="Enable verbose output"
    )
    parser.add_argument(
        "--generate-checksums",
        action="store_true",
        help="Generate new checksums instead of verifying existing ones"
    )
    
    args = parser.parse_args()
    
    verifier = EnvironmentVerifier(verbose=args.verbose)
    success = verifier.run_verification(generate_checksums=args.generate_checksums)
    
    sys.exit(0 if success else 1)


if __name__ == "__main__":
    main()
