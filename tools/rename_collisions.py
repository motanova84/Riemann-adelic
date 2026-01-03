#!/usr/bin/env python3
"""
Rename Collisions Script for NOESIS GUARDIAN ∞³

This script identifies and renames conflicting files in the repository,
such as backup files (.orig, .bak), merge conflict remnants, and duplicates.

Author: José Manuel Mota Burruezo (JMMB Ψ ✧)
"""

import os
import shutil
from datetime import datetime
from pathlib import Path
from typing import List, Tuple


def find_collision_files(repo_root: Path) -> List[Tuple[Path, str]]:
    """
    Find files that represent collisions or backups.
    
    Args:
        repo_root: Root directory of the repository
        
    Returns:
        list: Tuples of (file_path, collision_type)
    """
    collision_extensions = ['.orig', '.bak', '.backup', '.conflict', '.mine', '.theirs']
    
    collisions = []
    
    for root, dirs, files in os.walk(repo_root):
        # Skip hidden directories and common non-source directories
        dirs[:] = [d for d in dirs if not d.startswith('.') and d not in [
            'node_modules', '__pycache__', '.venv', 'venv', 'dist', 'build'
        ]]
        
        for file in files:
            file_path = Path(root) / file
            
            # Check for collision extensions
            for ext in collision_extensions:
                if file.endswith(ext):
                    collisions.append((file_path, f"backup_{ext}"))
                    break
            
            # Check for merge conflict patterns (e.g., file.py.r123)
            if '.r' in file and file.split('.r')[-1].isdigit():
                collisions.append((file_path, "svn_conflict"))
    
    return collisions


def move_collision_files(collisions: List[Tuple[Path, str]], repo_root: Path) -> dict:
    """
    Move collision files to a backup directory.
    
    Args:
        collisions: List of (path, type) tuples
        repo_root: Repository root directory
        
    Returns:
        dict: Report of moved files
    """
    backup_dir = repo_root / ".noesis_backups" / datetime.now().strftime("%Y%m%d_%H%M%S")
    backup_dir.mkdir(parents=True, exist_ok=True)
    
    report = {
        "moved": [],
        "errors": [],
        "backup_dir": str(backup_dir)
    }
    
    for file_path, collision_type in collisions:
        try:
            # Create subdirectory structure in backup
            rel_path = file_path.relative_to(repo_root)
            target_dir = backup_dir / rel_path.parent
            target_dir.mkdir(parents=True, exist_ok=True)
            
            target_path = target_dir / file_path.name
            
            # Move the file
            shutil.move(str(file_path), str(target_path))
            
            report["moved"].append({
                "original": str(rel_path),
                "backup": str(target_path),
                "type": collision_type
            })
            print(f"  ✓ Moved: {rel_path} → .noesis_backups/")
            
        except Exception as e:
            report["errors"].append({
                "file": str(file_path),
                "error": str(e)
            })
            print(f"  ✗ Error moving {file_path}: {e}")
    
    return report


def main():
    """Main entry point for collision rename script."""
    print("=" * 60)
    print("NOESIS GUARDIAN ∞³ — Collision Rename Tool")
    print("=" * 60)
    
    repo_root = Path.cwd()
    print(f"Scanning: {repo_root}")
    
    # Find collisions
    collisions = find_collision_files(repo_root)
    
    if not collisions:
        print("\n✓ No collision files found. Repository is clean.")
        return 0
    
    print(f"\nFound {len(collisions)} collision file(s):")
    for file_path, collision_type in collisions:
        rel_path = file_path.relative_to(repo_root)
        print(f"  - [{collision_type}] {rel_path}")
    
    # Move files
    print("\nMoving collision files to backup...")
    report = move_collision_files(collisions, repo_root)
    
    # Summary
    print("\n" + "=" * 60)
    print("SUMMARY")
    print("=" * 60)
    print(f"Files moved: {len(report['moved'])}")
    print(f"Errors: {len(report['errors'])}")
    print(f"Backup location: {report['backup_dir']}")
    
    if report['errors']:
        return 1
    return 0


if __name__ == "__main__":
    exit(main())
