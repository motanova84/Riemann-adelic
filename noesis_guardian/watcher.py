#!/usr/bin/env python3
"""
Repository Watcher Module for NOESIS GUARDIAN ∞³

This module scans the repository for:
- Collisions (duplicate or conflicting files)
- Missing essential files
- Lean environment status
- Unicode corruption issues

Author: José Manuel Mota Burruezo (JMMB Ψ ✧)
"""

import os
import re
import subprocess
from pathlib import Path
from typing import Dict, List, Any


# Configuration constants
SORRY_THRESHOLD = 10  # Maximum number of 'sorry' statements before Lean is marked incomplete
MAX_UNICODE_ISSUES = 100  # Maximum number of Unicode issues to report


class RepoWatcher:
    """
    Repository watcher that monitors QCAL repository health.
    
    Scans for:
    - File collisions (duplicate names, merge conflicts)
    - Missing essential modules
    - Lean formalization status
    - Unicode corruption in Python/Lean files
    """
    
    def __init__(self, repo_root: str = None):
        """
        Initialize the repository watcher.
        
        Args:
            repo_root: Root directory of the repository. 
                      If None, uses current working directory.
        """
        if repo_root is None:
            repo_root = os.getcwd()
        self.repo_root = Path(repo_root)
        
        # Essential files for QCAL framework
        self.essential_files = [
            "validate_v5_coronacion.py",
            "demo_H_DS_complete.py",
            "validate_h_psi_self_adjoint.py",
            "validate_critical_line.py",
            "operador/operador_H_DS.py",
            "operador/operador_H.py",
            "operador/hilbert_polya_operator.py",
            "fix_unicode.py",
            ".qcal_beacon",
            "Evac_Rpsi_data.csv",
        ]
        
        # Lean formalization files
        self.lean_files = [
            "formalization/lean/RiemannHypothesis.lean",
            "formalization/lean/lakefile.lean",
        ]
        
        # Unicode patterns that may indicate corruption
        self.unicode_corruption_patterns = [
            r'[\x00-\x08\x0b\x0c\x0e-\x1f]',  # Control characters
            r'[\ufffd]',  # Replacement character
            r'[\x80-\x9f]',  # C1 control codes
        ]
    
    def scan_repo(self) -> Dict[str, Any]:
        """
        Perform a complete repository scan.
        
        Returns:
            dict: State containing collisions, lean_status, missing count, and details
        """
        state = {
            "collisions": 0,
            "lean_status": "unknown",
            "missing": 0,
            "collision_details": [],
            "missing_files": [],
            "unicode_issues": [],
            "scan_complete": False
        }
        
        # Check for collisions
        collision_result = self._check_collisions()
        state["collisions"] = collision_result["count"]
        state["collision_details"] = collision_result["details"]
        
        # Check Lean status
        state["lean_status"] = self._check_lean_status()
        
        # Check for missing files
        missing_result = self._check_missing_files()
        state["missing"] = missing_result["count"]
        state["missing_files"] = missing_result["files"]
        
        # Check for Unicode issues
        unicode_result = self._check_unicode_issues()
        state["unicode_issues"] = unicode_result
        
        state["scan_complete"] = True
        return state
    
    def _check_collisions(self) -> Dict[str, Any]:
        """
        Check for file collisions in the repository.
        
        Looks for:
        - Merge conflict markers
        - Duplicate file patterns (file.py.orig, file.py.bak)
        - .orig files from conflict resolution
        """
        collisions = []
        
        # Walk through repository
        for root, dirs, files in os.walk(self.repo_root):
            # Skip .git and node_modules
            dirs[:] = [d for d in dirs if d not in ['.git', 'node_modules', '__pycache__', '.venv']]
            
            for file in files:
                file_path = Path(root) / file
                rel_path = file_path.relative_to(self.repo_root)
                
                # Check for backup/conflict files
                if file.endswith(('.orig', '.bak', '.backup', '.conflict')):
                    collisions.append({
                        "type": "backup_file",
                        "path": str(rel_path)
                    })
                
                # Check for merge conflict markers in text files
                if file.endswith(('.py', '.lean', '.md', '.txt', '.json')):
                    if self._has_merge_conflicts(file_path):
                        collisions.append({
                            "type": "merge_conflict",
                            "path": str(rel_path)
                        })
        
        return {
            "count": len(collisions),
            "details": collisions
        }
    
    def _has_merge_conflicts(self, file_path: Path) -> bool:
        """Check if a file contains merge conflict markers."""
        try:
            with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
                content = f.read()
                # Look for Git merge conflict markers - require all three markers
                # to be present (start, separator, and end)
                has_start = '<<<<<<< ' in content
                has_separator = '\n=======' in content or content.startswith('=======')
                has_end = '>>>>>>> ' in content
                
                # Must have all three markers to be a real conflict
                if has_start and has_separator and has_end:
                    # Additional check: ensure markers appear in order at line starts
                    lines = content.split('\n')
                    start_found = False
                    separator_found = False
                    for line in lines:
                        if line.startswith('<<<<<<< '):
                            start_found = True
                        elif line == '=======' and start_found:
                            separator_found = True
                        elif line.startswith('>>>>>>> ') and separator_found:
                            return True
        except Exception:
            pass
        return False
    
    def _check_lean_status(self) -> str:
        """
        Check the status of the Lean formalization environment.
        
        Returns:
            str: 'ok', 'broken', or 'missing'
        """
        lean_dir = self.repo_root / "formalization" / "lean"
        
        # Check if Lean directory exists
        if not lean_dir.exists():
            return "missing"
        
        # Check for lakefile
        lakefile = lean_dir / "lakefile.lean"
        if not lakefile.exists():
            # Try lakefile.toml as alternative
            lakefile_toml = lean_dir / "lakefile.toml"
            if not lakefile_toml.exists():
                return "broken"
        
        # Check for main RH Lean file
        rh_lean = lean_dir / "RiemannHypothesis.lean"
        if not rh_lean.exists():
            # Check for alternative paths
            for alt in ["RH.lean", "Main.lean", "QCAL.lean"]:
                if (lean_dir / alt).exists():
                    return "ok"
            return "broken"
        
        # Verify Lean file is valid (no sorry statements unless expected)
        try:
            with open(rh_lean, 'r', encoding='utf-8') as f:
                content = f.read()
                # Count sorry statements (incomplete proofs)
                sorry_count = content.count('sorry')
                if sorry_count > SORRY_THRESHOLD:
                    return "incomplete"
        except Exception:
            return "broken"
        
        return "ok"
    
    def _check_missing_files(self) -> Dict[str, Any]:
        """Check for missing essential files."""
        missing = []
        
        for essential in self.essential_files:
            file_path = self.repo_root / essential
            if not file_path.exists():
                missing.append(essential)
        
        return {
            "count": len(missing),
            "files": missing
        }
    
    def _check_unicode_issues(self) -> List[Dict[str, str]]:
        """
        Check for Unicode corruption in source files.
        
        Returns:
            list: Files with potential Unicode issues
        """
        issues = []
        
        extensions = ['.py', '.lean', '.md', '.txt']
        
        for ext in extensions:
            for file_path in self.repo_root.rglob(f'*{ext}'):
                # Skip hidden directories and node_modules
                if '.git' in str(file_path) or 'node_modules' in str(file_path):
                    continue
                
                try:
                    with open(file_path, 'rb') as f:
                        raw_content = f.read()
                    
                    # Try to decode as UTF-8
                    try:
                        content = raw_content.decode('utf-8')
                        
                        # Check for corruption patterns
                        for pattern in self.unicode_corruption_patterns:
                            if re.search(pattern, content):
                                rel_path = file_path.relative_to(self.repo_root)
                                issues.append({
                                    "path": str(rel_path),
                                    "issue": "unicode_corruption"
                                })
                                break
                    except UnicodeDecodeError:
                        rel_path = file_path.relative_to(self.repo_root)
                        issues.append({
                            "path": str(rel_path),
                            "issue": "decode_error"
                        })
                except Exception:
                    pass
        
        return issues[:MAX_UNICODE_ISSUES]  # Limit reported issues
    
    def get_summary(self) -> str:
        """
        Get a human-readable summary of the repository state.
        
        Returns:
            str: Summary text
        """
        state = self.scan_repo()
        
        lines = [
            "=" * 60,
            "NOESIS GUARDIAN ∞³ — Repository Status",
            "=" * 60,
            f"Collisions:     {state['collisions']}",
            f"Lean Status:    {state['lean_status']}",
            f"Missing Files:  {state['missing']}",
            f"Unicode Issues: {len(state['unicode_issues'])}",
            "=" * 60,
        ]
        
        if state['collision_details']:
            lines.append("\nCollision Details:")
            for collision in state['collision_details'][:10]:
                lines.append(f"  - {collision['type']}: {collision['path']}")
        
        if state['missing_files']:
            lines.append("\nMissing Files:")
            for missing in state['missing_files']:
                lines.append(f"  - {missing}")
        
        return "\n".join(lines)


def main():
    """Run repository scan and print summary."""
    watcher = RepoWatcher()
    print(watcher.get_summary())


if __name__ == "__main__":
    main()
