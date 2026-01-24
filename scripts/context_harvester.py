#!/usr/bin/env python3
"""
Context-Aware Harvester - Extract Mathematical Context for Lean Proof Generation

This module extracts mathematical derivations, constants, and context from Python
modules and Markdown documentation to support automated proof generation in Lean4.

Part of the Phoenix Solver system for automated sorry resolution.

Author: QCAL Phoenix Solver System
Date: 2026-01-18
"""

import re
import json
from pathlib import Path
from typing import Dict, List, Optional, Tuple, Any
from dataclasses import dataclass, asdict


@dataclass
class MathematicalConstant:
    """Represents a mathematical constant with its derivation."""
    name: str
    value: float
    description: str
    source_file: str
    derivation: Optional[str] = None
    precision: Optional[int] = None


@dataclass
class SorryStatement:
    """Represents a sorry statement in a Lean file."""
    file_path: str
    line_number: int
    lemma_name: str
    context: str
    theorem_statement: str
    dependencies: List[str]


@dataclass
class MathematicalContext:
    """Complete mathematical context for proof generation."""
    constants: Dict[str, MathematicalConstant]
    derivations: List[str]
    related_theorems: List[str]
    python_implementations: List[str]


class ContextHarvester:
    """Harvest mathematical context from Python and Markdown files."""
    
    def __init__(self, repo_root: Path):
        """Initialize the harvester.
        
        Args:
            repo_root: Root directory of the repository
        """
        self.repo_root = Path(repo_root)
        self.constants: Dict[str, MathematicalConstant] = {}
        self.derivations: List[str] = []
        
    def scan_lean_files(self) -> List[SorryStatement]:
        """Scan Lean files for sorry statements.
        
        Returns:
            List of SorryStatement objects found in Lean files
        """
        sorry_statements = []
        formalization_dir = self.repo_root / "formalization" / "lean"
        
        if not formalization_dir.exists():
            return sorry_statements
            
        for lean_file in formalization_dir.rglob("*.lean"):
            sorrys = self._extract_sorrys_from_file(lean_file)
            sorry_statements.extend(sorrys)
            
        return sorry_statements
    
    def _extract_sorrys_from_file(self, file_path: Path) -> List[SorryStatement]:
        """Extract sorry statements from a single Lean file.
        
        Args:
            file_path: Path to the Lean file
            
        Returns:
            List of SorryStatement objects
        """
        sorrys = []
        
        try:
            content = file_path.read_text(encoding='utf-8')
            lines = content.split('\n')
            
            for i, line in enumerate(lines):
                if 'sorry' in line.lower():
                    # Extract context (previous 20 lines)
                    context_start = max(0, i - 20)
                    context_lines = lines[context_start:i+1]
                    context = '\n'.join(context_lines)
                    
                    # Try to extract lemma/theorem name
                    lemma_name = self._extract_lemma_name(context_lines)
                    
                    # Extract theorem statement
                    theorem_stmt = self._extract_theorem_statement(context_lines)
                    
                    sorry_stmt = SorryStatement(
                        file_path=str(file_path.relative_to(self.repo_root)),
                        line_number=i + 1,
                        lemma_name=lemma_name,
                        context=context,
                        theorem_statement=theorem_stmt,
                        dependencies=[]
                    )
                    sorrys.append(sorry_stmt)
                    
        except Exception as e:
            print(f"Error processing {file_path}: {e}")
            
        return sorrys
    
    def _extract_lemma_name(self, lines: List[str]) -> str:
        """Extract lemma/theorem name from context lines."""
        for line in reversed(lines):
            # Match theorem, lemma, def patterns
            match = re.search(r'(theorem|lemma|def)\s+([a-zA-Z_][a-zA-Z0-9_]*)', line)
            if match:
                return match.group(2)
        return "unknown"
    
    def _extract_theorem_statement(self, lines: List[str]) -> str:
        """Extract the theorem statement from context lines."""
        # Look for theorem/lemma declaration
        theorem_lines = []
        in_theorem = False
        
        for line in lines:
            if re.search(r'(theorem|lemma|def)\s+', line):
                in_theorem = True
            if in_theorem:
                theorem_lines.append(line)
                if ':=' in line or 'by' in line:
                    break
                    
        return '\n'.join(theorem_lines)
    
    def extract_constants(self) -> Dict[str, MathematicalConstant]:
        """Extract mathematical constants from Python and Markdown files.
        
        Returns:
            Dictionary of constant name to MathematicalConstant
        """
        # Extract from key files
        self._extract_qcal_constants()
        self._extract_frequency_constants()
        self._extract_from_lean_files()
        
        return self.constants
    
    def _extract_qcal_constants(self):
        """Extract QCAL constants from .qcal_beacon file."""
        beacon_file = self.repo_root / ".qcal_beacon"
        
        if beacon_file.exists():
            try:
                content = beacon_file.read_text()
                
                # Extract coherence constant C
                c_match = re.search(r'C\s*=\s*([\d.]+)', content)
                if c_match:
                    self.constants['C'] = MathematicalConstant(
                        name='C',
                        value=float(c_match.group(1)),
                        description='QCAL Coherence Constant',
                        source_file='.qcal_beacon',
                        derivation='C = I × A_eff²'
                    )
                    
                # Extract frequency
                freq_match = re.search(r'frequency[_\s]*=\s*([\d.]+)', content, re.IGNORECASE)
                if freq_match:
                    self.constants['f0'] = MathematicalConstant(
                        name='f0',
                        value=float(freq_match.group(1)),
                        description='Base Frequency (Hz)',
                        source_file='.qcal_beacon',
                        precision=4
                    )
                    
            except Exception as e:
                print(f"Error reading .qcal_beacon: {e}")
    
    def _extract_frequency_constants(self):
        """Extract frequency constants from derivation markdown."""
        freq_file = self.repo_root / "FUNDAMENTAL_FREQUENCY_DERIVATION.md"
        
        if freq_file.exists():
            try:
                content = freq_file.read_text()
                
                # Extract high-precision frequency
                freq_match = re.search(r'f₀\s*=\s*([\d.]+)', content)
                if freq_match and 'f0' not in self.constants:
                    self.constants['f0'] = MathematicalConstant(
                        name='f0',
                        value=float(freq_match.group(1)),
                        description='Fundamental Frequency from spectral derivation',
                        source_file='FUNDAMENTAL_FREQUENCY_DERIVATION.md',
                        precision=15
                    )
                    
                # Extract zeta derivative
                zeta_match = re.search(r"ζ'\\(1/2\\)\s*≈\s*([-\d.]+)", content)
                if zeta_match:
                    self.constants['zeta_half_deriv'] = MathematicalConstant(
                        name='zeta_half_deriv',
                        value=float(zeta_match.group(1)),
                        description="ζ'(1/2) - Zeta derivative at critical point",
                        source_file='FUNDAMENTAL_FREQUENCY_DERIVATION.md',
                        precision=8
                    )
                    
            except Exception as e:
                print(f"Error reading frequency derivation: {e}")
    
    def _extract_from_lean_files(self):
        """Extract constants defined in Lean files."""
        lean_file = self.repo_root / "formalization" / "lean" / "RIGOROUS_UNIQUENESS_EXACT_LAW.lean"
        
        if lean_file.exists():
            try:
                content = lean_file.read_text()
                
                # Extract QCAL_frequency
                freq_match = re.search(r'def\s+QCAL_frequency\s*:\s*ℝ\s*:=\s*([\d.]+)', content)
                if freq_match:
                    self.constants['QCAL_frequency'] = MathematicalConstant(
                        name='QCAL_frequency',
                        value=float(freq_match.group(1)),
                        description='QCAL frequency (Hz) in Lean',
                        source_file='formalization/lean/RIGOROUS_UNIQUENESS_EXACT_LAW.lean'
                    )
                    
                # Extract QCAL_coherence
                coh_match = re.search(r'def\s+QCAL_coherence\s*:\s*ℝ\s*:=\s*([\d.]+)', content)
                if coh_match:
                    self.constants['QCAL_coherence'] = MathematicalConstant(
                        name='QCAL_coherence',
                        value=float(coh_match.group(1)),
                        description='QCAL coherence constant in Lean',
                        source_file='formalization/lean/RIGOROUS_UNIQUENESS_EXACT_LAW.lean'
                    )
                    
            except Exception as e:
                print(f"Error reading Lean file: {e}")
    
    def build_context_for_sorry(self, sorry: SorryStatement) -> MathematicalContext:
        """Build complete mathematical context for a sorry statement.
        
        Args:
            sorry: The sorry statement to build context for
            
        Returns:
            MathematicalContext with relevant information
        """
        # Find related Python implementations
        python_files = self._find_related_python_files(sorry.lemma_name)
        
        # Find related theorems
        related = self._find_related_theorems(sorry.file_path)
        
        context = MathematicalContext(
            constants=self.constants,
            derivations=self.derivations,
            related_theorems=related,
            python_implementations=python_files
        )
        
        return context
    
    def _find_related_python_files(self, lemma_name: str) -> List[str]:
        """Find Python files related to a lemma name."""
        related = []
        
        # Search for files with similar names
        name_parts = lemma_name.lower().split('_')
        
        for py_file in self.repo_root.glob("**/*.py"):
            if any(part in py_file.name.lower() for part in name_parts if len(part) > 3):
                related.append(str(py_file.relative_to(self.repo_root)))
                
        return related[:5]  # Limit to top 5
    
    def _find_related_theorems(self, lean_file: str) -> List[str]:
        """Find related theorems in the same Lean file."""
        related = []
        file_path = self.repo_root / lean_file
        
        try:
            if file_path.exists():
                content = file_path.read_text()
                # Extract theorem/lemma names
                matches = re.finditer(r'(theorem|lemma)\s+([a-zA-Z_][a-zA-Z0-9_]*)', content)
                for match in matches:
                    related.append(match.group(2))
        except Exception:
            pass
            
        return related
    
    def generate_quantum_prompt(self, sorry: SorryStatement, context: MathematicalContext) -> str:
        """Generate a quantum engineering prompt for AI proof generation.
        
        Args:
            sorry: The sorry statement to generate prompt for
            context: Mathematical context
            
        Returns:
            Formatted prompt string for AI assistants
        """
        prompt_parts = []
        
        # Header
        prompt_parts.append("# Quantum Engineering Proof Prompt")
        prompt_parts.append(f"\nFile: {sorry.file_path}")
        prompt_parts.append(f"Lemma: {sorry.lemma_name}")
        prompt_parts.append(f"Line: {sorry.line_number}\n")
        
        # Theorem statement
        prompt_parts.append("## Theorem Statement")
        prompt_parts.append("```lean")
        prompt_parts.append(sorry.theorem_statement)
        prompt_parts.append("```\n")
        
        # Mathematical constants
        if context.constants:
            prompt_parts.append("## QCAL Constants")
            for name, const in context.constants.items():
                prompt_parts.append(f"- **{name}** = {const.value}")
                prompt_parts.append(f"  {const.description}")
                if const.derivation:
                    prompt_parts.append(f"  Derivation: {const.derivation}")
            prompt_parts.append("")
        
        # Context
        prompt_parts.append("## Context")
        prompt_parts.append("```lean")
        prompt_parts.append(sorry.context)
        prompt_parts.append("```\n")
        
        # Related implementations
        if context.python_implementations:
            prompt_parts.append("## Related Python Implementations")
            for py_file in context.python_implementations:
                prompt_parts.append(f"- {py_file}")
            prompt_parts.append("")
        
        # Related theorems
        if context.related_theorems:
            prompt_parts.append("## Related Theorems in File")
            for thm in context.related_theorems[:10]:
                prompt_parts.append(f"- {thm}")
            prompt_parts.append("")
        
        # Instructions
        prompt_parts.append("## Task")
        prompt_parts.append("Generate a rigorous Lean4 proof for this sorry statement.")
        prompt_parts.append("The proof must:")
        prompt_parts.append("1. Compile without errors in Lean4")
        prompt_parts.append("2. Use only available Mathlib tactics")
        prompt_parts.append("3. Respect QCAL coherence (C = 244.36, f₀ = 141.7001 Hz)")
        prompt_parts.append("4. Maintain mathematical rigor")
        prompt_parts.append("5. Include clear comments explaining key steps\n")
        
        return '\n'.join(prompt_parts)
    
    def export_sorry_report(self, output_path: Path):
        """Export a complete sorry statement report.
        
        Args:
            output_path: Path to write the JSON report
        """
        sorrys = self.scan_lean_files()
        constants = self.extract_constants()
        
        report = {
            'timestamp': str(Path(__file__).stat().st_mtime),
            'total_sorrys': len(sorrys),
            'files_with_sorrys': len(set(s.file_path for s in sorrys)),
            'constants': {name: asdict(const) for name, const in constants.items()},
            'sorry_statements': [asdict(s) for s in sorrys[:100]]  # First 100 for size
        }
        
        output_path.write_text(json.dumps(report, indent=2))
        print(f"Report exported to {output_path}")
        print(f"Total sorry statements found: {len(sorrys)}")


def main():
    """Main entry point for the context harvester."""
    import argparse
    
    parser = argparse.ArgumentParser(description='Harvest mathematical context for Lean proofs')
    parser.add_argument('--repo-root', type=Path, default=Path.cwd(),
                       help='Repository root directory')
    parser.add_argument('--export', type=Path,
                       help='Export sorry report to JSON file')
    parser.add_argument('--show-constants', action='store_true',
                       help='Show extracted constants')
    
    args = parser.parse_args()
    
    harvester = ContextHarvester(args.repo_root)
    
    if args.show_constants:
        constants = harvester.extract_constants()
        print("\n=== Extracted Mathematical Constants ===\n")
        for name, const in constants.items():
            print(f"{name}: {const.value}")
            print(f"  {const.description}")
            print(f"  Source: {const.source_file}")
            if const.derivation:
                print(f"  Derivation: {const.derivation}")
            print()
    
    if args.export:
        harvester.export_sorry_report(args.export)


if __name__ == '__main__':
    main()
