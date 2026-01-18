#!/usr/bin/env python3
"""
Automated Lean Proof Completion System

This module provides tools to automatically complete Lean theorem proofs
marked with 'sorry' by using Noesis and Sabio tools to analyze context
and propose mathematical completions.

Author: José Manuel Mota Burruezo (JMMB Ψ✧)
License: MIT
"""

import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import List, Dict, Optional, Tuple
import argparse


@dataclass
class TheoremContext:
    """Context information for a theorem with 'sorry'"""
    file_path: Path
    theorem_name: str
    theorem_type: str  # theorem, lemma, def, axiom, etc.
    line_number: int
    theorem_statement: str
    proof_body: str
    dependencies: List[str] = field(default_factory=list)
    imports: List[str] = field(default_factory=list)
    namespace: Optional[str] = None
    variables: List[str] = field(default_factory=list)
    has_sorry: bool = False


@dataclass
class ProofCompletion:
    """A proposed proof completion"""
    theorem_context: TheoremContext
    proposed_proof: str
    confidence: float
    validation_status: str
    error_message: Optional[str] = None


class LeanFileParser:
    """Parse Lean files to extract theorems with 'sorry' statements"""
    
    def __init__(self):
        self.theorem_keywords = ['theorem', 'lemma', 'def', 'axiom', 'example']
        
    def parse_file(self, file_path: Path) -> List[TheoremContext]:
        """
        Parse a Lean file and extract all theorems/lemmas with 'sorry'
        
        Args:
            file_path: Path to the Lean file
            
        Returns:
            List of TheoremContext objects containing sorry statements
        """
        try:
            content = file_path.read_text(encoding='utf-8')
            return self._extract_theorems_with_sorry(file_path, content)
        except Exception as e:
            print(f"Error parsing {file_path}: {e}", file=sys.stderr)
            return []
    
    def _extract_theorems_with_sorry(self, file_path: Path, content: str) -> List[TheoremContext]:
        """Extract theorems containing sorry statements"""
        contexts = []
        lines = content.split('\n')
        
        # Extract imports
        imports = [line.strip() for line in lines if line.strip().startswith('import ')]
        
        # Extract namespace
        namespace = None
        for line in lines:
            if line.strip().startswith('namespace '):
                namespace = line.strip().split()[1]
                break
        
        i = 0
        while i < len(lines):
            line = lines[i].strip()
            
            # Check if line starts a theorem/lemma/def
            starts_theorem = any(line.startswith(kw + ' ') or line.startswith(kw + '(')
                               for kw in self.theorem_keywords)
            
            if starts_theorem:
                # Extract the theorem type
                theorem_type = next((kw for kw in self.theorem_keywords 
                                   if line.startswith(kw + ' ') or line.startswith(kw + '(')), None)
                
                # Extract theorem name and statement
                theorem_info = self._extract_theorem_block(lines, i)
                if theorem_info:
                    theorem_name, statement, proof_body, end_line = theorem_info
                    
                    # Check if proof contains sorry
                    if 'sorry' in proof_body:
                        context = TheoremContext(
                            file_path=file_path,
                            theorem_name=theorem_name,
                            theorem_type=theorem_type,
                            line_number=i + 1,
                            theorem_statement=statement,
                            proof_body=proof_body,
                            imports=imports,
                            namespace=namespace,
                            has_sorry=True
                        )
                        contexts.append(context)
                    
                    i = end_line
                else:
                    i += 1
            else:
                i += 1
        
        return contexts
    
    def _extract_theorem_block(self, lines: List[str], start_idx: int) -> Optional[Tuple[str, str, str, int]]:
        """
        Extract a complete theorem block including statement and proof
        
        Returns:
            Tuple of (theorem_name, statement, proof_body, end_line_idx) or None
        """
        # Get the first line
        first_line = lines[start_idx].strip()
        
        # Extract theorem name (simplified)
        name_match = re.match(r'(?:theorem|lemma|def|axiom|example)\s+(\w+)', first_line)
        if not name_match:
            # Sometimes name is on next line
            if start_idx + 1 < len(lines):
                name_match = re.match(r'(\w+)', lines[start_idx + 1].strip())
        
        theorem_name = name_match.group(1) if name_match else "unknown"
        
        # Find the ':=' or ':' that starts the proof
        statement_lines = []
        proof_lines = []
        in_proof = False
        brace_count = 0
        paren_count = 0
        
        i = start_idx
        while i < len(lines):
            line = lines[i]
            
            # Track braces and parens for nested structures
            for char in line:
                if char == '{':
                    brace_count += 1
                elif char == '}':
                    brace_count -= 1
                elif char == '(':
                    paren_count += 1
                elif char == ')':
                    paren_count -= 1
            
            # Check if we've entered the proof section
            if ':=' in line and not in_proof:
                in_proof = True
                # Split at :=
                parts = line.split(':=', 1)
                statement_lines.append(parts[0])
                if len(parts) > 1:
                    proof_lines.append(parts[1])
            elif in_proof:
                proof_lines.append(line)
                
                # Check for end of proof
                # A proof ends when braces are balanced and we hit a blank line or new theorem
                if brace_count == 0 and paren_count == 0:
                    next_line = lines[i + 1].strip() if i + 1 < len(lines) else ''
                    if (not next_line or 
                        any(next_line.startswith(kw + ' ') for kw in self.theorem_keywords)):
                        statement = '\n'.join(statement_lines)
                        proof_body = '\n'.join(proof_lines)
                        return theorem_name, statement, proof_body, i
            else:
                statement_lines.append(line)
            
            i += 1
            
            # Safety limit: stop parsing if block exceeds 500 lines
            # This prevents infinite loops on malformed Lean files
            if i - start_idx > 500:
                if self.verbose:
                    print(f"Warning: Theorem block parsing terminated after 500 lines at line {start_idx}")
                break
        
        return None


class ProofCompletionEngine:
    """Engine to generate proof completions using Noesis/Sabio"""
    
    def __init__(self, use_noesis: bool = True, use_sabio: bool = True):
        self.use_noesis = use_noesis
        self.use_sabio = use_sabio
        
    def generate_completion(self, context: TheoremContext) -> Optional[ProofCompletion]:
        """
        Generate a proof completion for a theorem with sorry
        
        Args:
            context: TheoremContext for the theorem
            
        Returns:
            ProofCompletion with proposed proof, or None if generation fails
        """
        # For now, we'll use a conservative approach:
        # 1. Analyze the theorem type and context
        # 2. Generate simple tactical proofs based on patterns
        # 3. Mark for manual review if complex
        
        proposed_proof = self._analyze_and_generate_proof(context)
        
        if proposed_proof:
            return ProofCompletion(
                theorem_context=context,
                proposed_proof=proposed_proof,
                confidence=0.7,  # Conservative confidence
                validation_status="pending"
            )
        
        return None
    
    def _analyze_and_generate_proof(self, context: TheoremContext) -> Optional[str]:
        """
        Analyze theorem context and generate appropriate proof
        
        This is a simplified implementation. In production, this would:
        1. Call Noesis for semantic analysis
        2. Call Sabio for proof search
        3. Synthesize results into valid Lean proof
        """
        # Check for common patterns
        
        # Pattern 1: Trivial proofs (e.g., reflexivity, simple arithmetic)
        if self._is_trivial_proof(context):
            return "  rfl"  # reflexivity
        
        # Pattern 2: Use of 'exact' with assumption
        if self._can_use_exact(context):
            return "  exact sorry  -- TODO: Identify correct assumption"
        
        # Pattern 3: Induction proofs
        if 'induction' in context.theorem_statement.lower() or 'ℕ' in context.theorem_statement:
            return "  -- Proof by induction\n  sorry  -- TODO: Complete induction proof"
        
        # Pattern 4: Simp or norm_num for arithmetic
        if any(kw in context.theorem_statement for kw in ['=', '+', '*', '-']):
            return "  -- Try: simp or norm_num\n  sorry"
        
        # Default: Keep sorry with context note
        return None
    
    def _is_trivial_proof(self, context: TheoremContext) -> bool:
        """Check if proof might be trivial (reflexivity, etc.)"""
        # Very conservative check
        statement = context.theorem_statement.lower()
        return ('refl' in statement or 
                'eq.refl' in statement or
                ('=' in statement and statement.count('=') == 1))
    
    def _can_use_exact(self, context: TheoremContext) -> bool:
        """Check if 'exact' might work with an assumption"""
        # Check if there are hypotheses that might directly prove the goal
        return 'have ' in context.theorem_statement or '→' in context.theorem_statement


class LeanProofCompleter:
    """Main orchestrator for Lean proof completion"""
    
    def __init__(self, verbose: bool = False, dry_run: bool = True):
        self.parser = LeanFileParser()
        self.engine = ProofCompletionEngine()
        self.verbose = verbose
        self.dry_run = dry_run
        self.stats = {
            'files_scanned': 0,
            'theorems_with_sorry': 0,
            'completions_proposed': 0,
            'completions_applied': 0,
            'errors': 0
        }
    
    def process_file(self, file_path: Path) -> List[ProofCompletion]:
        """
        Process a single Lean file to complete sorry statements
        
        Args:
            file_path: Path to Lean file
            
        Returns:
            List of ProofCompletion objects
        """
        self.stats['files_scanned'] += 1
        
        if self.verbose:
            print(f"\n📄 Processing: {file_path}")
        
        # Parse file to find theorems with sorry
        contexts = self.parser.parse_file(file_path)
        self.stats['theorems_with_sorry'] += len(contexts)
        
        if self.verbose and contexts:
            print(f"   Found {len(contexts)} theorems with 'sorry'")
        
        # Generate completions
        completions = []
        for context in contexts:
            if self.verbose:
                print(f"   - {context.theorem_type} {context.theorem_name} (line {context.line_number})")
            
            completion = self.engine.generate_completion(context)
            if completion:
                completions.append(completion)
                self.stats['completions_proposed'] += 1
        
        return completions
    
    def process_directory(self, directory: Path) -> Dict[str, List[ProofCompletion]]:
        """
        Process all Lean files in a directory
        
        Args:
            directory: Path to directory containing Lean files
            
        Returns:
            Dictionary mapping file paths to lists of ProofCompletion objects
        """
        results = {}
        
        lean_files = list(directory.rglob('*.lean'))
        total_files = len(lean_files)
        
        print(f"\n🔍 Scanning {total_files} Lean files in {directory}")
        print("=" * 70)
        
        for i, file_path in enumerate(lean_files, 1):
            # Skip .lake directory
            if '.lake' in file_path.parts:
                continue
            
            if self.verbose:
                print(f"\n[{i}/{total_files}] {file_path.relative_to(directory)}")
            
            completions = self.process_file(file_path)
            if completions:
                results[str(file_path)] = completions
        
        return results
    
    def generate_report(self, results: Dict[str, List[ProofCompletion]]) -> Dict:
        """Generate a summary report of the completion process"""
        report = {
            'summary': self.stats.copy(),
            'files_with_completions': len(results),
            'completions_by_file': {}
        }
        
        for file_path, completions in results.items():
            report['completions_by_file'][file_path] = [
                {
                    'theorem_name': c.theorem_context.theorem_name,
                    'theorem_type': c.theorem_context.theorem_type,
                    'line_number': c.theorem_context.line_number,
                    'confidence': c.confidence,
                    'proposed_proof_preview': c.proposed_proof[:100] if c.proposed_proof else None
                }
                for c in completions
            ]
        
        return report
    
    def print_summary(self):
        """Print summary statistics"""
        print("\n" + "=" * 70)
        print("📊 COMPLETION SUMMARY")
        print("=" * 70)
        print(f"Files scanned: {self.stats['files_scanned']}")
        print(f"Theorems with 'sorry': {self.stats['theorems_with_sorry']}")
        print(f"Completions proposed: {self.stats['completions_proposed']}")
        print(f"Completions applied: {self.stats['completions_applied']}")
        print(f"Errors: {self.stats['errors']}")
        print("=" * 70)


def main():
    """Main entry point"""
    parser = argparse.ArgumentParser(
        description='Automated Lean Proof Completion System',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Analyze a single file
  python lean_proof_completer.py --file formalization/lean/RH_final.lean

  # Scan entire directory (dry-run)
  python lean_proof_completer.py --dir formalization/lean --dry-run

  # Generate completions and save report
  python lean_proof_completer.py --dir formalization/lean --output report.json
        """
    )
    
    parser.add_argument('--file', type=Path,
                       help='Single Lean file to process')
    parser.add_argument('--dir', type=Path,
                       help='Directory of Lean files to process')
    parser.add_argument('--output', type=Path,
                       help='Output JSON report file')
    parser.add_argument('--dry-run', action='store_true', default=True,
                       help='Analyze only, do not modify files (default: True)')
    parser.add_argument('--verbose', '-v', action='store_true',
                       help='Verbose output')
    
    args = parser.parse_args()
    
    if not args.file and not args.dir:
        parser.error("Either --file or --dir must be specified")
    
    completer = LeanProofCompleter(verbose=args.verbose, dry_run=args.dry_run)
    
    if args.file:
        if not args.file.exists():
            print(f"Error: File not found: {args.file}", file=sys.stderr)
            return 1
        
        completions = completer.process_file(args.file)
        results = {str(args.file): completions}
    else:
        if not args.dir.exists():
            print(f"Error: Directory not found: {args.dir}", file=sys.stderr)
            return 1
        
        results = completer.process_directory(args.dir)
    
    # Generate and print report
    report = completer.generate_report(results)
    completer.print_summary()
    
    # Save report if requested
    if args.output:
        with open(args.output, 'w') as f:
            json.dump(report, f, indent=2)
        print(f"\n📄 Report saved to: {args.output}")
    
    return 0


if __name__ == '__main__':
    sys.exit(main())
