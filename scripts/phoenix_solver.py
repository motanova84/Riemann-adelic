#!/usr/bin/env python3
"""
Phoenix Solver - Automated Sorry Resolution System

This is the main orchestration script for the QCAL Phoenix Solver system.
It coordinates the resolution of 'sorry' statements in Lean4 formalization
through an automated pipeline:

1. Context-Aware Harvester: Extract mathematical context
2. Lean-REPL Sandbox: Test and validate proofs
3. Coherence Validator: Ensure QCAL integrity
4. Documentation Updater: Keep status files current

Author: QCAL Phoenix Solver System
Date: 2026-01-18

Usage:
    python scripts/phoenix_solver.py [options]
    
Options:
    --priority-file FILE    Focus on a specific Lean file
    --max-sorrys N         Maximum number of sorrys to resolve
    --batch-size N         Number of sorrys per validation batch
    --dry-run              Show plan without making changes
"""

import sys
import json
from pathlib import Path
from typing import List, Optional, Dict, Tuple
from dataclasses import dataclass
import argparse
from datetime import datetime

# Add scripts directory to path
REPO_ROOT = Path(__file__).parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts"))

from context_harvester import ContextHarvester, SorryStatement, MathematicalContext
from lean_sandbox import LeanSandbox, CompilationResult
from coherence_validator import CoherenceValidator, CoherenceResult


@dataclass
class ResolutionResult:
    """Result of sorry resolution attempt."""
    sorry: SorryStatement
    success: bool
    proof_code: Optional[str] = None
    compilation_result: Optional[CompilationResult] = None
    iterations: int = 0
    error_message: Optional[str] = None


class PhoenixSolver:
    """Main orchestration class for automated sorry resolution."""
    
    def __init__(self, repo_root: Path):
        """Initialize the Phoenix Solver.
        
        Args:
            repo_root: Root directory of the repository
        """
        self.repo_root = Path(repo_root)
        self.harvester = ContextHarvester(repo_root)
        self.sandbox = LeanSandbox()
        self.validator = CoherenceValidator(repo_root)
        
        # Statistics
        self.stats = {
            'total_sorrys': 0,
            'resolved': 0,
            'failed': 0,
            'skipped': 0,
            'validation_failures': 0
        }
        
    def scan_repository(self) -> List[SorryStatement]:
        """Scan repository for all sorry statements.
        
        Returns:
            List of SorryStatement objects
        """
        print("🔍 Scanning repository for sorry statements...")
        sorrys = self.harvester.scan_lean_files()
        self.stats['total_sorrys'] = len(sorrys)
        print(f"Found {len(sorrys)} sorry statements in {len(set(s.file_path for s in sorrys))} files")
        return sorrys
    
    def prioritize_sorrys(self, sorrys: List[SorryStatement], 
                         priority_file: Optional[str] = None) -> List[SorryStatement]:
        """Prioritize sorry statements for resolution.
        
        Args:
            sorrys: List of all sorry statements
            priority_file: Optional specific file to prioritize
            
        Returns:
            Sorted list of sorry statements
        """
        print("\n📊 Prioritizing sorry statements...")
        
        # Priority 1: Specific file if requested
        if priority_file:
            priority_sorrys = [s for s in sorrys if priority_file in s.file_path]
            other_sorrys = [s for s in sorrys if priority_file not in s.file_path]
            
            print(f"Priority file: {priority_file}")
            print(f"  - {len(priority_sorrys)} sorrys in priority file")
            print(f"  - {len(other_sorrys)} sorrys in other files")
            
            return priority_sorrys + other_sorrys
        
        # Priority 2: RIGOROUS_UNIQUENESS_EXACT_LAW.lean (critical file)
        critical_file = "RIGOROUS_UNIQUENESS_EXACT_LAW.lean"
        critical_sorrys = [s for s in sorrys if critical_file in s.file_path]
        
        # Priority 3: Files with fewer sorrys (easier to complete)
        from collections import Counter
        file_counts = Counter(s.file_path for s in sorrys)
        
        remaining = [s for s in sorrys if critical_file not in s.file_path]
        remaining.sort(key=lambda s: file_counts[s.file_path])
        
        print(f"Prioritization:")
        print(f"  1. Critical file ({critical_file}): {len(critical_sorrys)} sorrys")
        print(f"  2. Other files (sorted by count): {len(remaining)} sorrys")
        
        return critical_sorrys + remaining
    
    def resolve_sorry(self, sorry: SorryStatement) -> ResolutionResult:
        """Attempt to resolve a single sorry statement.
        
        Args:
            sorry: The sorry statement to resolve
            
        Returns:
            ResolutionResult with resolution status
        """
        print(f"\n{'='*70}")
        print(f"Resolving sorry in {sorry.file_path}:{sorry.line_number}")
        print(f"Lemma: {sorry.lemma_name}")
        print(f"{'='*70}")
        
        # Step 1: Build mathematical context
        print("\n1️⃣ Extracting mathematical context...")
        context = self.harvester.build_context_for_sorry(sorry)
        
        # Step 2: Generate quantum engineering prompt
        print("2️⃣ Generating quantum engineering prompt...")
        prompt = self.harvester.generate_quantum_prompt(sorry, context)
        
        # Save prompt for reference
        prompt_file = REPO_ROOT / "data" / "prompts" / f"{sorry.lemma_name}_prompt.md"
        prompt_file.parent.mkdir(parents=True, exist_ok=True)
        prompt_file.write_text(prompt)
        print(f"   Prompt saved to: {prompt_file}")
        
        # Step 3: For now, we note that AI proof generation would happen here
        print("\n3️⃣ AI Proof Generation...")
        print("   ⚠️  AI proof generation requires integration with:")
        print("      - GitHub Copilot Noesis API")
        print("      - Or GPT-4 / Claude with code generation")
        print("   📝 Prompt ready for manual review or API integration")
        
        # For now, return a placeholder result
        return ResolutionResult(
            sorry=sorry,
            success=False,
            proof_code=None,
            compilation_result=None,
            iterations=0,
            error_message="AI integration not yet implemented - proof generation requires API setup"
        )
    
    def validate_batch(self, resolved_sorrys: List[ResolutionResult]) -> CoherenceResult:
        """Validate a batch of resolved sorrys.
        
        Args:
            resolved_sorrys: List of resolution results
            
        Returns:
            CoherenceResult from validation
        """
        print(f"\n{'='*70}")
        print(f"🔍 Validating batch of {len(resolved_sorrys)} resolutions")
        print(f"{'='*70}")
        
        result = self.validator.validate()
        
        if not result.success:
            print("❌ Validation FAILED")
            print("   Coherence Ψ:", result.coherence_psi)
            print("   Frequency:", result.frequency)
            if result.errors:
                print("   Errors:")
                for error in result.errors:
                    print(f"     - {error}")
        else:
            print("✅ Validation PASSED")
            print(f"   Coherence Ψ: {result.coherence_psi:.6f}")
            print(f"   Frequency: {result.frequency:.4f} Hz")
        
        return result
    
    def update_documentation(self, resolved_count: int):
        """Update FORMALIZATION_STATUS.md and README.
        
        Args:
            resolved_count: Number of sorrys resolved
        """
        print("\n📝 Updating documentation...")
        
        formalization_status = REPO_ROOT / "FORMALIZATION_STATUS.md"
        
        if formalization_status.exists():
            content = formalization_status.read_text()
            
            # Update sorry count (this is a placeholder - real implementation would be more sophisticated)
            timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
            
            update_note = f"\n## Phoenix Solver Update ({timestamp})\n\n"
            update_note += f"- Resolved {resolved_count} sorry statements\n"
            update_note += f"- Current sorry count: {self.stats['total_sorrys'] - resolved_count}\n"
            update_note += f"- Validation status: {'✅ PASS' if self.stats['validation_failures'] == 0 else '❌ FAIL'}\n"
            
            # Prepend update (in real implementation, we'd update specific sections)
            updated_content = update_note + "\n" + content
            
            # For now, just log what we would do
            print("   Would update FORMALIZATION_STATUS.md with:")
            print(update_note)
        else:
            print("   ⚠️  FORMALIZATION_STATUS.md not found")
    
    def run(self, max_sorrys: Optional[int] = None,
            batch_size: int = 10,
            priority_file: Optional[str] = None,
            dry_run: bool = False) -> Dict:
        """Run the complete Phoenix Solver pipeline.
        
        Args:
            max_sorrys: Maximum number of sorrys to resolve (None = all)
            batch_size: Number of sorrys to resolve before validation
            priority_file: Optional specific file to focus on
            dry_run: If True, show plan without making changes
            
        Returns:
            Dictionary with run statistics
        """
        print("\n" + "="*70)
        print("🔥 PHOENIX SOLVER - QCAL Sorry Resolution System")
        print("="*70)
        
        if dry_run:
            print("\n⚠️  DRY RUN MODE - No changes will be made\n")
        
        # Step 1: Scan repository
        all_sorrys = self.scan_repository()
        
        if not all_sorrys:
            print("\n✅ No sorry statements found! Repository is complete.")
            return self.stats
        
        # Step 2: Prioritize
        prioritized = self.prioritize_sorrys(all_sorrys, priority_file)
        
        # Step 3: Limit if requested
        if max_sorrys:
            prioritized = prioritized[:max_sorrys]
            print(f"\n📌 Limited to first {max_sorrys} sorrys")
        
        # Step 4: Extract constants for context
        print("\n🔧 Extracting QCAL constants...")
        constants = self.harvester.extract_constants()
        print(f"   Found {len(constants)} constants:")
        for name, const in constants.items():
            print(f"     - {name} = {const.value}")
        
        # Step 5: Process sorrys in batches
        batch = []
        resolved_results = []
        
        for i, sorry in enumerate(prioritized, 1):
            print(f"\n\n[{i}/{len(prioritized)}] Processing sorry...")
            
            if dry_run:
                print(f"   Would resolve: {sorry.file_path}:{sorry.line_number}")
                print(f"   Lemma: {sorry.lemma_name}")
                continue
            
            result = self.resolve_sorry(sorry)
            resolved_results.append(result)
            
            if result.success:
                self.stats['resolved'] += 1
                batch.append(result)
            else:
                self.stats['failed'] += 1
            
            # Validate after each batch
            if len(batch) >= batch_size:
                validation_result = self.validate_batch(batch)
                
                if not validation_result.success:
                    print("\n⚠️  VALIDATION FAILED - Stopping resolution")
                    self.stats['validation_failures'] += 1
                    break
                
                batch = []
        
        # Final validation if there's a remaining batch
        if batch and not dry_run:
            self.validate_batch(batch)
        
        # Step 6: Update documentation
        if not dry_run and self.stats['resolved'] > 0:
            self.update_documentation(self.stats['resolved'])
        
        # Step 7: Generate final report
        self.print_final_report()
        
        return self.stats
    
    def print_final_report(self):
        """Print final statistics report."""
        print("\n" + "="*70)
        print("📊 PHOENIX SOLVER FINAL REPORT")
        print("="*70)
        print(f"\nTotal sorry statements scanned: {self.stats['total_sorrys']}")
        print(f"Successfully resolved: {self.stats['resolved']}")
        print(f"Failed resolutions: {self.stats['failed']}")
        print(f"Validation failures: {self.stats['validation_failures']}")
        print(f"Remaining sorrys: {self.stats['total_sorrys'] - self.stats['resolved']}")
        
        if self.stats['total_sorrys'] > 0:
            progress = (self.stats['resolved'] / self.stats['total_sorrys']) * 100
            print(f"\nCompletion: {progress:.2f}%")
        
        print("\n" + "="*70)


def main():
    """Main entry point."""
    parser = argparse.ArgumentParser(
        description='Phoenix Solver - Automated Lean4 sorry resolution',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__
    )
    
    parser.add_argument('--priority-file', type=str,
                       help='Focus on a specific Lean file (e.g., RIGOROUS_UNIQUENESS_EXACT_LAW.lean)')
    parser.add_argument('--max-sorrys', type=int,
                       help='Maximum number of sorrys to resolve')
    parser.add_argument('--batch-size', type=int, default=10,
                       help='Number of sorrys per validation batch (default: 10)')
    parser.add_argument('--dry-run', action='store_true',
                       help='Show plan without making changes')
    parser.add_argument('--repo-root', type=Path, default=REPO_ROOT,
                       help='Repository root directory')
    
    args = parser.parse_args()
    
    # Create solver instance
    solver = PhoenixSolver(args.repo_root)
    
    # Run the solver
    stats = solver.run(
        max_sorrys=args.max_sorrys,
        batch_size=args.batch_size,
        priority_file=args.priority_file,
        dry_run=args.dry_run
    )
    
    # Exit with appropriate code
    sys.exit(0 if stats['validation_failures'] == 0 else 1)


if __name__ == '__main__':
    main()
