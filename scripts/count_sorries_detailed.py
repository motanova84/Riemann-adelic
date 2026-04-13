#!/usr/bin/env python3
"""
Sorry Counter - Utility for Phoenix Solver

Counts and categorizes all 'sorry' statements in Lean 4 files.
"""

import sys
from pathlib import Path
import json
from collections import defaultdict


def count_sorries(lean_dir: Path) -> dict:
    """Count all sorry statements in Lean files."""
    
    results = {
        'total': 0,
        'by_file': {},
        'by_directory': defaultdict(int),
        'details': []
    }
    
    for lean_file in lean_dir.rglob("*.lean"):
        if not lean_file.is_file():
            continue
        
        file_sorries = 0
        
        try:
            with open(lean_file, 'r', encoding='utf-8') as f:
                lines = f.readlines()
            
            for i, line in enumerate(lines, start=1):
                if 'sorry' in line and not line.strip().startswith('--'):
                    file_sorries += 1
                    results['total'] += 1
                    
                    # Get theorem name
                    theorem_name = None
                    for j in range(i-1, max(0, i-10), -1):
                        prev_line = lines[j-1].strip()
                        if prev_line.startswith('theorem ') or prev_line.startswith('lemma '):
                            theorem_name = prev_line.split()[1].split(':')[0]
                            break
                    
                    results['details'].append({
                        'file': str(lean_file.relative_to(lean_dir.parent)),
                        'line': i,
                        'theorem': theorem_name,
                        'context': line.strip()[:80]
                    })
            
            if file_sorries > 0:
                rel_path = str(lean_file.relative_to(lean_dir.parent))
                results['by_file'][rel_path] = file_sorries
                
                # Count by directory
                dir_name = lean_file.parent.name
                results['by_directory'][dir_name] += file_sorries
                
        except Exception as e:
            print(f"Warning: Error reading {lean_file}: {e}", file=sys.stderr)
    
    return results


def main():
    # Find lean directory
    repo_root = Path(__file__).parent.parent
    lean_dir = repo_root / "formalization" / "lean"
    
    if not lean_dir.exists():
        print(f"Error: Lean directory not found at {lean_dir}")
        sys.exit(1)
    
    print("🔍 Scanning Lean files for sorry statements...")
    results = count_sorries(lean_dir)
    
    print(f"\n📊 SORRY STATEMENTS SUMMARY")
    print("=" * 60)
    print(f"Total sorry count: {results['total']}")
    print(f"\nTop 10 files with most sorries:")
    
    sorted_files = sorted(
        results['by_file'].items(),
        key=lambda x: x[1],
        reverse=True
    )
    
    for file_path, count in sorted_files[:10]:
        print(f"  {count:4d}  {file_path}")
    
    print(f"\nBy directory:")
    for dir_name, count in sorted(results['by_directory'].items(), key=lambda x: x[1], reverse=True):
        print(f"  {count:4d}  {dir_name}/")
    
    # Save detailed report
    output_file = repo_root / "data" / "sorry_map.json"
    output_file.parent.mkdir(parents=True, exist_ok=True)
    
    with open(output_file, 'w') as f:
        json.dump(results, f, indent=2)
    
    print(f"\n✓ Detailed report saved to {output_file}")
    
    return 0


if __name__ == "__main__":
    sys.exit(main())
