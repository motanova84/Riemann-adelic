#!/usr/bin/env python3
"""
Dependency Analyzer - Analyzes dependencies between Lean files
"""

import os
import sys
import json
import argparse
import re
from pathlib import Path
from typing import Dict, List, Set

class DependencyAnalyzer:
    """Analyzes dependencies in Lean formalization"""
    
    def __init__(self, input_dir: str, output: str = "dependencies.json"):
        self.input_dir = Path(input_dir)
        self.output = Path(output)
        
    def analyze(self) -> Dict:
        """Analyze all dependencies"""
        print(f"🧠 Analyzing dependencies in {self.input_dir}...")
        
        dependencies = {
            "timestamp": "auto",
            "files": [],
            "graph": {}
        }
        
        if not self.input_dir.exists():
            print(f"Warning: Directory {self.input_dir} does not exist")
            return dependencies
        
        # Find all Lean files
        lean_files = list(self.input_dir.rglob("*.lean"))
        print(f"Found {len(lean_files)} Lean files")
        
        for lean_file in lean_files:
            deps = self.extract_dependencies(lean_file)
            file_info = {
                "path": str(lean_file.relative_to(self.input_dir)),
                "dependencies": deps,
                "import_count": len(deps)
            }
            dependencies["files"].append(file_info)
            dependencies["graph"][str(lean_file.relative_to(self.input_dir))] = deps
        
        # Save results
        with open(self.output, 'w', encoding='utf-8') as f:
            json.dump(dependencies, f, indent=2)
        
        print(f"✅ Analysis complete. Saved to {self.output}")
        return dependencies
    
    def extract_dependencies(self, file_path: Path) -> List[str]:
        """Extract imports from a Lean file"""
        dependencies = []
        
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
                
            # Find import statements
            import_pattern = r'import\s+([A-Za-z0-9_.]+)'
            imports = re.findall(import_pattern, content)
            dependencies.extend(imports)
            
        except Exception as e:
            print(f"Warning: Could not read {file_path}: {e}")
        
        return dependencies

def main():
    parser = argparse.ArgumentParser(description='Dependency Analyzer')
    parser.add_argument('--input-dir', type=str, required=True,
                       help='Input directory to analyze')
    parser.add_argument('--output', type=str, default='dependencies.json',
                       help='Output file for dependencies')
    
    args = parser.parse_args()
    
    analyzer = DependencyAnalyzer(args.input_dir, args.output)
    analyzer.analyze()
    
    return 0

if __name__ == "__main__":
    sys.exit(main())
