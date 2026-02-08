#!/usr/bin/env python3
"""
📚 Lean Dependency Analyzer - Advanced Lean4 Analysis Tool
==========================================================

Analyzes Lean4 formalization dependencies, identifies critical files,
and generates optimization recommendations.

Frequency: 141.7001 Hz
"""

import argparse
import json
import sys
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Set, Tuple
import re


class LeanDependencyAnalyzer:
    """Advanced Lean4 dependency analysis"""
    
    def __init__(self, lean_path: str):
        self.lean_path = Path(lean_path)
        self.dependencies = {}
        self.reverse_deps = {}
        self.lean_files = []
        self.analysis_results = {
            "analyzer": "Lean Dependency Analyzer",
            "timestamp": datetime.utcnow().isoformat(),
            "lean_path": str(self.lean_path)
        }
    
    def find_lean_files(self) -> List[Path]:
        """Find all .lean files in the directory"""
        if not self.lean_path.exists():
            return []
        
        lean_files = list(self.lean_path.rglob("*.lean"))
        self.lean_files = lean_files
        return lean_files
    
    def extract_imports(self, lean_file: Path) -> List[str]:
        """Extract import statements from a Lean file"""
        imports = []
        
        try:
            content = lean_file.read_text()
            
            # Match import statements
            import_pattern = r'^\s*import\s+([^\s]+)'
            for line in content.split('\n'):
                match = re.match(import_pattern, line)
                if match:
                    imports.append(match.group(1))
        except Exception as e:
            print(f"Error reading {lean_file}: {e}")
        
        return imports
    
    def build_dependency_graph(self) -> Dict:
        """Build complete dependency graph"""
        graph = {
            "nodes": [],
            "edges": [],
            "stats": {}
        }
        
        for lean_file in self.lean_files:
            # Get relative path for cleaner display
            rel_path = lean_file.relative_to(self.lean_path)
            module_name = str(rel_path).replace('/', '.').replace('.lean', '')
            
            # Extract imports
            imports = self.extract_imports(lean_file)
            
            # Store dependencies
            self.dependencies[module_name] = imports
            
            # Add to graph
            graph["nodes"].append({
                "id": module_name,
                "file": str(rel_path),
                "import_count": len(imports)
            })
            
            for imp in imports:
                graph["edges"].append({
                    "from": module_name,
                    "to": imp,
                    "type": "import"
                })
                
                # Build reverse dependencies
                if imp not in self.reverse_deps:
                    self.reverse_deps[imp] = []
                self.reverse_deps[imp].append(module_name)
        
        # Calculate statistics
        graph["stats"] = {
            "total_files": len(self.lean_files),
            "total_imports": sum(len(deps) for deps in self.dependencies.values()),
            "avg_imports_per_file": sum(len(deps) for deps in self.dependencies.values()) / max(len(self.lean_files), 1)
        }
        
        return graph
    
    def identify_critical_files(self) -> List[Dict]:
        """Identify files that are most depended upon"""
        critical = []
        
        for module, dependents in self.reverse_deps.items():
            if len(dependents) >= 2:  # Threshold for "critical"
                critical.append({
                    "module": module,
                    "dependent_count": len(dependents),
                    "dependents": dependents[:5]  # First 5
                })
        
        # Sort by dependency count
        critical.sort(key=lambda x: x["dependent_count"], reverse=True)
        
        return critical
    
    def detect_circular_dependencies(self) -> List[List[str]]:
        """Detect circular dependency chains"""
        visited = set()
        rec_stack = set()
        cycles = []
        
        def dfs(node: str, path: List[str]):
            visited.add(node)
            rec_stack.add(node)
            path.append(node)
            
            for neighbor in self.dependencies.get(node, []):
                if neighbor not in visited:
                    dfs(neighbor, path.copy())
                elif neighbor in rec_stack:
                    # Found a cycle
                    cycle_start = path.index(neighbor)
                    cycle = path[cycle_start:] + [neighbor]
                    if cycle not in cycles:
                        cycles.append(cycle)
            
            rec_stack.remove(node)
        
        for node in self.dependencies:
            if node not in visited:
                dfs(node, [])
        
        return cycles
    
    def generate_optimization_plan(self) -> Dict:
        """Generate optimization recommendations"""
        plan = {
            "recommendations": [],
            "priority": "medium"
        }
        
        # Check for files with too many imports
        high_import_files = [
            (mod, len(deps))
            for mod, deps in self.dependencies.items()
            if len(deps) > 10
        ]
        
        if high_import_files:
            plan["recommendations"].append({
                "type": "refactor",
                "title": "Reduce import complexity",
                "files": [f[0] for f in high_import_files],
                "reason": "Files with >10 imports may benefit from refactoring"
            })
        
        # Check for circular dependencies
        cycles = self.detect_circular_dependencies()
        if cycles:
            plan["recommendations"].append({
                "type": "fix_cycles",
                "title": "Resolve circular dependencies",
                "cycles": cycles[:3],  # First 3
                "reason": "Circular dependencies can cause build issues"
            })
            plan["priority"] = "high"
        
        # Suggest modularization
        if len(self.lean_files) > 50:
            plan["recommendations"].append({
                "type": "modularize",
                "title": "Consider modularization",
                "reason": f"{len(self.lean_files)} files - consider grouping into modules"
            })
        
        return plan
    
    def run_analysis(self) -> Dict:
        """Run complete analysis"""
        print(f"📚 Lean Dependency Analyzer")
        print(f"=" * 60)
        print(f"📁 Path: {self.lean_path}")
        print(f"=" * 60)
        
        # Find files
        print(f"\n🔍 Finding Lean files...")
        lean_files = self.find_lean_files()
        print(f"   Found {len(lean_files)} .lean files")
        
        if len(lean_files) == 0:
            print(f"   ⚠️  No Lean files found")
            return self.analysis_results
        
        # Build dependency graph
        print(f"\n🕸️  Building dependency graph...")
        graph = self.build_dependency_graph()
        print(f"   Nodes: {len(graph['nodes'])}")
        print(f"   Edges: {len(graph['edges'])}")
        print(f"   Avg imports/file: {graph['stats']['avg_imports_per_file']:.2f}")
        
        # Identify critical files
        print(f"\n🎯 Identifying critical files...")
        critical = self.identify_critical_files()
        print(f"   Found {len(critical)} critical files")
        for c in critical[:5]:
            print(f"   • {c['module']}: {c['dependent_count']} dependents")
        
        # Detect cycles
        print(f"\n🔄 Detecting circular dependencies...")
        cycles = self.detect_circular_dependencies()
        if cycles:
            print(f"   ⚠️  Found {len(cycles)} circular dependency chains")
        else:
            print(f"   ✅ No circular dependencies detected")
        
        # Generate optimization plan
        print(f"\n📋 Generating optimization plan...")
        plan = self.generate_optimization_plan()
        print(f"   Priority: {plan['priority'].upper()}")
        print(f"   Recommendations: {len(plan['recommendations'])}")
        
        # Compile results
        self.analysis_results["graph"] = graph
        self.analysis_results["critical_files"] = critical
        self.analysis_results["circular_dependencies"] = cycles
        self.analysis_results["optimization_plan"] = plan
        
        print(f"\n✨ Analysis complete!")
        
        return self.analysis_results
    
    def save_results(self, output_path: str):
        """Save analysis results"""
        with open(output_path, 'w', encoding='utf-8') as f:
            json.dump(self.analysis_results, f, indent=2, ensure_ascii=False)
        print(f"\n💾 Results saved to: {output_path}")


def main():
    parser = argparse.ArgumentParser(
        description="📚 Lean Dependency Analyzer"
    )
    parser.add_argument(
        "--path",
        type=str,
        default="formalization/lean",
        help="Path to Lean files (default: formalization/lean)"
    )
    parser.add_argument(
        "--output",
        type=str,
        help="Output JSON file path"
    )
    
    args = parser.parse_args()
    
    # Create and run analyzer
    analyzer = LeanDependencyAnalyzer(args.path)
    results = analyzer.run_analysis()
    
    # Save results if output specified
    if args.output:
        analyzer.save_results(args.output)
    
    sys.exit(0)


if __name__ == "__main__":
    main()
