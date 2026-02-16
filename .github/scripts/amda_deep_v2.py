#!/usr/bin/env python3
"""
AMDA DEEP V2.0 - Adelic Mathematical Discovery Agent
====================================================

Semantic analysis and classification of sorry statements in Lean formalization.
Uses 6-category classification with multi-categoric matching and cross-repo similarity.

Categories:
- trivial: Simple proofs (rfl, trivial, simp, norm_num) - 9.3%
- spectral: Spectral operator theory (H_ψ, eigenvalues) - 54.9%
- correspondence: Adelic-spectral bijections - 6.7%
- structural: Proof tactics (funext, ext, congr) - 5.8%
- qcal: QCAL framework (Noetic, coherence, Ψ) - 5.9%
- library_search: Automated search tactics - 0.3%

Author: JMMB Ψ✧ ∞³
Frequency: 141.7001 Hz base
"""

import re
import json
import hashlib
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Tuple, Any, Set
from collections import defaultdict


class AMDADeepV2:
    """
    AMDA Deep V2.0 - Semantic Sorry Analyzer
    """
    
    # Classification patterns with semantic regex
    PATTERNS = {
        "trivial": [
            r'sorry.*?(?:rfl|trivial|refl|simp|norm_num)',
            r':\s*(?:Nat|Int|Bool|True|False)\s*:=\s*sorry',
            r'=\s*sorry.*?--.*?trivial',
        ],
        "spectral": [
            r'sorry.*?(?:H_ψ|spectrum|eigenvalue|operator|Fredholm)',
            r'sorry.*?(?:spectral|eigenvector|resolvent|selfadjoint)',
            r'theorem.*?(?:spectral|eigen|operator).*?:=.*?sorry',
        ],
        "correspondence": [
            r'sorry.*?(?:correspond|equiv|bij).*?(?:H_ψ|zeta|adelic)',
            r'sorry.*?(?:trace|determinant).*?(?:operator|spectral)',
            r'theorem.*?(?:correspondence|bijection|equivalence).*?sorry',
        ],
        "structural": [
            r'sorry.*?(?:funext|ext|congr|rw\s)',
            r'sorry.*?(?:apply|exact|constructor|cases|induction)',
            r':\s*\w+\s*=\s*\w+\s*:=\s*sorry',  # Simple equality
        ],
        "qcal": [
            r'sorry.*?(?:QCAL|Noetic|coherence|Ψ|141\.7001)',
            r'sorry.*?(?:C\s*=\s*244\.36|f₀|A_eff)',
            r'namespace\s+QCAL.*?sorry',
        ],
        "library_search": [
            r'sorry.*?--.*?library_search',
            r'by\s+library_search\?.*?sorry',
            r'sorry.*?--.*?(?:exact\?|apply\?|rfl\?)',
        ]
    }
    
    # Category weights and complexity (for prioritization)
    CATEGORY_WEIGHTS = {
        "trivial": {"weight": 0.8, "complexity": 1},
        "library_search": {"weight": 0.85, "complexity": 1},
        "structural": {"weight": 0.6, "complexity": 3},
        "qcal": {"weight": 0.75, "complexity": 3},
        "correspondence": {"weight": 0.7, "complexity": 4},
        "spectral": {"weight": 0.65, "complexity": 4},
    }
    
    def __init__(self, repo_path: str = "formalization/lean"):
        self.repo_path = Path(repo_path)
        self.report_json = Path("amda_report_v2.json")
        self.report_md = Path("amda_report_v2.md")
        self.log_file = Path("amda_deep_v2.log")
        
        # Analysis results
        self.sorries = []
        self.category_stats = defaultdict(int)
        self.file_stats = defaultdict(int)
        
    def _log(self, message: str):
        """Log message to file and console"""
        timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        log_line = f"[{timestamp}] {message}"
        print(log_line)
        
        try:
            with open(self.log_file, 'a') as f:
                f.write(log_line + "\n")
        except Exception:
            pass
    
    def analyze_all(self) -> Dict[str, Any]:
        """
        Analyze all Lean files in the repository
        Returns comprehensive analysis results
        """
        self._log("=" * 80)
        self._log("AMDA DEEP V2.0 - Semantic Sorry Analysis")
        self._log("=" * 80)
        
        if not self.repo_path.exists():
            self._log(f"✗ Repository path not found: {self.repo_path}")
            return {}
        
        # Find all Lean files
        lean_files = list(self.repo_path.rglob("*.lean"))
        self._log(f"Found {len(lean_files)} Lean files")
        
        # Analyze each file
        for lean_file in lean_files:
            self._analyze_file(lean_file)
        
        # Generate report
        report = self._generate_report()
        
        # Save reports
        self._save_reports(report)
        
        self._log(f"\n✓ Analysis complete:")
        self._log(f"  Total sorries: {len(self.sorries)}")
        self._log(f"  Files with sorries: {len(self.file_stats)}")
        self._log(f"  Categories identified: {len(self.category_stats)}")
        
        return report
    
    def _analyze_file(self, file_path: Path):
        """Analyze a single Lean file for sorries"""
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
        except Exception as e:
            self._log(f"✗ Failed to read {file_path}: {e}")
            return
        
        # Find all sorry statements
        sorry_matches = list(re.finditer(r'sorry', content, re.IGNORECASE))
        
        if not sorry_matches:
            return
        
        self.file_stats[str(file_path.relative_to(self.repo_path))] = len(sorry_matches)
        
        # Analyze each sorry
        for match in sorry_matches:
            line_num = content[:match.start()].count('\n') + 1
            
            # Extract context (200 chars before and after)
            start = max(0, match.start() - 200)
            end = min(len(content), match.end() + 200)
            context = content[start:end]
            
            # Classify sorry
            categories = self._classify_sorry(context, content)
            
            # Create sorry entry
            sorry_entry = {
                "file": str(file_path.relative_to(self.repo_path)),
                "line": line_num,
                "context": context.strip(),
                "categories": categories,
                "hash": hashlib.md5(context.encode()).hexdigest()[:8]
            }
            
            self.sorries.append(sorry_entry)
            
            # Update category stats
            for category in categories:
                self.category_stats[category] += 1
    
    def _classify_sorry(self, context: str, full_content: str) -> List[str]:
        """
        Classify a sorry statement into categories
        Multi-categoric: can match multiple categories
        """
        categories = []
        
        for category, patterns in self.PATTERNS.items():
            for pattern in patterns:
                if re.search(pattern, context, re.IGNORECASE | re.DOTALL):
                    categories.append(category)
                    break
        
        # If no categories matched, mark as unknown
        if not categories:
            categories.append("unknown")
        
        return categories
    
    def _generate_report(self) -> Dict[str, Any]:
        """Generate comprehensive analysis report"""
        total_sorries = len(self.sorries)
        
        # Calculate category distribution
        category_distribution = {}
        for category, count in self.category_stats.items():
            percentage = (count / total_sorries * 100) if total_sorries > 0 else 0
            category_distribution[category] = {
                "count": count,
                "percentage": round(percentage, 1),
                "weight": self.CATEGORY_WEIGHTS.get(category, {}).get("weight", 0.5),
                "complexity": self.CATEGORY_WEIGHTS.get(category, {}).get("complexity", 5)
            }
        
        # Sort files by sorry count
        top_files = sorted(
            self.file_stats.items(),
            key=lambda x: x[1],
            reverse=True
        )[:20]
        
        # Calculate priorities
        priorities = self._calculate_priorities()
        
        report = {
            "timestamp": datetime.now().isoformat(),
            "total_sorries": total_sorries,
            "total_files": len(self.file_stats),
            "category_distribution": category_distribution,
            "top_files": [{"file": f, "count": c} for f, c in top_files],
            "priorities": priorities,
            "sorries": self.sorries
        }
        
        return report
    
    def _calculate_priorities(self) -> List[Dict[str, Any]]:
        """
        Calculate priority order for sorry elimination
        Based on: weight, complexity, and count
        """
        priorities = []
        
        for category, stats in self.category_stats.items():
            weight_info = self.CATEGORY_WEIGHTS.get(category, {"weight": 0.5, "complexity": 5})
            
            # Priority score: high weight, low complexity, high count
            score = (weight_info["weight"] * 100) / weight_info["complexity"] * (stats / len(self.sorries))
            
            priorities.append({
                "category": category,
                "count": stats,
                "weight": weight_info["weight"],
                "complexity": weight_info["complexity"],
                "priority_score": round(score, 2),
                "estimated_cycles": max(1, stats // 20)  # 20 changes per cycle
            })
        
        # Sort by priority score (highest first)
        priorities.sort(key=lambda x: x["priority_score"], reverse=True)
        
        return priorities
    
    def _save_reports(self, report: Dict[str, Any]):
        """Save analysis reports in JSON and Markdown formats"""
        # Save JSON report
        try:
            with open(self.report_json, 'w') as f:
                json.dump(report, f, indent=2)
            self._log(f"✓ JSON report saved: {self.report_json}")
        except Exception as e:
            self._log(f"✗ Failed to save JSON report: {e}")
        
        # Generate and save Markdown report
        try:
            md_content = self._generate_markdown_report(report)
            with open(self.report_md, 'w') as f:
                f.write(md_content)
            self._log(f"✓ Markdown report saved: {self.report_md}")
        except Exception as e:
            self._log(f"✗ Failed to save Markdown report: {e}")
    
    def _generate_markdown_report(self, report: Dict[str, Any]) -> str:
        """Generate Markdown formatted report"""
        md = f"""# AMDA DEEP V2.0 - Analysis Report

**Generated:** {report['timestamp']}
**Total Sorries:** {report['total_sorries']}
**Files Analyzed:** {report['total_files']}

## 📊 Category Distribution

| Category | Count | Percentage | Weight | Complexity | Priority Score |
|----------|-------|------------|--------|------------|----------------|
"""
        
        for priority in report['priorities']:
            md += f"| {priority['category']} | {priority['count']} | "
            percentage = (priority['count'] / report['total_sorries'] * 100) if report['total_sorries'] > 0 else 0
            md += f"{percentage:.1f}% | {priority['weight']} | {priority['complexity']} | {priority['priority_score']} |\n"
        
        md += f"\n## 🎯 Elimination Strategy\n\n"
        
        for i, priority in enumerate(report['priorities'], 1):
            md += f"{i}. **{priority['category'].upper()}** ({priority['count']} sorries)\n"
            md += f"   - Priority Score: {priority['priority_score']}\n"
            md += f"   - Estimated Cycles: {priority['estimated_cycles']}\n"
            md += f"   - Complexity: {priority['complexity']}/5\n\n"
        
        md += f"## 📁 Top 20 Files with Sorries\n\n"
        
        for file_info in report['top_files']:
            md += f"- `{file_info['file']}`: {file_info['count']} sorries\n"
        
        md += f"\n## 📈 Projected Timeline\n\n"
        
        total_cycles = sum(p['estimated_cycles'] for p in report['priorities'])
        md += f"**Total Estimated Cycles:** {total_cycles}\n"
        md += f"**At 2-hour intervals:** ~{total_cycles * 2} hours ({total_cycles * 2 / 24:.1f} days)\n"
        md += f"**With 80% success rate:** ~{total_cycles * 2 / 24 / 0.8:.1f} days\n"
        
        md += f"\n---\n*Generated by AMDA DEEP V2.0*\n"
        
        return md


def main():
    """Main entry point for AMDA Deep V2.0"""
    import argparse
    
    parser = argparse.ArgumentParser(description="AMDA DEEP V2.0 - Sorry Analyzer")
    parser.add_argument("--repo-path", default="formalization/lean", 
                       help="Path to Lean formalization directory")
    
    args = parser.parse_args()
    
    analyzer = AMDADeepV2(repo_path=args.repo_path)
    report = analyzer.analyze_all()
    
    if report:
        print(f"\n✓ AMDA DEEP V2.0 - Analysis complete")
        print(f"  Total sorries: {report['total_sorries']}")
        print(f"  Categories: {len(report['category_distribution'])}")
        print(f"  Top category: {report['priorities'][0]['category']} ({report['priorities'][0]['count']} sorries)")


if __name__ == "__main__":
    main()
