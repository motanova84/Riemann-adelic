#!/usr/bin/env python3
"""
Automated formalization status counter for QCAL repository.
Counts sorry, admit, and axiom statements in Lean files and generates structured output.

This script provides the single source of truth for formalization completion status.
"""

import json
import os
import re
import subprocess
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Tuple


class FormalizationStatusCounter:
    """Count and report formalization status for Lean files."""
    
    def __init__(self, base_path: str = "."):
        self.base_path = Path(base_path)
        self.results = {
            "timestamp": datetime.utcnow().isoformat(),
            "total_files": 0,
            "sorry_count": 0,
            "admit_count": 0,
            "axiom_count": 0,
            "total_incomplete": 0,
            "files_with_sorry": 0,
            "files_with_admit": 0,
            "files_with_axiom": 0,
            "top_files": [],
            "status_summary": ""
        }
    
    def is_code_line(self, line: str) -> bool:
        """Check if line is actual code (not comment or documentation)."""
        stripped = line.strip()
        # Exclude comment lines
        if stripped.startswith("--") or stripped.startswith("/-") or stripped.startswith("/"):
            return False
        # Exclude documentation references
        if any(word in stripped.lower() for word in ["status", "the sorry", "⚠️", "warning"]):
            return False
        return True
    
    def count_in_file(self, filepath: Path, pattern: str) -> int:
        """Count occurrences of pattern in code lines of a file."""
        try:
            with open(filepath, 'r', encoding='utf-8') as f:
                count = 0
                in_comment_block = False
                for line in f:
                    # Track multi-line comment blocks
                    # Handle single-line block comments (both /- and -/ on same line)
                    if "/-" in line and "-/" in line:
                        # Single-line block comment - remove it and process the rest
                        line = re.sub(r'/\-.*?\-/', '', line)
                    elif "/-" in line:
                        in_comment_block = True
                        continue
                    elif "-/" in line:
                        in_comment_block = False
                        continue
                    
                    if in_comment_block:
                        continue
                    
                    # Count only if it's a code line
                    if self.is_code_line(line):
                        # Use word boundary matching
                        if re.search(rf'\b{pattern}\b', line):
                            count += 1
                return count
        except Exception as e:
            print(f"Warning: Could not read {filepath}: {e}")
            return 0
    
    def find_lean_files(self) -> List[Path]:
        """Find all Lean files excluding special directories."""
        lean_files = []
        exclude_dirs = {'.git', '_codeql', '__pycache__', 'node_modules'}
        
        for root, dirs, files in os.walk(self.base_path):
            # Remove excluded directories from search
            dirs[:] = [d for d in dirs if d not in exclude_dirs]
            
            for file in files:
                if file.endswith('.lean') and file != 'count_sorrys.lean':
                    lean_files.append(Path(root) / file)
        
        return lean_files
    
    def count_all(self) -> Dict:
        """Count all formalization status indicators."""
        lean_files = self.find_lean_files()
        self.results["total_files"] = len(lean_files)
        
        file_stats = []
        
        for filepath in lean_files:
            sorry_count = self.count_in_file(filepath, "sorry")
            admit_count = self.count_in_file(filepath, "admit")
            axiom_count = self.count_in_file(filepath, "axiom")
            
            total = sorry_count + admit_count + axiom_count
            
            if total > 0:
                file_stats.append({
                    "file": str(filepath.relative_to(self.base_path)),
                    "sorry": sorry_count,
                    "admit": admit_count,
                    "axiom": axiom_count,
                    "total": total
                })
            
            self.results["sorry_count"] += sorry_count
            self.results["admit_count"] += admit_count
            self.results["axiom_count"] += axiom_count
            
            if sorry_count > 0:
                self.results["files_with_sorry"] += 1
            if admit_count > 0:
                self.results["files_with_admit"] += 1
            if axiom_count > 0:
                self.results["files_with_axiom"] += 1
        
        self.results["total_incomplete"] = (
            self.results["sorry_count"] + 
            self.results["admit_count"] + 
            self.results["axiom_count"]
        )
        
        # Sort and get top 10 files
        file_stats.sort(key=lambda x: x["total"], reverse=True)
        self.results["top_files"] = file_stats[:10]
        
        # Generate status summary
        self.generate_status_summary()
        
        return self.results
    
    def generate_status_summary(self):
        """Generate human-readable status summary."""
        total = self.results["total_incomplete"]
        
        if total == 0:
            status = "✅ COMPLETAMENTE FORMALIZADO - Sin sorry, admit o axiom"
            emoji = "✅"
        elif total <= 10:
            status = f"⚠️ CASI COMPLETO - {total} statements pendientes"
            emoji = "⚠️"
        elif total <= 100:
            status = f"🔄 EN PROGRESO AVANZADO - {total} statements pendientes"
            emoji = "🔄"
        elif total <= 500:
            status = f"🔨 EN DESARROLLO - {total} statements pendientes"
            emoji = "🔨"
        else:
            status = f"📝 FORMALIZACIÓN INICIAL - {total} statements pendientes"
            emoji = "📝"
        
        self.results["status_summary"] = status
        self.results["status_emoji"] = emoji
    
    def generate_markdown_badge(self) -> str:
        """Generate markdown badge for README."""
        total = self.results["total_incomplete"]
        
        if total == 0:
            color = "brightgreen"
            message = "Formalized"
        elif total <= 10:
            color = "yellow"
            message = f"{total} remaining"
        elif total <= 100:
            color = "orange"
            message = f"{total} remaining"
        else:
            color = "red"
            message = f"{total} remaining"
        
        badge = f"![Formalization Status](https://img.shields.io/badge/Formalization-{message}-{color})"
        return badge
    
    def generate_detailed_report(self) -> str:
        """Generate detailed markdown report."""
        lines = [
            "## 📊 Estado de Formalización Lean 4",
            "",
            f"**Última actualización:** {self.results['timestamp']}",
            "",
            "### Resumen General",
            "",
            f"- **Estado:** {self.results['status_summary']}",
            f"- **Archivos Lean totales:** {self.results['total_files']}",
            f"- **Statements `sorry`:** {self.results['sorry_count']}",
            f"- **Statements `admit`:** {self.results['admit_count']}",
            f"- **Statements `axiom`:** {self.results['axiom_count']}",
            f"- **Total incompleto:** {self.results['total_incomplete']}",
            "",
        ]
        
        if self.results["top_files"]:
            lines.extend([
                "### Top 10 Archivos con Más Statements Pendientes",
                "",
                "| Archivo | sorry | admit | axiom | Total |",
                "|---------|-------|-------|-------|-------|",
            ])
            
            for file_info in self.results["top_files"]:
                lines.append(
                    f"| `{file_info['file']}` | "
                    f"{file_info['sorry']} | "
                    f"{file_info['admit']} | "
                    f"{file_info['axiom']} | "
                    f"**{file_info['total']}** |"
                )
            
            lines.append("")
        
        completion_percent = 100 - (self.results['total_incomplete'] / max(1, self.results['total_files'] * 10) * 100)
        completion_percent = max(0, min(100, completion_percent))
        
        lines.extend([
            "### Progreso de Completación",
            "",
            f"**Estimado:** {completion_percent:.1f}% completo",
            "",
            "```",
            self._generate_progress_bar(completion_percent),
            "```",
            ""
        ])
        
        return "\n".join(lines)
    
    def _generate_progress_bar(self, percent: float, width: int = 50) -> str:
        """Generate a text-based progress bar."""
        filled = int(width * percent / 100)
        empty = width - filled
        bar = "█" * filled + "░" * empty
        return f"[{bar}] {percent:.1f}%"
    
    def save_json(self, output_path: str):
        """Save results as JSON."""
        with open(output_path, 'w', encoding='utf-8') as f:
            json.dump(self.results, f, indent=2, ensure_ascii=False)
    
    def save_markdown(self, output_path: str):
        """Save detailed report as markdown."""
        report = self.generate_detailed_report()
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(report)


def main():
    """Main entry point."""
    import argparse
    
    parser = argparse.ArgumentParser(
        description="Count formalization status in Lean files"
    )
    parser.add_argument(
        "--path", 
        default=".", 
        help="Base path to search for Lean files"
    )
    parser.add_argument(
        "--json", 
        help="Output JSON file path"
    )
    parser.add_argument(
        "--markdown", 
        help="Output markdown file path"
    )
    parser.add_argument(
        "--summary",
        action="store_true",
        help="Print summary to stdout"
    )
    
    args = parser.parse_args()
    
    counter = FormalizationStatusCounter(args.path)
    results = counter.count_all()
    
    # Always print basic summary
    print("═" * 60)
    print("  QCAL Formalization Status Counter")
    print("═" * 60)
    print()
    print(f"Status: {results['status_summary']}")
    print()
    print(f"Total Lean files:    {results['total_files']}")
    print(f"'sorry' statements:  {results['sorry_count']}")
    print(f"'admit' statements:  {results['admit_count']}")
    print(f"'axiom' statements:  {results['axiom_count']}")
    print()
    print("─" * 60)
    print(f"TOTAL INCOMPLETE:    {results['total_incomplete']}")
    print("─" * 60)
    print()
    
    if args.summary:
        print(counter.generate_detailed_report())
    
    if args.json:
        counter.save_json(args.json)
        print(f"✓ JSON report saved to: {args.json}")
    
    if args.markdown:
        counter.save_markdown(args.markdown)
        print(f"✓ Markdown report saved to: {args.markdown}")
    
    print()
    print("Badge for README:")
    print(counter.generate_markdown_badge())
    print()


if __name__ == "__main__":
    main()
