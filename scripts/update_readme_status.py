#!/usr/bin/env python3
"""
Update README.md with current formalization status.
This script is the single source of truth for formalization completion.
"""

import json
import re
import sys
from pathlib import Path
from datetime import datetime


def load_status_data(json_path: str) -> dict:
    """Load formalization status from JSON file."""
    with open(json_path, 'r', encoding='utf-8') as f:
        return json.load(f)


def generate_status_section(data: dict) -> str:
    """Generate the formalization status section for README."""
    
    # Calculate completion percentage
    total_incomplete = data['total_incomplete']
    total_files = data['total_files']
    
    # Estimate completion (assuming ~10 statements per file when fully formalized)
    estimated_total = total_files * 10
    completion = max(0, min(100, 100 - (total_incomplete / max(1, estimated_total) * 100)))
    
    # Determine status badge color and message
    if total_incomplete == 0:
        badge_color = "brightgreen"
        badge_msg = "100%25%20Complete"
        status_icon = "✅"
        status_text = "COMPLETAMENTE FORMALIZADO"
    elif total_incomplete <= 10:
        badge_color = "yellow"
        badge_msg = f"{int(completion)}%25%20Complete"
        status_icon = "⚠️"
        status_text = f"CASI COMPLETO ({total_incomplete} statements pendientes)"
    elif total_incomplete <= 100:
        badge_color = "orange"
        badge_msg = f"{int(completion)}%25%20Complete"
        status_icon = "🔄"
        status_text = f"EN PROGRESO AVANZADO ({total_incomplete} statements pendientes)"
    else:
        badge_color = "red"
        badge_msg = f"{int(completion)}%25%20Complete"
        status_icon = "📝"
        status_text = f"EN DESARROLLO ({total_incomplete} statements pendientes)"
    
    # Build the section
    lines = [
        "### 📊 Estado de Formalización Lean 4 (Actualizado Automáticamente)",
        "",
        f"![Formalization Status](https://img.shields.io/badge/Formalización-{badge_msg}-{badge_color})",
        "",
        f"**{status_icon} Estado:** {status_text}",
        "",
        f"- **Archivos Lean totales:** {total_files}",
        f"- **Statements `sorry`:** {data['sorry_count']} (en {data['files_with_sorry']} archivos)",
        f"- **Statements `admit`:** {data['admit_count']} (en {data['files_with_admit']} archivos)",
        f"- **Statements `axiom`:** {data['axiom_count']} (en {data['files_with_axiom']} archivos)",
        f"- **Total incompleto:** **{total_incomplete}**",
        "",
        f"*Última actualización: {data['timestamp']}*",
        "",
    ]
    
    # Add note about skeletons if there are many incomplete statements
    if total_incomplete > 100:
        lines.extend([
            "> ⚠️ **Nota:** La formalización está en progreso activo. Algunos archivos contienen ",
            f"> `axiom` y `sorry` statements que representan pruebas por completar. El objetivo es ",
            "> reducir este número a cero mediante formalizaciones completas.",
            "",
        ])
    
    return "\n".join(lines)


def update_readme(readme_path: str, status_section: str):
    """Update README.md with new status section."""
    
    with open(readme_path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # Define markers for the auto-updated section
    start_marker = "<!-- AUTO-GENERATED: Formalization Status - DO NOT EDIT MANUALLY -->"
    end_marker = "<!-- END AUTO-GENERATED: Formalization Status -->"
    
    # Check if markers exist
    if start_marker in content and end_marker in content:
        # Replace existing section
        pattern = f"{re.escape(start_marker)}.*?{re.escape(end_marker)}"
        new_section = f"{start_marker}\n{status_section}\n{end_marker}"
        new_content = re.sub(pattern, new_section, content, flags=re.DOTALL)
    else:
        # Find where to insert (after main header, before or replacing old formalization text)
        # Look for the line about "Formalización Lean 4"
        pattern = r'- \*\*Formalización Lean 4\*\*:.*?\n'
        if re.search(pattern, content):
            # Replace the old line with the new section
            replacement = f"{start_marker}\n{status_section}\n{end_marker}\n"
            new_content = re.sub(pattern, replacement, content)
        else:
            # If not found, add after the first major section (after quickstart or structure)
            # Find a good insertion point - after "## 📂 Archivos Clave" or similar
            insert_patterns = [
                (r'(## 📂 Archivos Clave de la Demostración\n)', r'\1\n' + start_marker + '\n' + status_section + '\n' + end_marker + '\n\n'),
                (r'(## 🚀 Quickstart.*?\n)', r'\1\n' + start_marker + '\n' + status_section + '\n' + end_marker + '\n\n'),
            ]
            
            new_content = content
            for pattern, replacement in insert_patterns:
                if re.search(pattern, new_content, re.DOTALL):
                    new_content = re.sub(pattern, replacement, new_content, count=1)
                    break
            else:
                # Last resort: append to end
                new_content = content + "\n\n" + start_marker + "\n" + status_section + "\n" + end_marker + "\n"
    
    # Write back
    with open(readme_path, 'w', encoding='utf-8') as f:
        f.write(new_content)


def main():
    """Main entry point."""
    import argparse
    
    parser = argparse.ArgumentParser(
        description="Update README.md with current formalization status"
    )
    parser.add_argument(
        "--status-json",
        default="data/formalization_status.json",
        help="Path to formalization status JSON file"
    )
    parser.add_argument(
        "--readme",
        default="README.md",
        help="Path to README.md file"
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Print changes without modifying README"
    )
    
    args = parser.parse_args()
    
    # Check if status file exists
    if not Path(args.status_json).exists():
        print(f"Error: Status file not found: {args.status_json}")
        print("Run count_formalization_status.py first to generate status data.")
        sys.exit(1)
    
    # Load status data
    print(f"Loading status from: {args.status_json}")
    data = load_status_data(args.status_json)
    
    # Generate status section
    print("Generating status section...")
    status_section = generate_status_section(data)
    
    if args.dry_run:
        print("\n" + "=" * 60)
        print("DRY RUN - Generated section (not written to README):")
        print("=" * 60)
        print(status_section)
        print("=" * 60)
    else:
        # Update README
        print(f"Updating README: {args.readme}")
        update_readme(args.readme, status_section)
        print(f"✓ README updated successfully!")
        print(f"  Total incomplete statements: {data['total_incomplete']}")
        print(f"  Status: {data['status_summary']}")


if __name__ == "__main__":
    main()
