#!/usr/bin/env python3
"""
Update Lean Validation Table in README
=======================================

Reads validation_report.json and updates the Validation Summary table
in README.md with the latest values.

This script is called by the lean-validation.yml workflow.
"""

import json
import re
import sys
from pathlib import Path


def main():
    """Update the validation table in README."""
    report_file = Path('validation_report.json')
    readme_file = Path('README.md')
    
    if not report_file.exists():
        print("⚠️  validation_report.json not found")
        sys.exit(1)
    
    if not readme_file.exists():
        print("⚠️  README.md not found")
        sys.exit(1)
    
    # Read validation report
    with open(report_file, 'r') as f:
        report = json.load(f)
    
    val = report['validation']
    
    # Read current README
    with open(readme_file, 'r') as f:
        readme = f.read()
    
    # Create updated table
    table = f"""| Field | Value |
|-------|-------|
| **Status** | {val['status']} |
| **Build Time (s)** | {val['build_time_seconds']} |
| **Warnings** | {val['warnings']} |
| **Errors** | {val['errors']} |
| **Lean Version** | {val['lean_version']} |
| **Date (UTC)** | {val['timestamp_utc']} |"""
    
    # Look for Lean validation section and update table
    # Pattern: find the validation table between certain markers
    pattern = r'(\| Field \| Value \|\s*\n\|-------|-------|[\s\S]*?\| \*\*Date \(UTC\)\*\* \| [^\|]+ \|)'
    
    if re.search(pattern, readme):
        readme = re.sub(pattern, table, readme)
        print("✅ Updated existing validation table")
    else:
        print("⚠️  Validation table not found in README")
        sys.exit(1)
    
    # Write updated README
    with open(readme_file, 'w') as f:
        f.write(readme)
    
    print("✅ README.md updated successfully")
    return 0


if __name__ == '__main__':
    sys.exit(main())
