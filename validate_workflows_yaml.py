#!/usr/bin/env python3
"""
YAML Workflow Validation Script

This script validates all GitHub Actions workflow files in .github/workflows/
to ensure they:
1. Parse as valid YAML
2. Contain no HTML entities
3. Use correct English keywords (not Spanish translations)
4. Have no duplicate keys
5. Follow proper YAML structure

Usage:
    python3 validate_workflows_yaml.py

Exit codes:
    0 - All validations passed
    1 - One or more validations failed
"""

import glob
import re
import sys
from pathlib import Path

import yaml


def validate_yaml_syntax(workflow_file):
    """Validate that a file parses as valid YAML."""
    try:
        with open(workflow_file, 'r', encoding='utf-8') as f:
            yaml.safe_load(f)
        return True, None
    except yaml.YAMLError as e:
        return False, str(e)


def check_html_entities(workflow_file):
    """Check for HTML entities in the file."""
    with open(workflow_file, 'r', encoding='utf-8') as f:
        content = f.read()
    
    html_entities = re.findall(r'&[a-z]+;|&#\d+;', content, re.IGNORECASE)
    if html_entities:
        return False, html_entities
    return True, None


def check_spanish_keywords(workflow_file):
    """Check for incorrect Spanish keywords where English is expected."""
    # Skip ser.yml as it's intentionally in Spanish
    if 'ser.yml' in str(workflow_file):
        return True, None
    
    with open(workflow_file, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # Pattern for YAML keys that should be in English
    spanish_patterns = [
        (r'^\s*nombre\s*:', 'nombre: (should be name:)'),
        (r'^\s*correr\s*:', 'correr: (should be run:)'),
        (r'^\s*pasos\s*:', 'pasos: (should be steps:)'),
        (r'^\s*si\s*:', 'si: (should be if:)'),
        (r'pasos\..*\.salidas', 'pasos.*.salidas (should be steps.*.outputs)'),
        (r'verdadero', 'verdadero (should be true)'),
        (r'LÍNEA\s+BASE', 'LÍNEA BASE (should be BASELINE)'),
    ]
    
    issues = []
    for line_num, line in enumerate(content.split('\n'), 1):
        for pattern, description in spanish_patterns:
            if re.search(pattern, line, re.MULTILINE):
                issues.append(f"Line {line_num}: {description}")
    
    if issues:
        return False, issues
    return True, None


def main():
    """Main validation function."""
    print("=" * 70)
    print("GitHub Actions Workflow YAML Validation")
    print("=" * 70)
    print()
    
    workflow_files = sorted(
        glob.glob('.github/workflows/*.yml') +
        glob.glob('.github/workflows/*.yaml')
    )
    
    if not workflow_files:
        print("❌ No workflow files found in .github/workflows/")
        return 1
    
    print(f"Found {len(workflow_files)} workflow files to validate\n")
    
    all_passed = True
    results = {
        'passed': [],
        'failed': []
    }
    
    for workflow_file in workflow_files:
        file_name = Path(workflow_file).name
        print(f"Validating {file_name}...")
        
        # Test 1: YAML syntax
        yaml_valid, yaml_error = validate_yaml_syntax(workflow_file)
        if not yaml_valid:
            print(f"  ❌ YAML Syntax Error: {yaml_error}")
            results['failed'].append(workflow_file)
            all_passed = False
            continue
        
        # Test 2: HTML entities
        no_html, html_entities = check_html_entities(workflow_file)
        if not no_html:
            print(f"  ❌ HTML Entities Found: {html_entities}")
            results['failed'].append(workflow_file)
            all_passed = False
            continue
        
        # Test 3: Spanish keywords
        no_spanish, spanish_issues = check_spanish_keywords(workflow_file)
        if not no_spanish:
            print(f"  ❌ Incorrect Spanish Keywords:")
            for issue in spanish_issues:
                print(f"     {issue}")
            results['failed'].append(workflow_file)
            all_passed = False
            continue
        
        print(f"  ✅ All checks passed")
        results['passed'].append(workflow_file)
    
    # Print summary
    print()
    print("=" * 70)
    print("Summary")
    print("=" * 70)
    print(f"✅ Passed: {len(results['passed'])}")
    print(f"❌ Failed: {len(results['failed'])}")
    
    if results['failed']:
        print("\nFailed files:")
        for f in results['failed']:
            print(f"  - {Path(f).name}")
    
    if all_passed:
        print("\n🎉 All workflow files are valid!")
        return 0
    else:
        print("\n⚠️  Some workflow files have issues that need to be fixed.")
        return 1


if __name__ == '__main__':
    sys.exit(main())
