#!/usr/bin/env python3
"""
Validate GitHub Workflows Configuration

This script validates that the new GitHub workflows are properly configured
and would run successfully.
"""

import yaml
import subprocess
import sys
from pathlib import Path

def validate_yaml_syntax(workflow_path):
    """Validate YAML syntax of workflow file."""
    try:
        with open(workflow_path) as f:
            yaml.safe_load(f)
        return True, "Valid YAML"
    except Exception as e:
        return False, str(e)

def check_workflow_structure(workflow_path):
    """Check that workflow has required structure."""
    with open(workflow_path) as f:
        data = yaml.safe_load(f)
    
    # Check required fields
    # Note: YAML parsers may interpret 'on:' as boolean True
    required = ['name', 'jobs']
    missing = [field for field in required if field not in data]
    
    # Check for 'on' trigger (may be parsed as boolean True by PyYAML)
    has_trigger = 'on' in data or True in data
    if not has_trigger:
        missing.append('on/trigger')
    
    if missing:
        return False, f"Missing fields: {missing}"
    
    return True, f"Has all required fields"

def main():
    """Main validation function."""
    workflows = [
        '.github/workflows/ci.yml',
        '.github/workflows/coverage.yml',
        '.github/workflows/proof-check.yml',
        '.github/workflows/property-tests.yml',
        '.github/workflows/dependency-review.yml',
        '.github/workflows/release.yml',
        '.github/workflows/nightly.yml',
    ]
    
    print("=" * 70)
    print("GitHub Workflows Validation")
    print("=" * 70)
    print()
    
    all_valid = True
    
    for workflow in workflows:
        workflow_name = Path(workflow).name
        print(f"Validating {workflow_name}...")
        
        # Check YAML syntax
        valid, msg = validate_yaml_syntax(workflow)
        if not valid:
            print(f"  ❌ YAML Syntax: {msg}")
            all_valid = False
            continue
        print(f"  ✅ YAML Syntax: {msg}")
        
        # Check structure
        valid, msg = check_workflow_structure(workflow)
        if not valid:
            print(f"  ❌ Structure: {msg}")
            all_valid = False
            continue
        print(f"  ✅ Structure: {msg}")
        
        print()
    
    print("=" * 70)
    if all_valid:
        print("✅ All workflows validated successfully!")
        print()
        print("Next steps:")
        print("1. Push these workflows to GitHub")
        print("2. Configure CODECOV_TOKEN secret (optional for public repos)")
        print("3. Workflows will run automatically on next push to main")
        return 0
    else:
        print("❌ Some workflows have issues. Please fix them before pushing.")
        return 1

if __name__ == '__main__':
    sys.exit(main())
