#!/usr/bin/env python3
"""
Setup automation for Copilot automerge workflow.
This script helps configure the repository for complete automation.
"""

import os
import subprocess
import sys
import json
from pathlib import Path


def run_command(cmd, capture_output=True, check=True):
    """Run a shell command and return the result."""
    try:
        result = subprocess.run(
            cmd,
            shell=True,
            capture_output=capture_output,
            text=True,
            check=check
        )
        return result
    except subprocess.CalledProcessError as e:
        print(f"❌ Command failed: {cmd}")
        print(f"Error: {e.stderr}")
        return None


def check_dependencies():
    """Check if required dependencies are available."""
    print("🔍 Checking dependencies...")
    
    dependencies = {
        'git': 'git --version',
        'python': 'python --version',
        'gh': 'gh --version'  # GitHub CLI (optional but recommended)
    }
    
    missing = []
    for name, cmd in dependencies.items():
        result = run_command(cmd, check=False)
        if result and result.returncode == 0:
            print(f"✅ {name}: {result.stdout.strip()}")
        else:
            print(f"❌ {name}: Not found")
            missing.append(name)
    
    if missing:
        print(f"\n⚠️ Missing dependencies: {', '.join(missing)}")
        if 'gh' in missing:
            print("💡 Install GitHub CLI for full automation: https://cli.github.com/")
        return False
    
    return True


def validate_repository_structure():
    """Validate that the repository has the required structure."""
    print("\n📁 Validating repository structure...")
    
    required_files = [
        'requirements.txt',
        'validar_v5_coronacion.py',
        'validate_explicit_formula.py',
        'utils/mellin.py',
        'tests/test_validation.py',
        'docs/paper/main.tex',
        'docs/paper/Makefile',
        '.github/workflows/copilot-automerge.yml'
    ]
    
    required_dirs = [
        'zeros',
        'data', 
        'logs',
        'utils',
        'tests',
        'docs',
        '.github/workflows'
    ]
    
    missing_files = []
    missing_dirs = []
    
    for file_path in required_files:
        if not os.path.exists(file_path):
            missing_files.append(file_path)
        else:
            print(f"✅ {file_path}")
    
    for dir_path in required_dirs:
        if not os.path.exists(dir_path):
            missing_dirs.append(dir_path)
        else:
            print(f"✅ {dir_path}/")
    
    if missing_files or missing_dirs:
        print(f"\n❌ Missing files: {missing_files}")
        print(f"❌ Missing directories: {missing_dirs}")
        return False
    
    return True


def test_basic_functionality():
    """Test basic functionality of key scripts."""
    print("\n🧪 Testing basic functionality...")
    
    # Test pytest
    print("Testing pytest...")
    result = run_command("python -m pytest --version", check=False)
    if result and result.returncode == 0:
        print("✅ pytest available")
    else:
        print("❌ pytest not available")
        return False
    
    # Test validation script
    print("Testing validation script...")
    result = run_command("python validar_v5_coronacion.py --help", check=False)
    if result and result.returncode == 0:
        print("✅ validar_v5_coronacion.py working")
    else:
        print("❌ validar_v5_coronacion.py failed")
        return False
    
    # Test LaTeX (if available)
    print("Testing LaTeX compilation...")
    result = run_command("which pdflatex", check=False)
    if result and result.returncode == 0:
        print("✅ LaTeX available")
    else:
        print("⚠️ LaTeX not available (will be installed in CI)")
    
    return True


def setup_git_hooks():
    """Setup git hooks for better automation."""
    print("\n🔗 Setting up git hooks...")
    
    hooks_dir = Path('.git/hooks')
    if not hooks_dir.exists():
        print("❌ Not in a git repository")
        return False
    
    # Create pre-commit hook
    pre_commit_hook = hooks_dir / 'pre-commit'
    pre_commit_content = '''#!/bin/bash
# Auto-format Python files before commit
echo "🔧 Running pre-commit formatting..."

# Format Python files
for file in $(git diff --cached --name-only --diff-filter=ACM | grep '\\.py$'); do
    if command -v autopep8 >/dev/null 2>&1; then
        autopep8 --in-place --aggressive "$file"
        git add "$file"
    fi
done

echo "✅ Pre-commit checks completed"
exit 0
'''
    
    try:
        with open(pre_commit_hook, 'w') as f:
            f.write(pre_commit_content)
        os.chmod(pre_commit_hook, 0o755)
        print("✅ Pre-commit hook installed")
    except Exception as e:
        print(f"⚠️ Could not install pre-commit hook: {e}")
    
    return True


def generate_automation_report():
    """Generate a report on the current automation setup."""
    print("\n📋 Generating automation report...")
    
    report = {
        'timestamp': subprocess.run(['date'], capture_output=True, text=True).stdout.strip(),
        'repository': os.path.basename(os.getcwd()),
        'workflows': [],
        'status': {}
    }
    
    # Check workflows
    workflows_dir = Path('.github/workflows')
    if workflows_dir.exists():
        for workflow_file in workflows_dir.glob('*.yml'):
            report['workflows'].append(workflow_file.name)
    
    # Check automation status
    automation_checks = {
        'copilot_workflow': os.path.exists('.github/workflows/copilot-automerge.yml'),
        'branch_protection_guide': os.path.exists('.github/branch-protection.md'),
        'requirements_file': os.path.exists('requirements.txt'),
        'test_suite': os.path.exists('tests/test_validation.py'),
        'validation_script': os.path.exists('validar_v5_coronacion.py'),
        'latex_document': os.path.exists('docs/paper/main.tex'),
    }
    
    report['status'] = automation_checks
    
    # Save report
    with open('automation_setup_report.json', 'w') as f:
        json.dump(report, f, indent=2)
    
    print("✅ Automation report generated: automation_setup_report.json")
    
    # Print summary
    print(f"\n📊 Automation Setup Summary:")
    for check, status in automation_checks.items():
        status_emoji = "✅" if status else "❌"
        print(f"{status_emoji} {check.replace('_', ' ').title()}")
    
    return report


def main():
    """Main setup function."""
    print("🤖 Copilot Automation Setup")
    print("=" * 50)
    
    # Check if we're in the right directory
    if not os.path.exists('.git'):
        print("❌ This doesn't appear to be a git repository")
        print("Please run this script from the repository root")
        sys.exit(1)
    
    success_count = 0
    total_steps = 5
    
    # Step 1: Check dependencies
    if check_dependencies():
        success_count += 1
    
    # Step 2: Validate repository structure
    if validate_repository_structure():
        success_count += 1
    
    # Step 3: Test basic functionality
    if test_basic_functionality():
        success_count += 1
    
    # Step 4: Setup git hooks
    if setup_git_hooks():
        success_count += 1
    
    # Step 5: Generate report
    report = generate_automation_report()
    if report:
        success_count += 1
    
    # Final summary
    print("\n" + "=" * 50)
    print(f"🎯 Setup completed: {success_count}/{total_steps} steps successful")
    
    if success_count == total_steps:
        print("🏆 Automation setup complete!")
        print("\n📋 Next steps:")
        print("1. Review .github/branch-protection.md for GitHub settings")
        print("2. Configure branch protection rules in repository settings")
        print("3. Test with a copilot/fix-* branch")
        print("4. Enable auto-merge in repository settings")
    else:
        print("⚠️ Some setup steps failed. Review the output above.")
        print("💡 The automation may still work, but some features might be limited.")
    
    print(f"\n📄 Detailed report saved to: automation_setup_report.json")
    return success_count == total_steps


if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)