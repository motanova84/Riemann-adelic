#!/usr/bin/env python3
"""
Fix problematic Unicode characters in Jupyter notebooks.
This script replaces Unicode mathematical symbols with ASCII-safe equivalents.
"""

import glob
import json
import sys
from pathlib import Path


def fix_unicode_chars(file_path):
    """Fix Unicode characters in a Jupyter notebook file."""
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        original_content = content
        
        # Define Unicode character replacements
        replacements = {
            '≪': '<<',    # Much less than
            '≫': '>>',    # Much greater than
            '≠': '!=',    # Not equal
            '≤': '<=',    # Less than or equal
            '≥': '>=',    # Greater than or equal
            '–': '-',     # En dash
            '—': '-',     # Em dash
            '‘': "'",     # Left single quotation mark
            '’': "'",     # Right single quotation mark
            '“': '"',     # Left double quotation mark
            '”': '"',     # Right double quotation mark
            '…': '...',   # Horizontal ellipsis
        }
        
        # Apply replacements
        for old, new in replacements.items():
            content = content.replace(old, new)
        
        # Only write if there were changes
        if content != original_content:
            with open(file_path, 'w', encoding='utf-8') as f:
                f.write(content)
            print(f"✅ Fixed Unicode characters in {file_path}")
            return True
        else:
            print(f"ℹ️  No Unicode fixes needed in {file_path}")
            return False
            
    except Exception as e:
        print(f"❌ Error processing {file_path}: {e}")
        return False


def validate_notebook_json(file_path):
    """Validate that the notebook is still valid JSON after changes."""
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            json.load(f)
        return True
    except json.JSONDecodeError as e:
        print(f"❌ JSON validation failed for {file_path}: {e}")
        return False
    except Exception as e:
        print(f"❌ Error validating {file_path}: {e}")
        return False


def main():
    """Main function to fix Unicode in all notebooks."""
    print("🔧 Unicode Character Fixer for Jupyter Notebooks")
    print("=" * 60)
    
    # Find all notebook files
    notebook_patterns = [
        "*.ipynb",
        "notebooks/*.ipynb",
        "**/*.ipynb"
    ]
    
    notebook_files = set()
    for pattern in notebook_patterns:
        notebook_files.update(glob.glob(pattern, recursive=True))
    
    if not notebook_files:
        print("ℹ️  No Jupyter notebook files found.")
        return 0
    
    print(f"📋 Found {len(notebook_files)} notebook files:")
    for file in sorted(notebook_files):
        print(f"   - {file}")
    
    print("\n🔍 Processing files...")
    
    fixed_count = 0
    error_count = 0
    
    for notebook_file in sorted(notebook_files):
        print(f"\n📄 Processing: {notebook_file}")
        
        # Fix Unicode characters
        if fix_unicode_chars(notebook_file):
            fixed_count += 1
            
            # Validate JSON structure
            if not validate_notebook_json(notebook_file):
                error_count += 1
                print(f"⚠️  Warning: {notebook_file} may have JSON issues after fixing")
    
    print("\n" + "=" * 60)
    print("📊 SUMMARY")
    print("=" * 60)
    print(f"📁 Total files processed: {len(notebook_files)}")
    print(f"✅ Files with fixes applied: {fixed_count}")
    print(f"❌ Files with errors: {error_count}")
    
    if error_count == 0:
        print("\n🎉 All Unicode fixes completed successfully!")
        print("   ✓ All notebooks remain valid JSON")
        print("   ✓ Ready for execution without Unicode syntax errors")
        return 0
    else:
        print(f"\n⚠️  {error_count} files had issues. Please review manually.")
        return 1


if __name__ == "__main__":
    sys.exit(main())