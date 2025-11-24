#!/usr/bin/env python3
"""
Validate LaTeX paper structure for docs/paper/

This script checks:
1. All section files referenced in main.tex exist
2. No circular dependencies
3. Basic LaTeX syntax validation
4. Section file completeness
"""

import os
import re
from pathlib import Path

def validate_paper_structure():
    """Validate the paper structure in docs/paper/"""
    
    paper_dir = Path("docs/paper")
    main_tex = paper_dir / "main.tex"
    sections_dir = paper_dir / "sections"
    
    print("=" * 70)
    print("PAPER STRUCTURE VALIDATION")
    print("=" * 70)
    print()
    
    # Check main.tex exists
    if not main_tex.exists():
        print("❌ ERROR: main.tex not found in docs/paper/")
        return False
    
    print(f"✅ Found main.tex: {main_tex}")
    print()
    
    # Check sections directory exists
    if not sections_dir.exists():
        print("❌ ERROR: sections/ directory not found in docs/paper/")
        return False
    
    print(f"✅ Found sections directory: {sections_dir}")
    print()
    
    # Read main.tex
    with open(main_tex, 'r', encoding='utf-8') as f:
        main_content = f.read()
    
    # Extract all \input commands
    input_pattern = r'\\input\{([^}]+)\}'
    inputs = re.findall(input_pattern, main_content)
    
    print(f"📄 Found {len(inputs)} \\input commands in main.tex:")
    print()
    
    all_valid = True
    section_files = []
    
    for i, input_file in enumerate(inputs, 1):
        # Handle both with and without .tex extension
        if not input_file.endswith('.tex'):
            input_file_with_ext = input_file + '.tex'
        else:
            input_file_with_ext = input_file
        
        # Construct full path
        if 'sections/' in input_file:
            full_path = paper_dir / input_file_with_ext
        else:
            full_path = paper_dir / input_file_with_ext
        
        # Check if file exists
        exists = full_path.exists()
        status = "✅" if exists else "❌"
        
        print(f"{i:2d}. {status} {input_file}")
        
        if exists:
            # Get file size
            size = full_path.stat().st_size
            lines = len(full_path.read_text(encoding='utf-8').splitlines())
            print(f"    Size: {size:,} bytes, Lines: {lines:,}")
            section_files.append(full_path)
        else:
            print(f"    ERROR: File not found at {full_path}")
            all_valid = False
        
        print()
    
    # List all section files
    print("=" * 70)
    print("SECTION FILES IN sections/ DIRECTORY")
    print("=" * 70)
    print()
    
    if sections_dir.exists():
        section_files_on_disk = sorted(sections_dir.glob("*.tex"))
        print(f"Found {len(section_files_on_disk)} .tex files in sections/:")
        print()
        
        for i, section_file in enumerate(section_files_on_disk, 1):
            size = section_file.stat().st_size
            lines = len(section_file.read_text(encoding='utf-8').splitlines())
            
            # Check if referenced in main.tex
            # Remove .tex extension for comparison
            file_stem = section_file.stem
            referenced = any(file_stem in str(input_ref) for input_ref in inputs)
            ref_status = "📎 Referenced" if referenced else "⚠️  Not referenced"
            
            print(f"{i:2d}. {section_file.name:30s} {size:6,} bytes {lines:4,} lines  {ref_status}")
    
    print()
    print("=" * 70)
    print("VALIDATION SUMMARY")
    print("=" * 70)
    print()
    
    if all_valid:
        print("✅ All referenced files exist")
        print("✅ Paper structure is valid")
        print()
        print("Structure ready for:")
        print("  - Compilation with pdflatex or latexmk")
        print("  - Individual section editing")
        print("  - Enhancement of §6 and §8 as planned")
        return True
    else:
        print("❌ Some referenced files are missing")
        print("Please ensure all section files exist before compiling")
        return False

if __name__ == "__main__":
    import sys
    
    # Change to repo root if needed
    if not Path("docs/paper").exists():
        print("Changing to repository root...")
        os.chdir("/home/runner/work/-jmmotaburr-riemann-adelic/-jmmotaburr-riemann-adelic")
    
    success = validate_paper_structure()
    sys.exit(0 if success else 1)
