#!/usr/bin/env python3
"""
Validate LaTeX syntax of paper_standalone.tex
Checks for common issues like unmatched braces, environments, etc.
"""

import re
import sys

def validate_latex_file(filename):
    """Validate basic LaTeX syntax."""
    errors = []
    warnings = []
    
    with open(filename, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # Check for balanced braces
    brace_count = 0
    for i, char in enumerate(content):
        if char == '{':
            brace_count += 1
        elif char == '}':
            brace_count -= 1
        if brace_count < 0:
            errors.append(f"Unmatched closing brace at position {i}")
            break
    
    if brace_count > 0:
        errors.append(f"Unmatched opening braces: {brace_count} extra")
    
    # Check for balanced square brackets in math mode
    bracket_count = content.count('[') - content.count(']')
    if bracket_count != 0:
        warnings.append(f"Potentially unbalanced square brackets: {bracket_count} difference")
    
    # Check for begin/end environment matching
    begin_pattern = r'\\begin\{([^}]+)\}'
    end_pattern = r'\\end\{([^}]+)\}'
    
    begins = re.findall(begin_pattern, content)
    ends = re.findall(end_pattern, content)
    
    begin_counter = {}
    for env in begins:
        begin_counter[env] = begin_counter.get(env, 0) + 1
    
    end_counter = {}
    for env in ends:
        end_counter[env] = end_counter.get(env, 0) + 1
    
    for env in set(begins + ends):
        begin_count = begin_counter.get(env, 0)
        end_count = end_counter.get(env, 0)
        if begin_count != end_count:
            errors.append(f"Unmatched environment '{env}': {begin_count} begin, {end_count} end")
    
    # Check for document environment
    if '\\begin{document}' not in content:
        errors.append("Missing \\begin{document}")
    if '\\end{document}' not in content:
        errors.append("Missing \\end{document}")
    
    # Check for required structure elements
    if '\\documentclass' not in content:
        errors.append("Missing \\documentclass")
    if '\\title' not in content:
        warnings.append("Missing \\title")
    if '\\author' not in content:
        warnings.append("Missing \\author")
    
    # Check for common typos
    common_typos = [
        (r'\\text\s+', 'Space after \\text (should be \\text{...})'),
        (r'\\frac\s+', 'Space after \\frac (should be \\frac{...}{...})'),
    ]
    
    for pattern, message in common_typos:
        if re.search(pattern, content):
            warnings.append(message)
    
    # Report results
    print(f"Validating {filename}...")
    print(f"File size: {len(content)} characters")
    print(f"Lines: {content.count(chr(10)) + 1}")
    print()
    
    if errors:
        print(f"❌ ERRORS ({len(errors)}):")
        for error in errors:
            print(f"  - {error}")
        print()
    else:
        print("✅ No errors found")
        print()
    
    if warnings:
        print(f"⚠️  WARNINGS ({len(warnings)}):")
        for warning in warnings:
            print(f"  - {warning}")
        print()
    else:
        print("✅ No warnings")
        print()
    
    # Check structure
    sections = re.findall(r'\\section\{([^}]+)\}', content)
    print(f"📑 Document structure: {len(sections)} sections")
    for i, section in enumerate(sections, 1):
        print(f"  {i}. {section}")
    print()
    
    appendices = re.findall(r'\\section\{([^}]+)\}', content[content.find('\\appendix'):] if '\\appendix' in content else '')
    if appendices:
        print(f"📎 Appendices: {len(appendices)}")
        for i, app in enumerate(appendices, 1):
            print(f"  {chr(64+i)}. {app}")
    
    return len(errors) == 0

if __name__ == '__main__':
    filename = 'paper_standalone.tex'
    success = validate_latex_file(filename)
    sys.exit(0 if success else 1)
