#!/usr/bin/env python3
"""
Placeholder validation script for Lean formalization
Counts 'sorry' and 'admit' placeholders in Lean files
"""
import os
import re
from pathlib import Path

def count_placeholders(dir_path):
    """Count sorry and admit placeholders in Lean files"""
    total_sorry = 0
    total_admit = 0
    file_details = []
    
    for root, _, files in os.walk(dir_path):
        for file in files:
            if file.endswith('.lean'):
                path = os.path.join(root, file)
                try:
                    with open(path, 'r', encoding='utf-8') as f:
                        content = f.read()
                        sorry_count = len(re.findall(r'\bsorry\b', content, re.IGNORECASE))
                        admit_count = len(re.findall(r'\badmit\b', content, re.IGNORECASE))
                        
                        if sorry_count > 0 or admit_count > 0:
                            rel_path = os.path.relpath(path, dir_path)
                            file_details.append((rel_path, sorry_count, admit_count))
                        
                        total_sorry += sorry_count
                        total_admit += admit_count
                except Exception as e:
                    print(f"Error reading {path}: {e}")
    
    return total_sorry, total_admit, file_details

if __name__ == "__main__":
    lean_dir = Path(__file__).parent / 'formalization' / 'lean'
    
    if not lean_dir.exists():
        print(f"Lean directory not found: {lean_dir}")
        exit(1)
    
    sorry_count, admit_count, file_details = count_placeholders(lean_dir)
    
    print("=" * 70)
    print("QCAL ∞³ PLACEHOLDER VALIDATION REPORT")
    print("=" * 70)
    print(f"\nTotal sorry: {sorry_count}")
    print(f"Total admit: {admit_count}")
    print(f"Total placeholders: {sorry_count + admit_count}")
    
    if file_details:
        print("\n" + "=" * 70)
        print("DETAILED BREAKDOWN BY FILE")
        print("=" * 70)
        file_details.sort(key=lambda x: (x[1] + x[2]), reverse=True)
        for file, sorry, admit in file_details[:20]:  # Top 20 files
            if sorry > 0 or admit > 0:
                print(f"\n{file}")
                print(f"  sorry: {sorry}, admit: {admit}")
    
    print("\n" + "=" * 70)
    if sorry_count == 0 and admit_count == 0:
        print("✅ SUCCESS: All placeholders resolved!")
        print("The formalization is complete with 0 sorry and 0 admit.")
        exit(0)
    else:
        print(f"⚠️  INCOMPLETE: {sorry_count + admit_count} placeholders remaining")
        print("Continue working on closing sorry/admit statements.")
        exit(1)
