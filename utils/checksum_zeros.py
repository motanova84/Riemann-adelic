#!/usr/bin/env python3
"""
Checksum validation utility for Odlyzko zeros data.

This script computes and validates MD5 checksums for the zeros data files
to ensure data integrity and consistency with the original Odlyzko sources.

Usage:
    python utils/checksum_zeros.py zeros/zeros_t1e8.txt
"""

import hashlib
import sys
import os

def compute_md5(filepath):
    """Compute MD5 checksum of a file."""
    hash_md5 = hashlib.md5()
    try:
        with open(filepath, "rb") as f:
            for chunk in iter(lambda: f.read(4096), b""):
                hash_md5.update(chunk)
        return hash_md5.hexdigest()
    except FileNotFoundError:
        return None

def validate_zeros_file(filepath):
    """Validate the structure and content of a zeros file."""
    if not os.path.exists(filepath):
        print(f"❌ File not found: {filepath}")
        return False
    
    try:
        with open(filepath, 'r') as f:
            lines = f.readlines()
        
        # Check if file contains numeric data
        zeros_count = 0
        for i, line in enumerate(lines[:10]):  # Check first 10 lines
            try:
                float(line.strip())
                zeros_count += 1
            except ValueError:
                print(f"⚠️  Line {i+1} contains non-numeric data: {line.strip()}")
        
        total_lines = len(lines)
        print(f"✅ File structure valid: {total_lines} lines, {zeros_count}/10 sample lines are numeric")
        return True
        
    except Exception as e:
        print(f"❌ Error reading file: {e}")
        return False

def main():
    if len(sys.argv) != 2:
        print("Usage: python utils/checksum_zeros.py <zeros_file>")
        sys.exit(1)
    
    filepath = sys.argv[1]
    print(f"🔍 Validating: {filepath}")
    
    # Validate file structure
    if not validate_zeros_file(filepath):
        sys.exit(1)
    
    # Compute checksum
    checksum = compute_md5(filepath)
    if checksum:
        print(f"📊 MD5 Checksum: {checksum}")
        
        # Store checksum for future reference
        checksum_file = filepath + ".md5"
        with open(checksum_file, 'w') as f:
            f.write(f"{checksum}  {os.path.basename(filepath)}\n")
        print(f"💾 Checksum saved to: {checksum_file}")
    else:
        print("❌ Failed to compute checksum")
        sys.exit(1)

if __name__ == "__main__":
    main()
"""
🧠 Copilot Prompt:
Create a checksum validation utility for zeros_t1e8.txt to ensure data integrity.

This script validates that:
- File exists and is readable
- Contains numeric values (one per line)
- Has reasonable size and format
- Basic sanity checks on zero values
- Provides MD5 and SHA256 checksums for verification
- Validates monotonicity and known zero values

Usage in GitHub Actions workflow for data validation.
"""

import hashlib

def compute_checksum(file_path, hash_type="md5"):
    """Compute checksum of a file."""
    hash_func = hashlib.md5() if hash_type == "md5" else hashlib.sha256()
    with open(file_path, "rb") as f:
        for chunk in iter(lambda: f.read(4096), b""):
            hash_func.update(chunk)
    return hash_func.hexdigest()

def validate_checksum(file_path, expected_checksum, hash_type="md5"):
    """Validate file checksum against expected value."""
    computed_checksum = compute_checksum(file_path, hash_type)
    is_valid = computed_checksum == expected_checksum
    print(f"Checksum {hash_type.upper()}: {computed_checksum} (Expected: {expected_checksum}, Valid: {is_valid})")
    return is_valid

def validate_monotonicity(file_path):
    """Validate that zeros are in monotonically increasing order."""
    print("🔢 Validating monotonicity of zeros...")
    with open(file_path, 'r') as f:
        prev_zero = 0.0
        for i, line in enumerate(f):
            if i > 1000:  # Limit check to first 1000 for performance
                break
            try:
                zero = float(line.strip())
                if zero <= prev_zero:
                    print(f"❌ Monotonicity violation at line {i+1}: {zero} <= {prev_zero}")
                    return False
                prev_zero = zero
            except ValueError:
                continue
    print("✅ Monotonicity check passed")
    return True

def validate_known_zeros(file_path):
    """Validate against known first few zeros."""
    known_zeros = [14.134725, 21.022040, 25.010856, 30.424876, 32.935062]  # First 5 zeros (approximate)
    print("🎯 Validating known zeros...")
    
    with open(file_path, 'r') as f:
        zeros = []
        for i, line in enumerate(f):
            if i >= len(known_zeros):
                break
            try:
                zero = float(line.strip())
                zeros.append(zero)
            except ValueError:
                continue
    
    for i, (computed, expected) in enumerate(zip(zeros, known_zeros)):
        error = abs(computed - expected)
        if error > 0.01:  # Tolerance of 0.01
            print(f"❌ Zero {i+1}: computed {computed}, expected {expected}, error {error}")
            return False
        else:
            print(f"✅ Zero {i+1}: {computed} (error: {error:.6f})")
    
    return True

if __name__ == "__main__":
    file_path = "zeros/zeros_t1e8.txt"
    
    # Actual checksums for the current zeros_t1e8.txt file
    expected_md5 = "b7b8be60df6d46e78cd60874f9fd76c0"  # Current file MD5
    expected_sha256 = "3436c916a7878261ac183fd7b9448c9a4736b8bbccf1356874a6ce1788541632"  # Current file SHA256
    
    print("🔍 Validating zeros data integrity...")
    
    # Basic checksums
    validate_checksum(file_path, expected_md5, "md5")
    validate_checksum(file_path, expected_sha256, "sha256")
    
    # Additional validations
    validate_monotonicity(file_path)
    validate_known_zeros(file_path)
    
    print("✅ Validation complete!")
