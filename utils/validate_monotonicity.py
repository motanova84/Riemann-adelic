"""
Monotonicity validation utility for Riemann zeros.

Validates that zeros in zeros_t1e8.txt are in monotonically increasing order,
as expected from Odlyzko's data.
"""

def validate_monotonicity(file_path="zeros/zeros_t1e8.txt"):
    """Validate that zeros are in monotonically increasing order."""
    print("🔢 Validating monotonicity of zeros...")
    
    with open(file_path, 'r') as f:
        prev_zero = 0.0
        violations = 0
        
        for i, line in enumerate(f):
            try:
                zero = float(line.strip())
                if zero <= prev_zero:
                    print(f"❌ Monotonicity violation at line {i+1}: {zero} <= {prev_zero}")
                    violations += 1
                    if violations > 5:  # Stop after 5 violations to avoid spam
                        print("❌ Too many monotonicity violations, stopping check")
                        return False
                prev_zero = zero
            except ValueError:
                print(f"⚠️  Invalid numeric value at line {i+1}: {line.strip()}")
                continue
    
    if violations == 0:
        print("✅ All zeros are in monotonically increasing order")
        return True
    else:
        print(f"❌ Found {violations} monotonicity violations")
        return False

if __name__ == "__main__":
    import sys
    file_path = sys.argv[1] if len(sys.argv) > 1 else "zeros/zeros_t1e8.txt"
    success = validate_monotonicity(file_path)
    sys.exit(0 if success else 1)