"""
Known zeros validation utility.

Validates that the first few zeros in zeros_t1e8.txt match 
well-known theoretical values with high precision.
"""

def get_precise_known_zeros():
    """Return first 10 Riemann zeros with high precision."""
    return [
        14.134725141734693790,
        21.022039638771754864,
        25.010857580145688763,
        30.424876125859513210,
        32.935061587739189690,
        37.586178158825671257,
        40.918719012147495187,
        43.327073280914999519,
        48.005150881167159727,
        49.773832477672302181
    ]

def validate_known_zeros(file_path="zeros/zeros_t1e8.txt", tolerance=1e-6):
    """Validate first zeros against known high-precision values."""
    known_zeros = get_precise_known_zeros()
    
    print("🎯 Validating against known high-precision zeros...")
    print(f"📏 Tolerance: {tolerance}")
    
    with open(file_path, 'r') as f:
        file_zeros = []
        for i, line in enumerate(f):
            if i >= len(known_zeros):
                break
            try:
                zero = float(line.strip())
                file_zeros.append(zero)
            except ValueError:
                print(f"⚠️  Invalid value at line {i+1}: {line.strip()}")
                continue
    
    all_valid = True
    max_error = 0.0
    
    for i, (file_zero, known_zero) in enumerate(zip(file_zeros, known_zeros)):
        error = abs(file_zero - known_zero)
        max_error = max(max_error, error)
        
        if error <= tolerance:
            print(f"✅ Zero {i+1}: {file_zero:.12f} (error: {error:.2e})")
        else:
            print(f"❌ Zero {i+1}: {file_zero:.12f}, expected {known_zero:.12f} (error: {error:.2e})")
            all_valid = False
    
    print(f"\n📊 Summary:")
    print(f"   Max error: {max_error:.2e}")
    print(f"   Within tolerance: {'✅' if all_valid else '❌'}")
    print(f"   Validated {len(file_zeros)} zeros")
    
    return all_valid

if __name__ == "__main__":
    import sys
    
    file_path = "zeros/zeros_t1e8.txt"
    tolerance = 1e-6
    
    # Parse command line arguments
    if len(sys.argv) > 1:
        file_path = sys.argv[1]
    if len(sys.argv) > 2:
        tolerance = float(sys.argv[2])
    
    success = validate_known_zeros(file_path, tolerance)
    sys.exit(0 if success else 1)