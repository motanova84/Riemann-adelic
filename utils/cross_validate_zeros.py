"""
Cross-validation utility for Riemann zeros using SageMath (if available).

Compares first few zeros from zeros_t1e8.txt with SageMath computation.
Falls back to known theoretical values if SageMath is not available.
"""

def get_known_zeros():
    """Return first 10 known Riemann zeros (approximate values)."""
    return [
        14.134725141734694,
        21.022039638771755,
        25.010857580145688,
        30.424876125859513,
        32.935061587739190,
        37.586178158825671,
        40.918719012147495,
        43.327073280914999,
        48.005150881167159,
        49.773832477672302
    ]

def validate_with_sagemath(file_path="zeros/zeros_t1e8.txt", num_zeros=10):
    """Validate zeros using SageMath computation (if available)."""
    try:
        # Try to import SageMath - this will fail if not installed
        import sage.all as sage
        
        print("📊 Cross-validating with SageMath...")
        
        with open(file_path, 'r') as f:
            file_zeros = []
            for i, line in enumerate(f):
                if i >= num_zeros:
                    break
                try:
                    zero = float(line.strip())
                    file_zeros.append(zero)
                except ValueError:
                    continue
        
        # Compute zeros using SageMath
        sage_zeros = []
        for i in range(1, num_zeros + 1):
            zero = float(sage.zeta_zeros(i)[0].imag())
            sage_zeros.append(zero)
        
        # Compare
        max_error = 0.0
        for i, (file_zero, sage_zero) in enumerate(zip(file_zeros, sage_zeros)):
            error = abs(file_zero - sage_zero)
            max_error = max(max_error, error)
            print(f"Zero {i+1}: File={file_zero:.6f}, SageMath={sage_zero:.6f}, Error={error:.6f}")
        
        print(f"✅ SageMath cross-validation complete. Max error: {max_error:.6f}")
        return max_error < 0.001  # Tolerance of 0.001
        
    except ImportError:
        print("⚠️  SageMath not available, falling back to known values")
        return validate_with_known_values(file_path, num_zeros)

def validate_with_known_values(file_path="zeros/zeros_t1e8.txt", num_zeros=10):
    """Validate against known theoretical zero values."""
    known_zeros = get_known_zeros()[:num_zeros]
    
    print("🎯 Validating against known theoretical values...")
    
    with open(file_path, 'r') as f:
        file_zeros = []
        for i, line in enumerate(f):
            if i >= num_zeros:
                break
            try:
                zero = float(line.strip())
                file_zeros.append(zero)
            except ValueError:
                continue
    
    max_error = 0.0
    for i, (file_zero, known_zero) in enumerate(zip(file_zeros, known_zeros)):
        error = abs(file_zero - known_zero)
        max_error = max(max_error, error)
        status = "✅" if error < 0.001 else "❌"
        print(f"{status} Zero {i+1}: File={file_zero:.6f}, Known={known_zero:.6f}, Error={error:.6f}")
    
    success = max_error < 0.001
    print(f"{'✅' if success else '❌'} Cross-validation complete. Max error: {max_error:.6f}")
    return success

if __name__ == "__main__":
    import sys
    file_path = sys.argv[1] if len(sys.argv) > 1 else "zeros/zeros_t1e8.txt"
    success = validate_with_sagemath(file_path)
    sys.exit(0 if success else 1)