#!/usr/bin/env python3
"""
Quick validation script for system dependencies.

This script checks that all required system dependencies for advanced
mathematical libraries are correctly installed and functional.

Usage:
    python validate_system_dependencies.py
    
Exit codes:
    0 - All dependencies working correctly
    1 - One or more critical dependencies missing or not working
    
Author: José Manuel Mota Burruezo
Date: October 2025
"""

import sys
import subprocess


def print_header(title):
    """Print a section header."""
    print("\n" + "=" * 70)
    print(f"  {title}")
    print("=" * 70)


def check_python_package(package_name, import_name=None):
    """Check if a Python package can be imported."""
    if import_name is None:
        import_name = package_name
    
    try:
        module = __import__(import_name)
        version = getattr(module, '__version__', 'unknown')
        print(f"  ✅ {package_name:20s} : {version}")
        return True
    except ImportError:
        print(f"  ❌ {package_name:20s} : NOT INSTALLED")
        return False


def check_system_command(command, package_hint=None):
    """Check if a system command exists."""
    try:
        result = subprocess.run(
            [command, "--version"],
            capture_output=True,
            text=True,
            timeout=5
        )
        if result.returncode == 0:
            version = result.stdout.strip().split('\n')[0]
            print(f"  ✅ {command:20s} : {version}")
            return True
        else:
            print(f"  ⚠️  {command:20s} : NOT FOUND")
            if package_hint:
                print(f"      Install with: sudo apt-get install {package_hint}")
            return False
    except FileNotFoundError:
        print(f"  ⚠️  {command:20s} : NOT FOUND")
        if package_hint:
            print(f"      Install with: sudo apt-get install {package_hint}")
        return False
    except Exception as e:
        print(f"  ⚠️  {command:20s} : ERROR ({e})")
        return False


def check_llvm_binding():
    """Check LLVM binding functionality."""
    try:
        from llvmlite import binding
        binding.initialize_native_target()
        binding.initialize_native_asmprinter()
        target = binding.Target.from_default_triple()
        print(f"  ✅ LLVM binding       : {target.triple}")
        return True
    except Exception as e:
        print(f"  ❌ LLVM binding       : FAILED ({e})")
        return False


def check_numba_jit():
    """Check numba JIT compilation."""
    try:
        from numba import jit
        import numpy as np
        
        @jit(nopython=True)
        def test_func(x):
            return x * x
        
        result = test_func(5.0)
        assert result == 25.0
        print(f"  ✅ numba JIT          : Working")
        return True
    except Exception as e:
        print(f"  ❌ numba JIT          : FAILED ({e})")
        return False


def check_igraph_c_library():
    """Check igraph C library functionality."""
    try:
        import igraph
        g = igraph.Graph([(0, 1), (1, 2)])
        assert g.vcount() == 3
        assert g.ecount() == 2
        print(f"  ✅ igraph C library   : Working")
        return True
    except Exception as e:
        print(f"  ❌ igraph C library   : FAILED ({e})")
        return False


def check_numexpr_evaluation():
    """Check numexpr evaluation."""
    try:
        import numexpr as ne
        import numpy as np
        
        x = np.array([1.0, 2.0, 3.0])
        result = ne.evaluate('x**2')
        expected = np.array([1.0, 4.0, 9.0])
        assert np.allclose(result, expected)
        
        ncores = ne.detect_number_of_cores()
        nthreads = ne.get_num_threads()
        print(f"  ✅ numexpr evaluation : Working ({ncores} cores, {nthreads} threads)")
        return True
    except Exception as e:
        print(f"  ❌ numexpr evaluation : FAILED ({e})")
        return False


def main():
    """Main validation function."""
    print_header("SYSTEM DEPENDENCIES VALIDATION")
    
    print("\nPython Environment:")
    print(f"  Python: {sys.version.split()[0]}")
    print(f"  Platform: {sys.platform}")
    
    # Check Python packages
    print_header("Python Packages")
    results = []
    
    results.append(check_python_package("numpy"))
    results.append(check_python_package("scipy"))
    results.append(check_python_package("mpmath"))
    results.append(check_python_package("llvmlite"))
    results.append(check_python_package("numba"))
    results.append(check_python_package("python-igraph", "igraph"))
    results.append(check_python_package("numexpr"))
    results.append(check_python_package("networkx"))
    results.append(check_python_package("scikit-learn", "sklearn"))
    
    # Check system commands
    print_header("System Commands")
    
    check_system_command("llvm-config", "llvm-14-dev")
    check_system_command("pkg-config")
    
    # Check LLVM binding
    print_header("LLVM Binding")
    results.append(check_llvm_binding())
    
    # Check numba JIT
    print_header("numba JIT Compilation")
    results.append(check_numba_jit())
    
    # Check igraph C library
    print_header("igraph C Library")
    results.append(check_igraph_c_library())
    
    # Check numexpr evaluation
    print_header("numexpr Evaluation")
    results.append(check_numexpr_evaluation())
    
    # Summary
    print_header("VALIDATION SUMMARY")
    
    total = len(results)
    passed = sum(results)
    failed = total - passed
    
    print(f"\n  Total checks: {total}")
    print(f"  ✅ Passed: {passed}")
    print(f"  ❌ Failed: {failed}")
    
    if failed == 0:
        print("\n  ✅ ALL DEPENDENCIES WORKING CORRECTLY")
        print("\n" + "=" * 70)
        return 0
    else:
        print("\n  ⚠️  SOME DEPENDENCIES NOT WORKING")
        print("\n  To install missing system dependencies:")
        print("    sudo apt-get update")
        print("    sudo apt-get install -y llvm-14 llvm-14-dev libigraph-dev libigraph3t64")
        print("\n  To install missing Python packages:")
        print("    pip install -r requirements.txt")
        print("\n" + "=" * 70)
        return 1


if __name__ == "__main__":
    sys.exit(main())
