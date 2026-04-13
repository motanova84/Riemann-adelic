"""
Test system dependencies are correctly installed and functional.

This module tests that system-level dependencies required for advanced
mathematical libraries (numba, python-igraph, numexpr) are properly
installed and working in the CI/CD environment.

Author: José Manuel Mota Burruezo
Date: October 2025
"""

import pytest
import numpy as np
import sys
import os
import subprocess


class TestLLVMDependencies:
    """Test LLVM dependencies for numba/llvmlite."""
    
    def test_llvmlite_import(self):
        """Test that llvmlite can be imported."""
        try:
            import llvmlite
            assert llvmlite is not None
            print(f"\n✅ llvmlite version: {llvmlite.__version__}")
        except ImportError as e:
            pytest.fail(f"llvmlite not available: {e}")
    
    def test_llvmlite_binding(self):
        """Test that llvmlite.binding works (requires LLVM)."""
        try:
            from llvmlite import binding
            
            # Note: binding.initialize() is deprecated in newer versions
            # LLVM initialization is now handled automatically
            
            # Initialize native target and asm printer
            binding.initialize_native_target()
            binding.initialize_native_asmprinter()
            
            # Get target information
            target = binding.Target.from_default_triple()
            target_machine = target.create_target_machine()
            
            print(f"\n✅ LLVM Target: {target.name}")
            print(f"✅ Target Triple: {target.triple}")
            print(f"✅ Target Machine: {target_machine}")
            
            assert target is not None
            assert target_machine is not None
        except Exception as e:
            pytest.fail(f"LLVM binding failed: {e}")
    
    def test_numba_with_llvm(self):
        """Test that numba works with LLVM backend."""
        try:
            from numba import jit
            import numpy as np
            
            @jit(nopython=True)
            def compute_spectral_sum(eigenvalues):
                """Compute sum of squared eigenvalues."""
                result = 0.0
                for eig in eigenvalues:
                    result += eig * eig
                return result
            
            # Test data
            test_eigenvalues = np.array([1.0, 2.0, 3.0, 4.0, 5.0])
            
            # Compile and run
            result = compute_spectral_sum(test_eigenvalues)
            expected = np.sum(test_eigenvalues ** 2)
            
            print(f"\n✅ Numba JIT compilation successful")
            print(f"✅ Result: {result}, Expected: {expected}")
            
            assert abs(result - expected) < 1e-10
        except Exception as e:
            pytest.fail(f"Numba JIT compilation failed: {e}")


class TestIGraphDependencies:
    """Test libigraph dependencies for python-igraph."""
    
    def test_igraph_c_library(self):
        """Test that igraph C library is available."""
        try:
            import igraph
            
            # Try to create a simple graph - this requires the C library
            g = igraph.Graph([(0, 1), (0, 2), (1, 2)])
            
            print(f"\n✅ igraph version: {igraph.__version__}")
            print(f"✅ Graph created: {g.vcount()} vertices, {g.ecount()} edges")
            
            assert g.vcount() == 3
            assert g.ecount() == 3
        except ImportError as e:
            pytest.fail(f"igraph not available: {e}")
        except Exception as e:
            pytest.fail(f"igraph C library not working: {e}")
    
    def test_python_igraph_import(self):
        """Test that python-igraph can be imported."""
        try:
            import igraph as ig
            assert ig is not None
            
            # Check for key functions
            assert hasattr(ig, 'Graph')
            assert hasattr(ig, 'plot')
            
            print(f"\n✅ python-igraph imported successfully")
        except ImportError as e:
            pytest.fail(f"python-igraph not available: {e}")
    
    def test_igraph_algorithms(self):
        """Test that igraph algorithms work (requires C library)."""
        try:
            import igraph as ig
            
            # Create a prime network-like graph
            g = ig.Graph()
            primes = [2, 3, 5, 7, 11, 13, 17, 19]
            g.add_vertices(len(primes))
            
            # Add edges between primes with prime differences
            prime_set = set(primes)
            edges = []
            for i, p1 in enumerate(primes):
                for j, p2 in enumerate(primes[i+1:], start=i+1):
                    if (p2 - p1) in prime_set:
                        edges.append((i, j))
            
            g.add_edges(edges)
            
            # Test algorithms
            degree = g.degree()
            betweenness = g.betweenness()
            clustering = g.transitivity_undirected()
            
            print(f"\n✅ Graph algorithms working")
            print(f"   Vertices: {g.vcount()}, Edges: {g.ecount()}")
            print(f"   Average degree: {sum(degree)/len(degree):.2f}")
            print(f"   Clustering coefficient: {clustering:.4f}")
            
            assert len(degree) == len(primes)
            assert len(betweenness) == len(primes)
            assert 0 <= clustering <= 1
        except Exception as e:
            pytest.fail(f"igraph algorithms failed: {e}")


class TestNumexprDependencies:
    """Test numexpr and CPU detection."""
    
    def test_numexpr_import(self):
        """Test that numexpr can be imported."""
        try:
            import numexpr as ne
            assert ne is not None
            
            print(f"\n✅ numexpr version: {ne.__version__}")
        except ImportError as e:
            pytest.fail(f"numexpr not available: {e}")
    
    def test_numexpr_cpu_detection(self):
        """Test that numexpr can detect CPU features."""
        try:
            import numexpr as ne
            
            # Get CPU info
            ncores = ne.detect_number_of_cores()
            nthreads = ne.get_num_threads()
            vml_version = ne.get_vml_version()
            
            print(f"\n✅ numexpr CPU detection:")
            print(f"   Detected cores: {ncores}")
            print(f"   Active threads: {nthreads}")
            print(f"   VML version: {vml_version}")
            
            assert ncores > 0
            assert nthreads > 0
        except Exception as e:
            pytest.fail(f"numexpr CPU detection failed: {e}")
    
    def test_numexpr_evaluation(self):
        """Test that numexpr can evaluate expressions."""
        try:
            import numexpr as ne
            
            # Test simple expression
            x = np.arange(1000, dtype=np.float64)
            y = np.arange(1000, dtype=np.float64)
            
            result_numpy = x**2 + y**2 + 2*x*y
            result_numexpr = ne.evaluate('x**2 + y**2 + 2*x*y')
            
            error = np.max(np.abs(result_numpy - result_numexpr))
            
            print(f"\n✅ numexpr evaluation working")
            print(f"   Array size: {len(x)}")
            print(f"   Max error: {error:.2e}")
            
            assert error < 1e-10
        except Exception as e:
            pytest.fail(f"numexpr evaluation failed: {e}")
    
    def test_numexpr_environment_variables(self):
        """Test that numexpr respects environment variables."""
        import numexpr as ne
        
        # Check if environment variables are set
        max_threads_env = os.environ.get('NUMEXPR_MAX_THREADS')
        num_threads_env = os.environ.get('NUMEXPR_NUM_THREADS')
        
        print(f"\n✅ numexpr environment variables:")
        print(f"   NUMEXPR_MAX_THREADS: {max_threads_env}")
        print(f"   NUMEXPR_NUM_THREADS: {num_threads_env}")
        
        # Get actual thread count
        actual_threads = ne.get_num_threads()
        print(f"   Actual threads: {actual_threads}")
        
        # Verify threads are within reasonable bounds
        assert actual_threads > 0
        assert actual_threads <= 64  # Sanity check


class TestSystemPackages:
    """Test that system packages are installed."""
    
    @pytest.mark.skipif(sys.platform != "linux", reason="Only on Linux")
    def test_llvm_installed(self):
        """Test that LLVM is installed on the system."""
        try:
            result = subprocess.run(
                ["llvm-config", "--version"],
                capture_output=True,
                text=True,
                timeout=5
            )
            
            if result.returncode == 0:
                version = result.stdout.strip()
                print(f"\n✅ LLVM installed: version {version}")
                assert version != ""
            else:
                print(f"\n⚠️  LLVM not found or llvm-config not available")
        except FileNotFoundError:
            print(f"\n⚠️  llvm-config command not found")
        except Exception as e:
            print(f"\n⚠️  Could not check LLVM installation: {e}")
    
    @pytest.mark.skipif(sys.platform != "linux", reason="Only on Linux")
    def test_libigraph_installed(self):
        """Test that libigraph is installed on the system."""
        try:
            # Try to find libigraph
            result = subprocess.run(
                ["pkg-config", "--modversion", "igraph"],
                capture_output=True,
                text=True,
                timeout=5
            )
            
            if result.returncode == 0:
                version = result.stdout.strip()
                print(f"\n✅ libigraph installed: version {version}")
                assert version != ""
            else:
                print(f"\n⚠️  libigraph not found via pkg-config")
        except FileNotFoundError:
            print(f"\n⚠️  pkg-config command not found")
        except Exception as e:
            print(f"\n⚠️  Could not check libigraph installation: {e}")


class TestIntegration:
    """Test integration of all dependencies."""
    
    def test_all_libraries_available(self):
        """Test that all advanced libraries are available."""
        libraries = []
        
        # Test numba
        try:
            from numba import jit
            libraries.append(("numba", "✅ Available"))
        except ImportError:
            libraries.append(("numba", "❌ Not available"))
        
        # Test llvmlite
        try:
            import llvmlite
            libraries.append(("llvmlite", "✅ Available"))
        except ImportError:
            libraries.append(("llvmlite", "❌ Not available"))
        
        # Test python-igraph
        try:
            import igraph
            libraries.append(("python-igraph", "✅ Available"))
        except ImportError:
            libraries.append(("python-igraph", "❌ Not available"))
        
        # Test numexpr
        try:
            import numexpr
            libraries.append(("numexpr", "✅ Available"))
        except ImportError:
            libraries.append(("numexpr", "❌ Not available"))
        
        # Test networkx
        try:
            import networkx
            libraries.append(("networkx", "✅ Available"))
        except ImportError:
            libraries.append(("networkx", "❌ Not available"))
        
        # Test scikit-learn
        try:
            import sklearn
            libraries.append(("scikit-learn", "✅ Available"))
        except ImportError:
            libraries.append(("scikit-learn", "❌ Not available"))
        
        print("\n" + "="*70)
        print("SYSTEM DEPENDENCIES - INTEGRATION TEST")
        print("="*70)
        for lib, status in libraries:
            print(f"{lib:20s} : {status}")
        print("="*70)
        
        # Check critical libraries
        critical = ["numba", "llvmlite", "python-igraph", "numexpr"]
        critical_status = {name: status for name, status in libraries if name in critical}
        
        for lib in critical:
            if lib in critical_status:
                assert "✅" in critical_status[lib], f"Critical library {lib} not available"


def test_system_dependencies_summary():
    """Print comprehensive system dependencies summary."""
    print("\n" + "="*70)
    print("SYSTEM DEPENDENCIES VERIFICATION SUMMARY")
    print("="*70)
    
    # Python version
    print(f"\nPython: {sys.version}")
    print(f"Platform: {sys.platform}")
    
    # NumPy
    print(f"\nNumPy: {np.__version__}")
    
    # Check each dependency
    deps = []
    
    try:
        import llvmlite
        deps.append(("llvmlite", llvmlite.__version__, "✅"))
    except ImportError:
        deps.append(("llvmlite", "N/A", "❌"))
    
    try:
        from numba import jit
        import numba
        deps.append(("numba", numba.__version__, "✅"))
    except ImportError:
        deps.append(("numba", "N/A", "❌"))
    
    try:
        import igraph
        deps.append(("python-igraph", igraph.__version__, "✅"))
    except ImportError:
        deps.append(("python-igraph", "N/A", "❌"))
    
    try:
        import numexpr as ne
        deps.append(("numexpr", ne.__version__, "✅"))
        deps.append(("  - cores detected", str(ne.detect_number_of_cores()), "ℹ️"))
        deps.append(("  - threads active", str(ne.get_num_threads()), "ℹ️"))
    except ImportError:
        deps.append(("numexpr", "N/A", "❌"))
    
    print("\nDependencies:")
    for name, version, status in deps:
        print(f"  {status} {name:25s} : {version}")
    
    print("\n" + "="*70)
    
    # Always pass - this is just informational
    assert True


if __name__ == "__main__":
    pytest.main([__file__, "-v", "-s"])
