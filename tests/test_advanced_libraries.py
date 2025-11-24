"""
Tests for advanced mathematical libraries integration.

This module tests the integration and functionality of advanced mathematical
libraries in the Riemann-Adelic framework.

Author: José Manuel Mota Burruezo
Date: October 2025
"""

import pytest
import numpy as np
import sys
import os

# Check library availability
try:
    from numba import jit
    NUMBA_AVAILABLE = True
except ImportError:
    NUMBA_AVAILABLE = False

try:
    import networkx as nx
    NETWORKX_AVAILABLE = True
except ImportError:
    NETWORKX_AVAILABLE = False

try:
    from sklearn.decomposition import PCA
    SKLEARN_AVAILABLE = True
except ImportError:
    SKLEARN_AVAILABLE = False

try:
    import numexpr as ne
    NUMEXPR_AVAILABLE = True
except ImportError:
    NUMEXPR_AVAILABLE = False


class TestNumbaIntegration:
    """Test Numba JIT compilation integration."""
    
    @pytest.mark.skipif(not NUMBA_AVAILABLE, reason="Numba not installed")
    def test_numba_import(self):
        """Test that numba can be imported."""
        from numba import jit
        assert jit is not None
    
    @pytest.mark.skipif(not NUMBA_AVAILABLE, reason="Numba not installed")
    def test_simple_jit_function(self):
        """Test a simple JIT-compiled function."""
        from numba import jit
        
        @jit(nopython=True)
        def add_arrays(a, b):
            return a + b
        
        x = np.array([1.0, 2.0, 3.0])
        y = np.array([4.0, 5.0, 6.0])
        result = add_arrays(x, y)
        
        expected = np.array([5.0, 7.0, 9.0])
        np.testing.assert_array_almost_equal(result, expected)
    
    @pytest.mark.skipif(not NUMBA_AVAILABLE, reason="Numba not installed")
    def test_spectral_density_jit(self):
        """Test JIT-compiled spectral density computation."""
        from numba import jit
        
        @jit(nopython=True)
        def spectral_density(eigenvalues, t, sigma=0.1):
            result = 0.0
            for lam in eigenvalues:
                result += np.exp(-((lam - t)**2) / (2 * sigma**2))
            return result / (sigma * np.sqrt(2 * np.pi))
        
        eigenvalues = np.array([1.0, 2.0, 3.0])
        t = 2.0
        density = spectral_density(eigenvalues, t)
        
        assert density > 0
        assert np.isfinite(density)


class TestNetworkXIntegration:
    """Test NetworkX graph theory integration."""
    
    @pytest.mark.skipif(not NETWORKX_AVAILABLE, reason="NetworkX not installed")
    def test_networkx_import(self):
        """Test that NetworkX can be imported."""
        import networkx as nx
        assert nx is not None
    
    @pytest.mark.skipif(not NETWORKX_AVAILABLE, reason="NetworkX not installed")
    def test_prime_network_creation(self):
        """Test creation of prime number network."""
        import networkx as nx
        
        # Small set of primes
        primes = [2, 3, 5, 7, 11, 13]
        
        G = nx.Graph()
        G.add_nodes_from(primes)
        
        # Connect primes if difference is prime
        prime_set = set(primes)
        for i, p1 in enumerate(primes):
            for p2 in primes[i+1:]:
                if (p2 - p1) in prime_set:
                    G.add_edge(p1, p2)
        
        assert G.number_of_nodes() == len(primes)
        assert G.number_of_edges() >= 0
    
    @pytest.mark.skipif(not NETWORKX_AVAILABLE, reason="NetworkX not installed")
    def test_graph_centrality(self):
        """Test graph centrality measures."""
        import networkx as nx
        
        G = nx.Graph()
        G.add_edges_from([(1, 2), (2, 3), (3, 4), (4, 1)])
        
        centrality = nx.degree_centrality(G)
        
        assert len(centrality) == 4
        assert all(0 <= c <= 1 for c in centrality.values())


class TestSklearnIntegration:
    """Test scikit-learn machine learning integration."""
    
    @pytest.mark.skipif(not SKLEARN_AVAILABLE, reason="scikit-learn not installed")
    def test_sklearn_import(self):
        """Test that scikit-learn can be imported."""
        from sklearn.decomposition import PCA
        assert PCA is not None
    
    @pytest.mark.skipif(not SKLEARN_AVAILABLE, reason="scikit-learn not installed")
    def test_pca_on_zero_features(self):
        """Test PCA on simulated zero features."""
        from sklearn.decomposition import PCA
        
        # Simulate zero features: [height, spacing, density]
        n_zeros = 100
        features = np.random.randn(n_zeros, 3)
        
        pca = PCA(n_components=2)
        features_pca = pca.fit_transform(features)
        
        assert features_pca.shape == (n_zeros, 2)
        assert hasattr(pca, 'explained_variance_ratio_')
        assert len(pca.explained_variance_ratio_) == 2
    
    @pytest.mark.skipif(not SKLEARN_AVAILABLE, reason="scikit-learn not installed")
    def test_clustering(self):
        """Test K-means clustering."""
        from sklearn.cluster import KMeans
        
        # Simple 2D data
        X = np.random.randn(100, 2)
        
        kmeans = KMeans(n_clusters=3, random_state=42, n_init=10)
        labels = kmeans.fit_predict(X)
        
        assert len(labels) == 100
        assert len(set(labels)) <= 3
        assert all(0 <= l < 3 for l in labels)


class TestNumexprIntegration:
    """Test numexpr fast expression evaluation integration."""
    
    @pytest.mark.skipif(not NUMEXPR_AVAILABLE, reason="numexpr not installed")
    def test_numexpr_import(self):
        """Test that numexpr can be imported."""
        import numexpr as ne
        assert ne is not None
    
    @pytest.mark.skipif(not NUMEXPR_AVAILABLE, reason="numexpr not installed")
    def test_simple_expression(self):
        """Test simple expression evaluation."""
        import numexpr as ne
        
        x = np.array([1.0, 2.0, 3.0])
        y = np.array([4.0, 5.0, 6.0])
        
        result_numpy = x**2 + y**2
        result_numexpr = ne.evaluate('x**2 + y**2')
        
        np.testing.assert_array_almost_equal(result_numpy, result_numexpr)
    
    @pytest.mark.skipif(not NUMEXPR_AVAILABLE, reason="numexpr not installed")
    def test_complex_expression(self):
        """Test complex expression with transcendental functions."""
        import numexpr as ne
        
        x = np.random.randn(1000)
        
        result_numpy = np.exp(-x**2 / 2) / np.sqrt(2 * np.pi)
        
        pi = np.pi
        result_numexpr = ne.evaluate('exp(-x**2 / 2) / sqrt(2*pi)',
                                     local_dict={'x': x, 'pi': pi})
        
        np.testing.assert_array_almost_equal(result_numpy, result_numexpr)


class TestAdvancedLibrariesDemo:
    """Test the advanced libraries demo script."""
    
    def test_demo_script_exists(self):
        """Test that demo script exists."""
        demo_path = os.path.join(os.path.dirname(__file__), 
                                '..', 'demo_advanced_math_libraries.py')
        assert os.path.exists(demo_path), "Demo script not found"
    
    def test_demo_script_is_executable(self):
        """Test that demo script can be imported."""
        # Add parent directory to path
        parent_dir = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
        if parent_dir not in sys.path:
            sys.path.insert(0, parent_dir)
        
        # Try to import (this will execute module-level code)
        try:
            import demo_advanced_math_libraries
            # If import succeeds, the script is valid Python
            assert True
        except Exception as e:
            pytest.fail(f"Demo script import failed: {e}")


class TestRealDataUsage:
    """Test that real, verified data is used in demonstrations."""
    
    def test_real_zeros_file_exists(self):
        """Test that real Riemann zeros data file exists."""
        zeros_path = os.path.join(os.path.dirname(__file__), '..', 'zeros', 'zeros_t1e8.txt')
        assert os.path.exists(zeros_path), "Real zeros data file not found"
    
    def test_real_zeros_data_valid(self):
        """Test that zeros data is valid and not empty."""
        zeros_path = os.path.join(os.path.dirname(__file__), '..', 'zeros', 'zeros_t1e8.txt')
        
        with open(zeros_path, 'r') as f:
            zeros = [float(line.strip()) for line in f if line.strip()]
        
        assert len(zeros) > 0, "Zeros data is empty"
        assert len(zeros) >= 100, f"Expected at least 100 zeros, got {len(zeros)}"
        
        # Check that zeros are in reasonable range
        assert all(z > 0 for z in zeros), "All zeros should be positive"
        assert zeros[0] >= 14.0, f"First zero should be >= 14.0, got {zeros[0]}"
    
    def test_demo_loads_real_zeros(self):
        """Test that demo script can load real zeros."""
        import sys
        sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
        
        from demo_advanced_math_libraries import load_real_zeros
        
        zeros = load_real_zeros(max_zeros=100)
        
        assert zeros is not None, "load_real_zeros returned None"
        assert len(zeros) == 100, f"Expected 100 zeros, got {len(zeros)}"
        assert zeros[0] >= 14.0, f"First zero should be >= 14.0, got {zeros[0]}"
    
    def test_no_random_data_in_demo(self):
        """Test that demo doesn't use random data for zeros."""
        demo_path = os.path.join(os.path.dirname(__file__), '..', 'demo_advanced_math_libraries.py')
        
        with open(demo_path, 'r') as f:
            content = f.read()
        
        # Check that demo mentions real data
        assert 'load_real_zeros' in content, "Demo should load real zeros"
        assert 'Odlyzko' in content, "Demo should reference Odlyzko data"
        
        # Check that old random simulation is removed
        assert 't_values = 14.134 + np.cumsum(np.abs(np.random.randn' not in content, \
            "Demo should not simulate zeros with random data"


class TestDocumentation:
    """Test that advanced libraries documentation exists."""
    
    def test_advanced_libraries_readme_exists(self):
        """Test that ADVANCED_LIBRARIES_README.md exists."""
        readme_path = os.path.join(os.path.dirname(__file__),
                                   '..', 'ADVANCED_LIBRARIES_README.md')
        assert os.path.exists(readme_path), "ADVANCED_LIBRARIES_README.md not found"
    
    def test_advanced_libraries_readme_content(self):
        """Test that README contains key sections."""
        readme_path = os.path.join(os.path.dirname(__file__),
                                   '..', 'ADVANCED_LIBRARIES_README.md')
        
        with open(readme_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # Check for key sections
        assert 'Numba' in content
        assert 'JAX' in content
        assert 'NetworkX' in content
        assert 'TensorLy' in content
        assert 'Scikit-learn' in content
        assert 'Performance Benchmarks' in content
        assert 'Installation Guide' in content
    
    def test_readme_mentions_real_data(self):
        """Test that README emphasizes use of real data."""
        readme_path = os.path.join(os.path.dirname(__file__),
                                   '..', 'ADVANCED_LIBRARIES_README.md')
        
        with open(readme_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # Check that README mentions real data
        assert 'REAL' in content or 'real' in content, "README should mention real data"
        assert 'Odlyzko' in content, "README should reference Odlyzko data"
        assert 'verified' in content.lower(), "README should mention verified data"


class TestWorkflows:
    """Test that new GitHub Actions workflows exist."""
    
    def test_performance_benchmark_workflow_exists(self):
        """Test that performance benchmark workflow exists."""
        workflow_path = os.path.join(os.path.dirname(__file__),
                                    '..', '.github', 'workflows',
                                    'performance-benchmark.yml')
        assert os.path.exists(workflow_path), "Performance benchmark workflow not found"
    
    def test_advanced_validation_workflow_exists(self):
        """Test that advanced validation workflow exists."""
        workflow_path = os.path.join(os.path.dirname(__file__),
                                    '..', '.github', 'workflows',
                                    'advanced-validation.yml')
        assert os.path.exists(workflow_path), "Advanced validation workflow not found"


def test_library_summary():
    """Print summary of available advanced libraries."""
    print("\n" + "="*70)
    print("ADVANCED MATHEMATICAL LIBRARIES - AVAILABILITY SUMMARY")
    print("="*70)
    
    libraries = [
        ("Numba", NUMBA_AVAILABLE),
        ("NetworkX", NETWORKX_AVAILABLE),
        ("Scikit-learn", SKLEARN_AVAILABLE),
        ("Numexpr", NUMEXPR_AVAILABLE),
    ]
    
    for name, available in libraries:
        status = "✅ Available" if available else "❌ Not installed"
        print(f"{name:20s} : {status}")
    
    available_count = sum(1 for _, avail in libraries if avail)
    total_count = len(libraries)
    
    print(f"\nTotal: {available_count}/{total_count} libraries available")
    print("="*70)
    
    # This test always passes, it just prints info
    assert True


if __name__ == "__main__":
    pytest.main([__file__, "-v", "-s"])
