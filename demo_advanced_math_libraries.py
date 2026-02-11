#!/usr/bin/env python3
"""
Demo: Advanced Mathematical Libraries for Riemann-Adelic Framework

This script demonstrates the integration of advanced mathematical libraries
to accelerate and expand the computational capabilities of the Riemann-Adelic
proof framework.

Libraries demonstrated:
- numba: JIT compilation for performance
- networkx: Graph theory for prime number networks
- tensorly: Tensor decompositions for spectral analysis
- scikit-learn: Clustering and dimensionality reduction
- numexpr: Fast numerical expression evaluation

Author: José Manuel Mota Burruezo
Date: October 2025
"""

import time
import warnings
from typing import Dict, List, Tuple

import numpy as np

warnings.filterwarnings("ignore")

# Import advanced libraries conditionally
try:
    from numba import jit, prange

    NUMBA_AVAILABLE = True
except ImportError:
    NUMBA_AVAILABLE = False
    print("⚠️  numba not available - install with: pip install numba")

try:
    import networkx as nx

    NETWORKX_AVAILABLE = True
except ImportError:
    NETWORKX_AVAILABLE = False
    print("⚠️  networkx not available - install with: pip install networkx")

try:
    import tensorly as tl
    from tensorly.decomposition import parafac

    TENSORLY_AVAILABLE = True
except ImportError:
    TENSORLY_AVAILABLE = False
    print("⚠️  tensorly not available - install with: pip install tensorly")

try:
    from sklearn.cluster import KMeans
    from sklearn.decomposition import PCA

    SKLEARN_AVAILABLE = True
except ImportError:
    SKLEARN_AVAILABLE = False
    print("⚠️  scikit-learn not available - install with: pip install scikit-learn")

try:
    import numexpr as ne

    NUMEXPR_AVAILABLE = True
except ImportError:
    NUMEXPR_AVAILABLE = False
    print("⚠️  numexpr not available - install with: pip install numexpr")


# ==============================================================================
# 1. NUMBA: JIT Compilation for Performance
# ==============================================================================

if NUMBA_AVAILABLE:

    @jit(nopython=True, parallel=True)
    def compute_spectral_density_grid(
        zeros_imaginary: np.ndarray, t_grid: np.ndarray, sigma: float = 0.5
    ) -> np.ndarray:
        """
        Fast computation of spectral density on grid using real Riemann zeros.

        Uses Gaussian kernel density estimation with real zeros data.
        """
        n_grid = len(t_grid)
        n_zeros = len(zeros_imaginary)
        densities = np.zeros(n_grid)

        normalization = 1.0 / (sigma * np.sqrt(2 * np.pi))

        for i in prange(n_grid):
            t = t_grid[i]
            density = 0.0
            for j in range(n_zeros):
                diff = zeros_imaginary[j] - t
                density += np.exp(-(diff * diff) / (2 * sigma * sigma))
            densities[i] = density * normalization

        return densities

    @jit(nopython=True)
    def compute_zero_spacings(zeros_imaginary: np.ndarray) -> np.ndarray:
        """
        Fast computation of consecutive zero spacings.

        This is a key quantity in random matrix theory and RH.
        """
        n = len(zeros_imaginary)
        spacings = np.zeros(n - 1)
        for i in range(n - 1):
            spacings[i] = zeros_imaginary[i + 1] - zeros_imaginary[i]
        return spacings


def load_real_zeros(filename: str = "zeros/zeros_t1e8.txt", max_zeros: int = None) -> np.ndarray:
    """
    Load real Riemann zeros from Odlyzko data.

    These are actual, verified non-trivial zeros of the Riemann zeta function.
    """
    try:
        with open(filename, "r") as f:
            zeros = [float(line.strip()) for line in f if line.strip()]

        if max_zeros is not None:
            zeros = zeros[:max_zeros]

        return np.array(sorted(zeros))
    except FileNotFoundError:
        print(f"⚠️  Warning: {filename} not found, using fallback data")
        # Fallback to zeros_t1e3.txt if available
        try:
            with open("zeros/zeros_t1e3.txt", "r") as f:
                zeros = [float(line.strip()) for line in f if line.strip()]
            if max_zeros is not None:
                zeros = zeros[:max_zeros]
            return np.array(sorted(zeros))
        except BaseException:
            return None


def demo_numba_acceleration():
    """Demonstrate numba JIT acceleration using REAL Riemann zeros."""
    if not NUMBA_AVAILABLE:
        print("\n❌ Numba not available - skipping demo")
        return

    print("\n" + "=" * 80)
    print("DEMO 1: NUMBA JIT COMPILATION FOR REAL SPECTRAL COMPUTATIONS")
    print("=" * 80)

    # Load REAL Riemann zeros from Odlyzko data
    zeros_imaginary = load_real_zeros(max_zeros=1000)

    if zeros_imaginary is None:
        print("\n❌ Could not load real zeros data - skipping demo")
        return

    print(f"\n✅ Loaded Real Riemann Zeros:")
    print(f"   • Number of zeros: {len(zeros_imaginary)}")
    print(f"   • Height range: [{zeros_imaginary.min():.3f}, {zeros_imaginary.max():.3f}]")
    print(f"   • First 5 zeros: {zeros_imaginary[:5]}")
    print(f"   • Data source: Odlyzko tables (verified)")

    # Compute spectral density using real zeros
    t_grid = np.linspace(zeros_imaginary.min(), zeros_imaginary.max(), 500)

    print(f"\n✅ Computing Spectral Density (Numba-accelerated):")
    start = time.time()
    densities_numba = compute_spectral_density_grid(zeros_imaginary, t_grid, sigma=1.0)
    time_numba = time.time() - start

    # Compare with pure NumPy (without JIT)
    def spectral_density_numpy(zeros, grid, sigma):
        densities = np.zeros(len(grid))
        norm = 1.0 / (sigma * np.sqrt(2 * np.pi))
        for i, t in enumerate(grid):
            densities[i] = norm * np.sum(np.exp(-((zeros - t) ** 2) / (2 * sigma**2)))
        return densities

    start = time.time()
    densities_numpy = spectral_density_numpy(zeros_imaginary, t_grid, sigma=1.0)
    time_numpy = time.time() - start

    print(f"   • Numba time: {time_numba:.4f}s")
    print(f"   • NumPy time: {time_numpy:.4f}s")
    print(f"   • Speedup: {time_numpy/time_numba:.2f}x")
    print(f"   • Max density: {densities_numba.max():.4f}")
    print(f"   • Mean density: {densities_numba.mean():.4f}")

    # Compute zero spacings (important for RMT analysis)
    print(f"\n✅ Zero Spacings Analysis (Numba-accelerated):")
    spacings = compute_zero_spacings(zeros_imaginary)
    print(f"   • Number of spacings: {len(spacings)}")
    print(f"   • Mean spacing: {spacings.mean():.4f}")
    print(f"   • Std spacing: {spacings.std():.4f}")
    print(f"   • Min spacing: {spacings.min():.4f}")
    print(f"   • Max spacing: {spacings.max():.4f}")
    print(f"   • These statistics are crucial for Random Matrix Theory predictions")


# ==============================================================================
# 2. NETWORKX: Graph Theory for Prime Networks
# ==============================================================================


def demo_prime_network_analysis():
    """Demonstrate graph theory analysis using REAL prime numbers and their relationship to zeros."""
    if not NETWORKX_AVAILABLE:
        print("\n❌ NetworkX not available - skipping demo")
        return

    print("\n" + "=" * 80)
    print("DEMO 2: GRAPH THEORY FOR REAL PRIME-ZERO RELATIONSHIPS")
    print("=" * 80)

    # Generate REAL prime numbers using Sieve of Eratosthenes
    def sieve_of_eratosthenes(limit):
        sieve = [True] * (limit + 1)
        sieve[0] = sieve[1] = False
        for i in range(2, int(limit**0.5) + 1):
            if sieve[i]:
                for j in range(i * i, limit + 1, i):
                    sieve[j] = False
        return [i for i in range(limit + 1) if sieve[i]]

    primes = sieve_of_eratosthenes(1000)

    print(f"\n✅ Real Prime Number Network:")
    print(f"   • Generated primes up to 1000 using Sieve of Eratosthenes")
    print(f"   • Total primes: {len(primes)}")
    print(f"   • First 10: {primes[:10]}")
    print(f"   • Last 10: {primes[-10:]}")

    # Load real zeros for comparison
    zeros_imaginary = load_real_zeros(max_zeros=500)

    # Create graph: connect primes based on their relationship to zero spacings
    # This is a novel analysis connecting the prime side to the zero side of the explicit formula
    G = nx.Graph()
    G.add_nodes_from(primes[:100])  # Use first 100 primes for visualization

    prime_set = set(primes[:100])

    # Edge creation: connect primes if their difference is prime (classical)
    classical_edges = 0
    for i, p1 in enumerate(primes[:100]):
        for p2 in primes[i + 1 : i + 20]:  # Look ahead limited window
            if p2 in prime_set and (p2 - p1) in prime_set:
                G.add_edge(p1, p2, weight=p2 - p1, type="classical")
                classical_edges += 1

    print(f"\n✅ Prime Network Graph Properties:")
    print(f"   • Nodes (primes): {G.number_of_nodes()}")
    print(f"   • Edges (prime-gap connections): {G.number_of_edges()}")
    print(f"   • Average degree: {sum(dict(G.degree()).values()) / G.number_of_nodes():.2f}")

    # Analyze graph properties
    if G.number_of_edges() > 0:
        print(f"   • Density: {nx.density(G):.4f}")
        print(f"   • Is connected: {nx.is_connected(G)}")

        # Find communities
        components = list(nx.connected_components(G))
        print(f"   • Connected components: {len(components)}")

        if len(components) > 0:
            largest_component = max(components, key=len)
            print(f"   • Largest component size: {len(largest_component)}")

    # Centrality measures
    degree_centrality = nx.degree_centrality(G)
    betweenness = nx.betweenness_centrality(G)

    top_central = sorted(degree_centrality.items(), key=lambda x: x[1], reverse=True)[:5]
    print(f"\n✅ Most Central Primes (by degree centrality):")
    for prime, centrality in top_central:
        between = betweenness[prime]
        print(f"   • {prime}: degree={centrality:.4f}, betweenness={between:.4f}")

    # Additional analysis: relate to zeros if available
    if zeros_imaginary is not None and len(zeros_imaginary) > 0:
        mean_zero_spacing = np.mean(np.diff(zeros_imaginary))
        mean_prime_gap = np.mean(np.diff(primes[:100]))
        print(f"\n✅ Prime-Zero Relationship:")
        print(f"   • Mean zero spacing: {mean_zero_spacing:.4f}")
        print(f"   • Mean prime gap (first 100): {mean_prime_gap:.4f}")
        print(f"   • These quantities are related via the explicit formula")


# ==============================================================================
# 3. TENSORLY: Tensor Decompositions for Spectral Analysis
# ==============================================================================


def demo_tensor_decomposition():
    """Demonstrate tensor decomposition on REAL spectral data from Riemann zeros."""
    if not TENSORLY_AVAILABLE:
        print("\n❌ TensorLy not available - skipping demo")
        return

    print("\n" + "=" * 80)
    print("DEMO 3: TENSOR DECOMPOSITION FOR REAL SPECTRAL ANALYSIS")
    print("=" * 80)

    # Load REAL Riemann zeros
    zeros_imaginary = load_real_zeros(max_zeros=1000)

    if zeros_imaginary is None:
        print("\n❌ Could not load real zeros data - skipping demo")
        return

    # Create a 3D tensor from real spectral data
    # Dimensions: (frequency_bins, height_segments, spectral_features)
    # This represents spectral properties across different height ranges

    n_freq = 20  # Frequency bins for spectral density
    n_segments = 30  # Height segments
    n_features = 10  # Different sigma values for kernel

    # Divide zeros into height segments
    segment_size = len(zeros_imaginary) // n_segments

    tensor = np.zeros((n_freq, n_segments, n_features))

    print(f"\n✅ Building Real Spectral Tensor:")
    print(f"   • Using {len(zeros_imaginary)} verified Riemann zeros")
    print(f"   • Data source: Odlyzko tables")

    # Fill tensor with real spectral density data
    for seg_idx in range(n_segments):
        start_idx = seg_idx * segment_size
        end_idx = min((seg_idx + 1) * segment_size, len(zeros_imaginary))
        segment_zeros = zeros_imaginary[start_idx:end_idx]

        if len(segment_zeros) < 2:
            continue

        # Create frequency grid for this segment
        t_min, t_max = segment_zeros.min(), segment_zeros.max()
        t_range = t_max - t_min
        if t_range < 0.1:
            continue

        freq_grid = np.linspace(t_min, t_max, n_freq)

        # Compute spectral density with different kernel widths
        for feat_idx in range(n_features):
            sigma = 0.1 + feat_idx * 0.2  # Varying kernel width

            for freq_idx, t in enumerate(freq_grid):
                # Gaussian kernel density
                density = np.sum(np.exp(-((segment_zeros - t) ** 2) / (2 * sigma**2)))
                tensor[freq_idx, seg_idx, feat_idx] = density / (sigma * np.sqrt(2 * np.pi))

    print(f"   • Tensor shape: {tensor.shape}")
    print(f"   • Total elements: {tensor.size}")
    print(f"   • Memory: {tensor.nbytes / 1024:.2f} KB")
    print(f"   • Data represents: spectral density across height segments")

    # Perform CP (CANDECOMP/PARAFAC) decomposition
    rank = 5
    try:
        print(f"\n✅ CP Decomposition (rank={rank}):")
        factors = parafac(tensor, rank=rank, n_iter_max=100)

        print(f"   • Factor shapes: {[f.shape for f in factors[1]]}")

        # Reconstruct tensor
        reconstructed = tl.cp_to_tensor(factors)
        error = np.linalg.norm(tensor - reconstructed) / np.linalg.norm(tensor)

        print(f"   • Reconstruction error: {error:.6f}")
        print(f"   • Compression ratio: {tensor.size / sum(f.size for f in factors[1]):.2f}x")
        print(f"   • This decomposition reveals latent spectral patterns in real zeros")

    except Exception as e:
        print(f"   ⚠️  Decomposition failed: {str(e)}")


# ==============================================================================
# 4. SCIKIT-LEARN: Machine Learning for Pattern Recognition
# ==============================================================================


def demo_ml_pattern_recognition():
    """Demonstrate ML techniques using REAL Riemann zeros."""
    if not SKLEARN_AVAILABLE:
        print("\n❌ Scikit-learn not available - skipping demo")
        return

    print("\n" + "=" * 80)
    print("DEMO 4: MACHINE LEARNING ON REAL RIEMANN ZERO PATTERNS")
    print("=" * 80)

    # Load REAL Riemann zeros
    zeros_imaginary = load_real_zeros(max_zeros=1000)

    if zeros_imaginary is None:
        print("\n❌ Could not load real zeros data - skipping demo")
        return

    print(f"\n✅ Real Riemann Zeros Dataset:")
    print(f"   • Number of zeros: {len(zeros_imaginary)}")
    print(f"   • Data source: Odlyzko verified tables")
    print(f"   • Height range: [{zeros_imaginary.min():.2f}, {zeros_imaginary.max():.2f}]")

    # Compute real features from actual zeros
    # Feature 1: Zero heights (imaginary parts)
    # Feature 2: Consecutive spacings
    # Feature 3: Local density (zeros in sliding window)
    # Feature 4: Normalized height (for scaling effects)

    spacings = np.diff(zeros_imaginary)
    spacings = np.concatenate([[spacings[0]], spacings])  # Pad to match length

    # Local density: count zeros within window of size 10
    local_density = np.array([np.sum((zeros_imaginary >= t - 5) & (zeros_imaginary <= t + 5)) for t in zeros_imaginary])

    # Normalized spacings (important for GUE comparison)
    mean_spacing = np.mean(np.diff(zeros_imaginary))
    normalized_spacings = spacings / mean_spacing

    # Create feature matrix
    features = np.column_stack([zeros_imaginary, spacings, local_density, normalized_spacings])

    print(f"   • Feature dimensions: {features.shape}")
    print(f"   • Features: [height, spacing, local_density, normalized_spacing]")

    # PCA for dimensionality reduction
    pca = PCA(n_components=3)
    features_pca = pca.fit_transform(features)

    print(f"\n✅ PCA Dimensionality Reduction:")
    print(f"   • Explained variance: {pca.explained_variance_ratio_}")
    print(f"   • Cumulative variance: {pca.explained_variance_ratio_.sum():.4f}")
    print(f"   • First PC captures: {100*pca.explained_variance_ratio_[0]:.1f}% of variance")

    # K-means clustering to identify different spacing regimes
    n_clusters = 3
    kmeans = KMeans(n_clusters=n_clusters, random_state=42, n_init=10)
    labels = kmeans.fit_predict(features)

    print(f"\n✅ K-Means Clustering of Real Zero Patterns:")
    print(f"   • Number of clusters: {n_clusters}")
    for i in range(n_clusters):
        cluster_size = np.sum(labels == i)
        print(f"   • Cluster {i+1}: {cluster_size} zeros ({100*cluster_size/len(zeros_imaginary):.1f}%)")

    # Analyze spacing distribution per cluster
    print(f"\n✅ Spacing Statistics by Cluster:")
    for i in range(n_clusters):
        cluster_mask = labels == i
        cluster_spacings = spacings[cluster_mask]
        print(f"   • Cluster {i+1}: mean={cluster_spacings.mean():.4f}, std={cluster_spacings.std():.4f}")


# ==============================================================================
# 5. NUMEXPR: Fast Numerical Expression Evaluation
# ==============================================================================


def demo_numexpr_performance():
    """Demonstrate fast numerical evaluation using REAL spectral kernel computations."""
    if not NUMEXPR_AVAILABLE:
        print("\n❌ Numexpr not available - skipping demo")
        return

    print("\n" + "=" * 80)
    print("DEMO 5: FAST REAL SPECTRAL KERNEL EVALUATION")
    print("=" * 80)

    # Load REAL Riemann zeros
    zeros_imaginary = load_real_zeros(max_zeros=1000)

    if zeros_imaginary is None:
        print("\n❌ Could not load real zeros data - skipping demo")
        return

    print(f"\n✅ Real Spectral Kernel Computation:")
    print(f"   • Using {len(zeros_imaginary)} verified Riemann zeros")
    print(f"   • Computing heat kernel on dense grid")

    # Create dense grid for evaluation
    t_min, t_max = zeros_imaginary.min(), zeros_imaginary.max()
    n_grid = 500000  # Half million points for dense evaluation
    t_grid = np.linspace(t_min, t_max, n_grid)

    # Broadcast zeros for vectorized computation
    # For each grid point, we'll compute sum over all zeros
    # This simulates the trace formula evaluation
    zeros_broadcast = zeros_imaginary.reshape(1, -1)
    t_broadcast = t_grid.reshape(-1, 1)

    # Parameters for heat kernel
    sigma = 1.0
    pi = np.pi

    print(f"   • Grid points: {n_grid}")
    print(f"   • Expression: sum_ρ exp(-(t - ρ)²/(2σ²)) / (σ√(2π))")

    # NumPy version
    start = time.time()
    diff_numpy = t_broadcast - zeros_broadcast
    kernel_numpy = np.exp(-(diff_numpy**2) / (2 * sigma**2))
    result_numpy = np.sum(kernel_numpy, axis=1) / (sigma * np.sqrt(2 * pi))
    time_numpy = time.time() - start

    # Numexpr version - evaluate in chunks for memory efficiency
    start = time.time()
    chunk_size = 10000
    result_numexpr = np.zeros(n_grid)

    for i in range(0, n_grid, chunk_size):
        end_i = min(i + chunk_size, n_grid)
        t_chunk = t_grid[i:end_i].reshape(-1, 1)
        diff = t_chunk - zeros_broadcast

        # Use numexpr for the computation
        kernel_chunk = ne.evaluate("exp(-(diff**2) / (2 * sigma**2))", local_dict={"diff": diff, "sigma": sigma})
        result_numexpr[i:end_i] = np.sum(kernel_chunk, axis=1) / (sigma * np.sqrt(2 * pi))

    time_numexpr = time.time() - start

    print(f"   • NumPy time: {time_numpy:.4f}s")
    print(f"   • Numexpr time: {time_numexpr:.4f}s")
    print(f"   • Speedup: {time_numpy/time_numexpr:.2f}x")
    print(f"   • Max difference: {np.max(np.abs(result_numpy - result_numexpr)):.2e}")
    print(f"   • Mean kernel value: {result_numpy.mean():.4f}")
    print(f"   • Max kernel value: {result_numpy.max():.4f}")
    print(f"   • This kernel is central to the trace formula in RH proof")


# ==============================================================================
# MAIN EXECUTION
# ==============================================================================


def main():
    """Run all demonstrations."""
    print("\n" + "=" * 80)
    print("ADVANCED MATHEMATICAL LIBRARIES DEMONSTRATION")
    print("Riemann-Adelic Proof Framework Enhancement")
    print("=" * 80)
    print(f"\nAuthor: José Manuel Mota Burruezo")
    print(f"Date: October 2025")
    print(f"Version: V5 — Coronación")

    # Check which libraries are available
    print("\n📦 Library Availability:")
    print(f"   • Numba: {'✅' if NUMBA_AVAILABLE else '❌'}")
    print(f"   • NetworkX: {'✅' if NETWORKX_AVAILABLE else '❌'}")
    print(f"   • TensorLy: {'✅' if TENSORLY_AVAILABLE else '❌'}")
    print(f"   • Scikit-learn: {'✅' if SKLEARN_AVAILABLE else '❌'}")
    print(f"   • Numexpr: {'✅' if NUMEXPR_AVAILABLE else '❌'}")

    # Run demonstrations
    demo_numba_acceleration()
    demo_prime_network_analysis()
    demo_tensor_decomposition()
    demo_ml_pattern_recognition()
    demo_numexpr_performance()

    print("\n" + "=" * 80)
    print("✅ ALL DEMONSTRATIONS COMPLETED")
    print("=" * 80)
    print("\n💡 These advanced libraries can accelerate:")
    print("   • Spectral computations (numba, numexpr)")
    print("   • Prime number analysis (networkx)")
    print("   • Multi-dimensional data (tensorly)")
    print("   • Pattern recognition (scikit-learn)")
    print("\n🚀 For production use, install all libraries:")
    print("   pip install -r requirements.txt")


if __name__ == "__main__":
    main()
