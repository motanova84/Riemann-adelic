# Kappa Experiment: Modal Curvature Analysis ∞³

## Overview

This module implements the complete pipeline for analyzing curvature emergence in modal space through orthonormal Fourier basis decomposition and spectral graph analysis.

## Mathematical Framework

### Orthonormal Fourier Basis

The basis functions are defined as:

```
φ_0(t) = 1/√T                    (DC component)
φ_n(t) = √(2/T) cos(nπt/T)      (n ≥ 1, oscillatory modes)
```

**Orthonormality Property:**
```
⟨φ_n, φ_m⟩ = ∫₀ᵀ φ_n(t) φ_m(t) dt = δ_{nm}
```

### Modal Covariance Operator

Two types of operators are computed:

1. **Pure Covariance**: `O_nm = ⟨φ_n(t)·φ_m(t)⟩`
2. **Forcing-Weighted**: `O_nm = ⟨φ_n(t)·φ_m(t)·F(t)⟩`

where the forcing function is:
```
F(t) = Σ_{k=1}^K α_k φ_k(t)
```

### Adjacency Graph

The modal similarity graph is constructed as:
```
A_nm = 1  if  ⟨φ_n, φ_m⟩/(‖φ_n‖·‖φ_m‖) > θ
A_nm = 0  otherwise
```

### Curvature Analysis

From the graph Laplacian `L = D - A`, we extract spectral curvature:
```
κ(n) ~ C/(n log n)
```

This asymptotic form mirrors the prime number theorem density `ρ(n) ~ 1/(n log n)`.

## Modules

### 1. `build_orthonormal_basis.py`

Constructs orthonormal Fourier basis for L²([0,T]).

**Class: `OrthonormalFourierBasis`**

```python
from build_orthonormal_basis import OrthonormalFourierBasis

# Initialize basis
basis = OrthonormalFourierBasis(T=1.0, n_modes=50, n_points=2000)

# Evaluate basis function
phi_n = basis.phi_n(n=5, t=np.linspace(0, 1, 100))

# Verify orthonormality
verification = basis.verify_orthonormality(n_check=10)
print(f"Is orthonormal: {verification['is_orthonormal']}")

# Decompose function
def my_function(t):
    return np.cos(2*np.pi*t) + 0.5*np.sin(4*np.pi*t)

coeffs = basis.decompose_function(my_function, n_coeffs=20)

# Reconstruct
reconstructed = basis.reconstruct_function(coeffs, t)
```

### 2. `compute_covariance_operator.py`

Computes modal covariance operator and constructs adjacency graph.

**Class: `ModalCovarianceOperator`**

```python
from compute_covariance_operator import ModalCovarianceOperator

# Initialize with basis
cov_op = ModalCovarianceOperator(basis)

# Compute covariance matrix
O_cov = cov_op.compute_covariance_matrix(max_mode=30)

# Compute forcing operator
forcing_coeffs = np.zeros(51)
forcing_coeffs[1] = 1.0  # Mode 1
forcing_coeffs[3] = 0.5  # Mode 3
O_forcing = cov_op.compute_forcing_operator(forcing_coeffs, max_mode=30)

# Construct adjacency graph
A_graph = cov_op.compute_adjacency_graph(theta=0.1, use_forcing=True)

# Analyze graph properties
props = cov_op.analyze_graph_properties()
print(f"Nodes: {props['n_nodes']}, Edges: {props['n_edges']}")
```

### 3. `analyze_kappa_curve.py`

Analyzes curvature κ(n) and fits to asymptotic form.

**Class: `KappaCurveAnalyzer`**

```python
from analyze_kappa_curve import KappaCurveAnalyzer

# Initialize with adjacency graph
analyzer = KappaCurveAnalyzer(A_graph)

# Compute spectral curvature
kappa = analyzer.compute_spectral_curvature(method='laplacian')

# Fit asymptotic form κ(n) ~ C/(n log n)
fit_results = analyzer.fit_asymptotic_form(n_min=5, n_max=40)
print(f"C = {fit_results['C']:.4f}")
print(f"R² = {fit_results['r_squared']:.4f}")

# Analyze convergence
conv_results = analyzer.analyze_convergence(window_size=5)
print(f"Mean relative error: {conv_results['mean_relative_error']:.6f}")
```

### 4. `run_kappa_experiment_2.py`

Complete experiment orchestrator.

**Class: `KappaExperiment`**

```python
from run_kappa_experiment_2 import KappaExperiment

# Create configuration
config = {
    'T': 1.0,
    'n_modes': 60,
    'n_points': 2000,
    'forcing': {
        'type': 'resonant',
        'modes': [1, 2, 3, 5, 8],
        'amplitudes': [1.0, 0.7, 0.5, 0.3, 0.2]
    },
    'graph': {
        'theta': 0.08
    },
    'curvature': {
        'method': 'laplacian',
        'fit_range': (5, 50)
    },
    'qcal': {
        'f0': 141.7001,
        'C': 244.36
    }
}

# Run experiment
experiment = KappaExperiment(config=config, output_dir='./results')
experiment.run_full_experiment()
```

## Running the Experiment

### Quick Start

```bash
# Run with default configuration
python run_kappa_experiment_2.py
```

### Custom Configuration

```python
from run_kappa_experiment_2 import KappaExperiment

config = KappaExperiment.default_config()
config['n_modes'] = 100  # Customize
config['forcing']['modes'] = [1, 3, 5, 7]

experiment = KappaExperiment(config=config)
experiment.run_full_experiment()
```

## Output

The experiment generates:

1. **Visualizations**:
   - `basis_functions.png`: Orthonormal basis modes
   - `covariance_matrix.png`: Covariance operator heatmap
   - `forcing_operator.png`: Forcing-weighted operator
   - `adjacency_graph.png`: Modal similarity graph
   - `kappa_curve.png`: Curvature analysis with fit

2. **JSON Results** (`experiment_results.json`):
   ```json
   {
     "basis": {
       "orthonormality_verified": true,
       "max_diagonal_error": 1e-16,
       "max_offdiag_error": 1e-16
     },
     "operator": {
       "forcing_modes": [1, 2, 3, 5, 8],
       "O_forcing_norm": 10.7441
     },
     "graph": {
       "n_nodes": 61,
       "n_edges": 760,
       "density": 0.4156
     },
     "curvature": {
       "fit": {
         "C": 0.9128,
         "r_squared": 0.9991
       }
     }
   }
   ```

## Testing

Run the comprehensive test suite:

```bash
# Run all tests
pytest tests/test_kappa_experiment.py -v

# Run specific test class
pytest tests/test_kappa_experiment.py::TestOrthonormalFourierBasis -v

# Run with coverage
pytest tests/test_kappa_experiment.py --cov=. --cov-report=html
```

**Test Coverage:**
- ✓ Basis orthonormality (< 1e-10 error)
- ✓ Function decomposition/reconstruction
- ✓ Parseval's identity
- ✓ Covariance operator symmetry
- ✓ Adjacency graph properties
- ✓ Laplacian computation
- ✓ Curvature asymptotic fit (R² > 0.95)
- ✓ QCAL integration

## QCAL Integration

This implementation integrates with the QCAL ∞³ framework:

- **Fundamental Frequency**: f₀ = 141.7001 Hz
- **Coherence Constant**: C = 244.36
- **Spectral Equation**: Ψ = I × A_eff² × C^∞
- **Modal Analysis**: Compatible with existing spectral operators

## Mathematical Validation

### Expected Results

For a well-formed modal graph:

1. **Orthonormality**: `‖⟨φ_n, φ_m⟩ - δ_{nm}‖ < 1e-10`
2. **Covariance Identity**: `O_cov ≈ I` (for orthonormal basis)
3. **Curvature Fit**: `R² > 0.95` for `κ(n) ~ C/(n log n)`
4. **Convergence**: Relative error decreases with `n`

### Physical Interpretation

- **Modal Resonance**: Forcing at specific modes creates graph structure
- **Curvature Emergence**: Spectral geometry emerges without direct interaction
- **Prime-like Distribution**: κ(n) follows same asymptotic law as primes
- **Spectral Correspondence**: Validates QCAL spectral-geometric duality

## Performance

- **Basis Construction**: O(n_modes × n_points)
- **Covariance Operator**: O(n_modes²)
- **Curvature Analysis**: O(n_modes²) for Laplacian eigenvalues
- **Full Experiment**: ~1-2 seconds for n_modes=60

## References

1. de Branges, L. (1968). "Hilbert spaces of entire functions"
2. Conrey, J.B. (2003). "The Riemann Hypothesis"
3. Montgomery, H.L. (1973). "The pair correlation of zeros of the zeta function"
4. QCAL Framework: DOI 10.5281/zenodo.17379721

## Author

José Manuel Mota Burruezo Ψ ∴ ∞³  
ORCID: 0009-0002-1923-0773  
February 2026

## License

This code is part of the QCAL ∞³ framework and follows the repository's licensing structure.
