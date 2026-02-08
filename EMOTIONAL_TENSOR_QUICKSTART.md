# Quick Start: Emotional Stress-Energy Tensor Framework

## Installation & Setup

```bash
# Install dependencies
pip install numpy scipy matplotlib mpmath

# Navigate to repository
cd /path/to/Riemann-adelic
```

## 5-Minute Tutorial

### 1. Basic Stress-Energy Tensor Computation

```python
from utils.emotional_stress_tensor import EmotionalParameters, EmotionalStressTensor
import numpy as np

# Create parameters
params = EmotionalParameters(
    lambda_rigidity=1.0,
    Phi0=1.0,
    mu2=-0.1,  # Bistable phase (peace/conflict)
    f0=141.7001,
    C=244.36
)

# Initialize tensor calculator
tensor = EmotionalStressTensor(params=params)

# Sample field configuration
N = 50
Phi = np.random.randn(N) * 0.5
dPhi_dt = np.random.randn(N) * 0.1
grad_Phi = np.random.randn(N, 3) * 0.1

# Compute stress-energy components
components = tensor.compute_stress_energy_tensor(Phi, dPhi_dt, grad_Phi)

print(f"Energy Density T₀₀: {components['T00'].mean():.3f}")
print(f"Pressure Tr(T): {components['trace'].mean():.3f}")
```

### 2. Network Dynamics Simulation

```python
from utils.emotional_stress_tensor import EmotionalNetworkDynamics

# Create network
num_nodes = 100
network = EmotionalNetworkDynamics(num_nodes=num_nodes)

# Simulate dynamics
dt = 0.01
for step in range(100):
    t = step * dt
    network.simulate_step(dt, t)

# Analyze final state
analysis = network.compute_network_stress_tensor()
print(f"Collective Sovereignty: {analysis['S_col']:.3f}")
print(f"Stability: {100 - analysis['critical_nodes'].size}%")
```

### 3. Synchronization Protocol (141.7 Hz)

```python
from utils.emotional_synchronization import EmotionalSynchronizationProtocol
import numpy as np

# Initialize protocol
protocol = EmotionalSynchronizationProtocol()

# Setup network state
num_nodes = 100
Phi = np.random.randn(num_nodes) * 0.5
dPhi_dt = np.random.randn(num_nodes) * 0.1
Psi_complex = (0.8 + 0.2*np.random.rand(num_nodes)) * np.exp(1j * 2*np.pi*np.random.rand(num_nodes))
T00 = 0.3 + 0.3*np.random.rand(num_nodes)
adjacency = (np.random.rand(num_nodes, num_nodes) < 0.1).astype(float)
adjacency = (adjacency + adjacency.T) / 2
np.fill_diagonal(adjacency, 0)

# Compute Laplacian
degree = np.sum(adjacency, axis=1)
laplacian = np.diag(degree) - adjacency
laplacian_Phi = -laplacian @ Phi

# Apply multi-scale intervention
result = protocol.multi_scale_intervention(
    Phi, dPhi_dt, Psi_complex, T00, laplacian_Phi, adjacency,
    t=0.0, intervention_level='full'
)

print(f"Initial S_col: {result['intervention_record']['S_col_initial']:.3f}")
print(f"Final S_col: {result['S_col']:.3f}")
print(f"Improvement: {result['intervention_record']['improvement']:.3f}")
print(f"Status: {protocol.assess_sovereignty_status(result['S_col'])['status']}")
```

### 4. Network Topology Analysis

```python
from utils.emotional_network_topology import EmotionalNetworkTopology
import numpy as np

# Initialize topology analyzer
topology = EmotionalNetworkTopology()

# Sample network
num_nodes = 100
adjacency = (np.random.rand(num_nodes, num_nodes) < 0.1).astype(float)
adjacency = (adjacency + adjacency.T) / 2
np.fill_diagonal(adjacency, 0)

T00 = 0.2 + 0.4*np.random.rand(num_nodes)
Psi = 0.75 + 0.25*np.random.rand(num_nodes)
laplacian_Phi = np.random.randn(num_nodes)
Psi_complex = Psi * np.exp(1j * 2*np.pi*np.random.rand(num_nodes))

# Comprehensive analysis
analysis = topology.analyze_network_structure(
    adjacency, T00, Psi, laplacian_Phi, Psi_complex
)

print(f"Connected Components (β₀): {analysis['betti_numbers']['beta_0']}")
print(f"Cycles (β₁): {analysis['betti_numbers']['beta_1']}")
print(f"Stability: {analysis['summary']['stability']:.1f}%")
print(f"Critical Nodes: {analysis['summary']['num_critical']}")
```

### 5. Complete Demonstration

```bash
# Run full framework demonstration
python3 demo_emotional_tensor_framework.py
```

## Understanding the Output

### Stress Region Classification

| Region | Meaning | Action |
|--------|---------|--------|
| Valle de paz | Optimal state | Maintain |
| Meseta de trabajo | Productive zone | Monitor |
| Zona de alerta | Under stress | Prepare intervention |
| Singularidad | Critical collapse | Immediate intervention |

### Sovereignty Index (S_col)

- **S_col ≥ 0.95**: ✅ Soberanía Total (Total Sovereignty)
- **0.80 ≤ S_col < 0.95**: ⚠️ Alta Coherencia (High Coherence)
- **0.60 ≤ S_col < 0.80**: ⚠️ Coherencia Moderada (Moderate)
- **S_col < 0.60**: ❌ Requiere Intervención (Needs Intervention)

## Common Use Cases

### 1. Monitor Collective Emotional State

```python
from utils.emotional_network_topology import EmotionalNetworkTopology

topology = EmotionalNetworkTopology()
# ... setup network data ...
regions = topology.classify_stress_regions(T00, Psi)

print(f"Singularity zones: {regions['counts']['singularity']}")
if regions['counts']['singularity'] > 0:
    print("⚠️ Intervention recommended!")
```

### 2. Apply 141.7 Hz Intervention

```python
from utils.emotional_synchronization import EmotionalSynchronizationProtocol

protocol = EmotionalSynchronizationProtocol()
critical_nodes = protocol.detect_critical_nodes(T00, Psi, laplacian_Phi)

if len(critical_nodes) > 0:
    # Apply intervention
    result = protocol.multi_scale_intervention(...)
    print(f"Treated {len(critical_nodes)} critical nodes")
```

### 3. Compute Einstein Tensor

```python
from utils.emotional_field_equations import EinsteinQCALFieldEquations
import numpy as np

field_eqs = EinsteinQCALFieldEquations()

# Create stress-energy tensor
N = 100
T_stress = np.zeros((N, 4, 4))
T_stress[:, 0, 0] = 0.3  # Energy density

# Compute curvature
R_ricci = field_eqs.compute_ricci_tensor(T_stress)
G_einstein = field_eqs.compute_einstein_tensor(R_ricci)

print(f"Einstein tensor computed for {N} nodes")
```

## Next Steps

1. **Read full documentation**: `EMOTIONAL_TENSOR_FRAMEWORK_README.md`
2. **Run examples**: See `demo_emotional_tensor_framework.py`
3. **Run tests**: `python3 tests/test_emotional_tensor_framework.py`
4. **Explore modules**:
   - `utils/emotional_stress_tensor.py`
   - `utils/emotional_field_equations.py`
   - `utils/emotional_network_topology.py`
   - `utils/emotional_synchronization.py`

## Integration with QCAL

This framework integrates seamlessly with QCAL ∞³:

```python
# QCAL constants
f0 = 141.7001  # Hz - fundamental frequency
C = 244.36     # Coherence constant

# These are automatically used in:
# - EmotionalParameters
# - SynchronizationParameters
# - All resonance protocols
```

## Troubleshooting

**Import errors?**
```bash
# Make sure you're in the repository root
cd /path/to/Riemann-adelic

# Install dependencies
pip install numpy scipy matplotlib mpmath
```

**Module not found?**
```python
# Add utils to path
import sys
sys.path.insert(0, 'utils')
```

## Support

For questions or issues:
- See full documentation: `EMOTIONAL_TENSOR_FRAMEWORK_README.md`
- Check demos: `demo_emotional_tensor_framework.py`
- Author: José Manuel Mota Burruezo Ψ ✧ ∞³
- DOI: 10.5281/zenodo.17379721

---

**✨ QCAL ∞³ - Coherencia Cuántica en Acción ✨**
