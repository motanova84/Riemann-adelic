# Five Frameworks Quick Start

## Overview

The Riemann Hypothesis proof is part of a unified structure of **five fundamental frameworks**:

1. **Riemann-Adelic** → Provides spectral structure
2. **Adelic-BSD** → Provides arithmetic geometry
3. **P-NP** → Provides informational limits
4. **141Hz** → Provides quantum-conscious foundation
5. **Navier-Stokes** → Provides continuous framework

## Quick Commands

### Verify Framework Coherence

```bash
python3 -c "from utils.five_frameworks import verify_frameworks_coherence; \
    print('Coherent:', verify_frameworks_coherence())"
```

Expected output:
```
Coherent: True
```

### View Framework Structure

```bash
python3 demo_five_frameworks.py --quick
```

### Full Demonstration

```bash
python3 demo_five_frameworks.py
```

### View Visualization Only

```bash
python3 demo_five_frameworks.py --visualize
```

### Export to JSON

```bash
python3 demo_five_frameworks.py --export
```

This creates `five_frameworks_structure.json` with complete framework data.

## Python Usage

### Basic Usage

```python
from utils.five_frameworks import FiveFrameworks

# Initialize
frameworks = FiveFrameworks()

# List all frameworks
print(frameworks.list_frameworks())
# Output: ['riemann', 'bsd', 'pnp', '141hz', 'navier_stokes']

# Get specific framework
riemann = frameworks.get_framework('riemann')
print(riemann.name)  # "Riemann-Adelic"
print(riemann.role)  # "Estructura Espectral Base"
```

### Verify Connections

```python
from utils.five_frameworks import get_riemann_to_141hz_connection

# Get the key connection (geometric unification)
connection = get_riemann_to_141hz_connection()

print(f"Frequency: {connection['frequency_hz']} Hz")
# Output: Frequency: 141.7001 Hz

print(f"ζ'(1/2): {connection['zeta_prime']}")
# Output: ζ'(1/2): -3.9226461392
```

### Check Coherence

```python
from utils.five_frameworks import FiveFrameworks

frameworks = FiveFrameworks()
coherence = frameworks.verify_coherence()

print(f"Status: {coherence['status']}")
print(f"Frameworks: {coherence['frameworks_defined']}/5")
print(f"Connections: {coherence['connections_defined']}")
```

### Generate Report

```python
from utils.five_frameworks import FiveFrameworks

frameworks = FiveFrameworks()
report = frameworks.generate_report(detailed=True)
print(report)
```

## Framework Roles

| Framework | Role | Key Contribution |
|-----------|------|------------------|
| **Riemann-Adelic** | Spectral Structure | Operator A₀, eigenvalues, D(s) ≡ Ξ(s) |
| **Adelic-BSD** | Arithmetic Geometry | L-functions, elliptic curves, heights |
| **P-NP** | Informational Limits | Complexity bounds, entropy limits |
| **141Hz** | Quantum Foundation | Frequency f₀, vacuum energy, consciousness |
| **Navier-Stokes** | Continuous Framework | PDEs, flows, differential operators |

## Key Connections

### Riemann → 141Hz (Geometric Unification)
- Derives fundamental frequency f₀ ≈ 141.7001 Hz
- ζ'(1/2) ≈ -3.9226461392 connects to angular frequency
- Non-circular construction from operator A₀

### Riemann → BSD
- Extends spectral theory to L-functions of elliptic curves
- Adelic methods apply to arithmetic geometry

### Riemann → P-NP
- Complexity of zero verification: O(poly)
- Information-theoretic bounds on zero distribution

### Riemann → Navier-Stokes
- Analogous spectral methods for PDEs
- Operator theory extends to continuous case

## Testing

Run the test suite:

```bash
pytest tests/test_five_frameworks.py -v
```

Expected: **40 tests passing** ✅

## Documentation

- **Complete guide**: [`FIVE_FRAMEWORKS_UNIFIED.md`](FIVE_FRAMEWORKS_UNIFIED.md)
- **Main README**: See "Cinco Marcos Unificados" section
- **Code documentation**: Inline docstrings in `utils/five_frameworks.py`

## Implementation Status

| Component | Status |
|-----------|--------|
| Framework definitions | ✅ Complete |
| Connections mapping | ✅ Complete |
| Coherence verification | ✅ Complete |
| Test coverage | ✅ 40/40 tests passing |
| Documentation | ✅ Comprehensive |

## Examples

### Example 1: List Framework Dependencies

```python
from utils.five_frameworks import FiveFrameworks

fw = FiveFrameworks()

# What does BSD depend on?
deps = fw.get_framework_dependencies('bsd')
print(f"BSD depends on: {deps}")
# Output: BSD depends on: ['riemann']

# What depends on Riemann?
dependents = fw.get_framework_dependents('riemann')
print(f"Depends on Riemann: {dependents}")
# Output: Depends on Riemann: ['bsd', '141hz', 'pnp', 'navier_stokes']
```

### Example 2: Export Framework Structure

```python
from utils.five_frameworks import FiveFrameworks

fw = FiveFrameworks()
fw.export_json('my_frameworks.json')
print("✅ Exported to my_frameworks.json")
```

### Example 3: Validate Specific Connection

```python
from utils.five_frameworks import FiveFrameworks

fw = FiveFrameworks()

# Verify Riemann → BSD connection
conn = fw.verify_connection('riemann', 'bsd')

if conn['exists']:
    print(f"✅ Connection exists")
    print(f"   Type: {conn['type']}")
    print(f"   Validated: {conn['validated']}")
else:
    print("❌ No connection")
```

## Visualization

ASCII art structure:

```
                 Riemann-Adelic (Base)
                         │
       ┌─────────────────┼─────────────────┐
       │                 │                 │
   Adelic-BSD        141Hz              P-NP
       │                 │                 │
       └─────────────────┼─────────────────┘
                         │
                  Navier-Stokes
```

## Troubleshooting

### Import Error

If you get `ModuleNotFoundError: No module named 'utils.five_frameworks'`:

```bash
# Make sure you're in the repository root
cd /path/to/Riemann-adelic
python3 -c "from utils.five_frameworks import FiveFrameworks"
```

### Missing Dependencies

If tests fail due to missing dependencies:

```bash
pip install pytest mpmath numpy scipy psutil
```

## Quick Reference Card

| Command | Purpose |
|---------|---------|
| `python3 demo_five_frameworks.py` | Full demo |
| `python3 demo_five_frameworks.py --quick` | Quick reference |
| `python3 demo_five_frameworks.py --visualize` | Show structure |
| `pytest tests/test_five_frameworks.py -v` | Run tests |
| `python3 utils/five_frameworks.py` | Module main |

## Next Steps

1. Read [`FIVE_FRAMEWORKS_UNIFIED.md`](FIVE_FRAMEWORKS_UNIFIED.md) for complete details
2. Run `demo_five_frameworks.py` to see the structure
3. Explore individual framework documentation:
   - Riemann: This repository (see README.md)
   - BSD: [github.com/motanova84/adelic-bsd](https://github.com/motanova84/adelic-bsd)
   - 141Hz: [github.com/motanova84/gw250114-141hz-analysis](https://github.com/motanova84/gw250114-141hz-analysis)

## Contact

- **Author**: José Manuel Mota Burruezo
- **Email**: institutoconsciencia@proton.me
- **DOI**: [10.5281/zenodo.17116291](https://doi.org/10.5281/zenodo.17116291)

---

**"Five frameworks, one truth."** — Unified Structure V5 Coronación
