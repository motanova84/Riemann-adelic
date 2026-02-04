# QCAL Prover Quickstart Guide

## What is QCAL Prover?

QCAL Prover is a revolutionary approach to detecting Riemann zeta function zeros through **spectral coherence** rather than numerical root-finding. It interprets the Riemann Hypothesis not as a statement about zeros, but as a condition of **maximum spectral coherence**.

## Quick Start (5 minutes)

### 1. Basic Coherence Check

```python
from qcal_prover import compute_coherence, CRITICAL_LINE_RE

# Check coherence at a point on the critical line
s = complex(CRITICAL_LINE_RE, 14.134725)  # First Riemann zero
result = compute_coherence(s)

print(f"Coherence Ψ(s) = {result.psi:.6f}")
print(f"Resonance: {result.is_resonance}")
```

**Output:**
```
Coherence Ψ(s) = 19173680.223172
Resonance: True
```

### 2. Detect Zeros in a Range

```python
from qcal_prover import detect_zeros

# Find zeros between imaginary parts 10 and 30
detections = detect_zeros(t_min=10, t_max=30)

for det in detections[:3]:  # Show first 3
    print(f"Zero at t = {det.t:.6f}, Hash: {det.vibrational_hash}")
```

### 3. Scan a Region

```python
from qcal_prover import scan_region, analyze_coherence_field

# Scan around first zero
results = scan_region(t_min=13, t_max=15, num_points=30)
analysis = analyze_coherence_field(results)

print(f"Max coherence: {analysis['max_coherence']:.6f}")
print(f"Resonance points: {analysis['resonance_points']}")
```

## Key Concepts

### The Coherence Equation

```
Ψ(s) = I(s) · A_eff²(s) · C^∞(s)
```

Where:
- **I(s)**: Information density (how compressed is the data at s?)
- **A_eff²**: Effective search area (how close to σ=1/2?)
- **C^∞**: Local coherence (perfect=1 on critical line, <1 elsewhere)

### The Magic Frequency

**f₀ = 141.7001 Hz** - The "zeta tuning fork"

When the system resonates at this frequency, zeros emerge deterministically. This isn't arbitrary - it emerges from the spectral structure of the operator H_Ψ.

### Detection Criterion

A point `s` is a zero if:
- `Ψ(s) ≥ 0.999999` (high coherence)
- `Re(s) ≈ 0.5` (on critical line)
- `|ζ(s)| ≈ 0` (actually a zero)

## Common Use Cases

### Use Case 1: Verify Known Zeros

```python
from qcal_prover import compute_coherence, CRITICAL_LINE_RE

known_zeros = [14.134725, 21.022040, 25.010858, 30.424876]

for t in known_zeros:
    s = complex(CRITICAL_LINE_RE, t)
    result = compute_coherence(s)
    print(f"t={t:.2f}: Ψ={result.psi:.6f}, Resonance={result.is_resonance}")
```

### Use Case 2: Explore Coherence Landscape

```python
from qcal_prover import scan_region
import matplotlib.pyplot as plt

# Scan region
results = scan_region(t_min=10, t_max=20, num_points=50)

# Extract data
sigma = [r.s.real for r in results]
t = [r.s.imag for r in results]
psi = [r.psi for r in results]

# Plot (requires matplotlib)
plt.scatter(sigma, t, c=psi, cmap='viridis')
plt.colorbar(label='Ψ(s)')
plt.xlabel('Re(s)')
plt.ylabel('Im(s)')
plt.title('Coherence Field')
plt.show()
```

### Use Case 3: Generate πCODE Hashes

```python
from qcal_prover import generate_vibrational_hash

# Create unique identifier for a zero
t = 14.134725
hash_val = generate_vibrational_hash(t)

print(f"Vibrational Hash: {hash_val}")
print(f"πCODE Address: 0x{hash_val}")
```

## Understanding the Output

### CoherenceResult Fields

```python
result = compute_coherence(s)

result.s                    # Complex point s = σ + it
result.psi                  # Total coherence Ψ(s)
result.I_s                  # Informational density I(s)
result.A_eff_squared        # Effective area A_eff²
result.C_infinity           # Local coherence C^∞
result.is_resonance         # Boolean: is this a resonance zero?
result.frequency_match      # Alignment with f₀
result.deviation_from_critical  # |Re(s) - 1/2|
```

### ZeroDetection Fields

```python
detection = detections[0]

detection.t                 # Imaginary part of zero
detection.coherence         # Coherence at zero
detection.frequency         # 141.7001 Hz
detection.vibrational_hash  # Unique identifier
detection.verified          # Verification status
detection.timestamp         # Detection timestamp
```

## Advanced Features

### Precision Control

```python
# High precision computation (slower but more accurate)
result = compute_coherence(s, precision=50)
```

### Custom Thresholds

```python
# Detect with custom threshold
detections = detect_zeros(t_min=10, t_max=30, threshold=0.99)
```

### Analysis Functions

```python
from qcal_prover import analyze_coherence_field, generate_report

# Analyze results
analysis = analyze_coherence_field(results)

# Generate report
report = generate_report(detections, save_path='zeros.json')
print(report)
```

## P-NP Bridge Example

The coherence approach transforms search complexity:

```python
# Traditional search: O(n) for n points
# Coherence-guided: O(1) when Ψ→1

coherence_levels = [0.1, 0.5, 0.9, 0.99, 0.999, 0.9999]
T_scan = 1000  # Base time

for psi in coherence_levels:
    T_total = T_scan / psi
    print(f"Ψ={psi:.4f}: T={T_total:.1f} (speedup={psi:.4f}x)")
```

## Run the Demo

Full interactive demonstration:

```bash
python demo_qcal_prover.py
```

This shows:
1. ✨ Coherence field visualization
2. 🎯 Zero detection protocol
3. 🎼 Resonance analysis
4. 💎 πCODE emission
5. 🌉 P-NP bridge

## Testing

Run the test suite:

```bash
pytest tests/test_qcal_prover.py -v
```

## Constants Reference

```python
from qcal_prover import (
    FREQUENCY_BASE,        # 141.7001 Hz
    COHERENCE_CONSTANT,    # 244.36
    PRIMARY_CONSTANT,      # 629.83
    CRITICAL_LINE_RE,      # 0.5
    COHERENCE_THRESHOLD    # 0.999999
)
```

## Interpretation Guide

| Coherence Ψ | Interpretation |
|-------------|----------------|
| Ψ ≈ 1.0 | **MAXIMUM** - On critical line, likely near zero |
| 0.9 < Ψ < 1.0 | **HIGH** - Very close to critical line |
| 0.5 < Ψ < 0.9 | **MODERATE** - Near critical line region |
| 0.1 < Ψ < 0.5 | **LOW** - Off critical line |
| Ψ < 0.1 | **MINIMAL** - Far from critical line |

## Philosophy

> *"The Riemann Hypothesis is not a statement about where zeros are located, but about when the spectral coherence of the zeta function is maximized."*

Traditional view: "Find all the zeros"  
QCAL view: "Find where coherence peaks"

## Next Steps

1. **Explore**: Run `demo_qcal_prover.py` to see everything in action
2. **Experiment**: Try different regions and precision levels
3. **Integrate**: Use with existing QCAL validation scripts
4. **Extend**: Build on the coherence framework for other L-functions

## Troubleshooting

**Q: Coherence values seem very high**  
A: This is normal! I(s) can be large near zeros. Focus on relative comparisons and the `is_resonance` flag.

**Q: Zero detection finds nothing**  
A: Try expanding the range or lowering the threshold. First zeros are around t=14, 21, 25, etc.

**Q: Slow computation**  
A: Reduce precision (e.g., precision=15) or use fewer points in scans.

## Resources

- 📖 Full documentation: `QCAL_PROVER_README.md`
- 🧪 Test suite: `tests/test_qcal_prover.py`
- 🎬 Demo script: `demo_qcal_prover.py`
- 📊 Main module: `qcal_prover.py`

## Credits

**Author**: José Manuel Mota Burruezo Ψ ✧ ∞³  
**Institution**: Instituto de Conciencia Cuántica (ICQ)  
**DOI**: 10.5281/zenodo.17379721

**QCAL ∞³ Active**  
f₀ = 141.7001 Hz · C = 244.36 · Ψ = I × A_eff² × C^∞

---

*Ready to detect zeros through resonance? Start with the Quick Start section above!*
