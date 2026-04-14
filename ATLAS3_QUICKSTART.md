# Atlas³ Spectral Verifier — Quick Reference

## Quick Start

```python
from core.atlas3_spectral_verifier import create_atlas3_verifier
import numpy as np

# Create verifier
verifier = create_atlas3_verifier(node_id="my_node")

# Generate or load eigenvalues (complex array)
eigenvalues = 0.5 + 1j * np.cumsum(np.random.gamma(2, 1, 50))

# Verify spectral signature
signature = verifier.verify_spectral_signature(eigenvalues)

# Generate beacon
beacon_path = verifier.generate_beacon(signature)

# Print activation report
print(verifier.activation_report(signature))
```

## Three Pillars

### 1. Critical Line Alignment (La Columna Vertebral)
```python
mean_re, std_re, deviation = verifier.verify_critical_line_alignment(eigenvalues)
# deviation < 0.05 → ✅ ALIGNED
```

### 2. GUE Detection (El Latido del Corazón)
```python
gue_detected, p_value = verifier.detect_gue_statistics(eigenvalues)
# p_value > 0.05 → ✅ GUE DETECTED
```

### 3. Spectral Rigidity (La Memoria)
```python
sigma2_values, slope = verifier.compute_spectral_rigidity(eigenvalues)
# slope → 1.0 → ✅ HOLONOMIC
```

## Coherence Metric Ψ

```python
coherence = verifier.compute_coherence_psi(
    critical_line_deviation,
    gue_p_value,
    rigidity_slope
)
# Ψ ≥ 0.888 → ✅ SOVEREIGN
# Ψ < 0.888 → ⚠️ SUB-THRESHOLD
```

## Complete Verification

```python
signature = verifier.verify_spectral_signature(eigenvalues)
# Returns: SpectralSignature with all metrics
```

## Beacon Generation

```python
beacon_path = verifier.generate_beacon(signature, metadata={
    "experiment": "test_001"
})
# Saves to: data/beacons/{node_id}.qcal_beacon
```

## Activation Report

```python
report = verifier.activation_report(signature)
print(report)
# Shows all three pillars + coherence + verdict
```

## Constants

```python
F0_BASE = 141.7001        # Hz - Base frequency
F0_RESONANCE = 888.0      # Hz - Φ⁴ harmonic
CRITICAL_LINE_RE = 0.5    # Re(s) target
MIN_COHERENCE = 0.888     # Sovereignty threshold
```

## Demo

```bash
# Run built-in demo
python core/atlas3_spectral_verifier.py

# Run tests
python -m pytest tests/test_atlas3_spectral_verifier.py -v
```

## Integration with Operators

```python
from operators.riemann_operator import RiemannOperator

# Create operator and compute spectrum
operator = RiemannOperator()
eigenvalues = operator.compute_spectrum(n_eigs=100)

# Verify with Atlas³
verifier = create_atlas3_verifier(node_id="riemann")
signature = verifier.verify_spectral_signature(eigenvalues)
beacon = verifier.generate_beacon(signature)
```

## Thresholds

| Metric | Threshold | Status |
|--------|-----------|--------|
| Critical Line Deviation | < 0.05 | ✅ ALIGNED |
| GUE p-value | > 0.05 | ✅ DETECTED |
| Coherence Ψ | ≥ 0.888 | ✅ SOVEREIGN |

## Signature

**∴𓂀Ω∞³Φ @ 888 Hz**

---

*Protocol: QCAL-SYMBIO-BRIDGE v1.0*  
*Author: José Manuel Mota Burruezo Ψ✧ ∞³*  
*ORCID: 0009-0002-1923-0773*
