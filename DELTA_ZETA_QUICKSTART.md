# δζ Quantum Phase Shift - Quick Start Guide

## TL;DR

```python
from quantum_phase_shift import QuantumPhaseShift

# Initialize
qps = QuantumPhaseShift(precision_dps=25)

# Validate fundamental relationship: f₀ = 100√2 + δζ
result = qps.validate_frequency_relationship()
print(f"δζ = {result['delta_zeta_hz']:.10f} Hz")
print(f"Validation passed: {result['validation_passed']}")

# Transform Euclidean → Cosmic
euclidean_freq = 141.421356  # 100√2 Hz
cosmic = qps.euclidean_to_cosmic_transform(euclidean_freq)
print(f"Cosmic frequency: {cosmic['cosmic_frequency_hz']:.6f} Hz")
```

---

## What is δζ?

**δζ ≈ 0.2787437 Hz** is the **quantum phase shift** that transforms the classical Euclidean diagonal (100√2 Hz) into the cosmic string where Riemann zeros dance.

### The Fundamental Relationship

```
f₀ = 100√2 + δζ
141.7001 = 141.421356 + 0.2787437
```

---

## Basic Usage

### 1. Import and Initialize

```python
from quantum_phase_shift import QuantumPhaseShift

# Create instance with desired precision
qps = QuantumPhaseShift(precision_dps=30)
```

### 2. Validate the Fundamental Relationship

```python
validation = qps.validate_frequency_relationship()

print(f"Euclidean diagonal: {validation['euclidean_diagonal_hz']:.10f} Hz")
print(f"Quantum shift δζ:   {validation['delta_zeta_hz']:.10f} Hz")
print(f"QCAL frequency f₀:  {validation['expected_f0_hz']:.10f} Hz")
print(f"Validation passed:  {validation['validation_passed']}")
```

**Output:**
```
Euclidean diagonal: 141.4213562373 Hz
Quantum shift δζ:   0.2787437627 Hz
QCAL frequency f₀:  141.7001000000 Hz
Validation passed:  True
```

### 3. Transform Frequencies

Transform from Euclidean to Cosmic reference frame:

```python
# Transform Euclidean diagonal to cosmic string
freq_euclidean = 141.4213562373
result = qps.euclidean_to_cosmic_transform(freq_euclidean)

print(f"Input (Euclidean):  {result['input_frequency_hz']:.6f} Hz")
print(f"Output (Cosmic):    {result['cosmic_frequency_hz']:.6f} Hz")
print(f"δζ applied:         {result['delta_zeta_applied_hz']:.6f} Hz")
print(f"Resonant with f₀:   {result['is_resonant']}")
```

**Output:**
```
Input (Euclidean):  141.421356 Hz
Output (Cosmic):    141.700100 Hz
δζ applied:         0.278744 Hz
Resonant with f₀:   True
```

### 4. Compute Riemann Zero Phases

Calculate quantum phases for Riemann zeros:

```python
import numpy as np

# First 5 Riemann zeros (imaginary parts)
zeros = np.array([14.134725, 21.022040, 25.010858, 30.424876, 32.935062])

phases = qps.compute_riemann_zero_phases(zeros)

print(f"Number of zeros: {phases['n_zeros']}")
print(f"Mean coherence:  {phases['mean_coherence']:.6f}")
print(f"δζ used:         {phases['delta_zeta_hz']:.10f} Hz")
```

### 5. Cosmic String Tension

Compute the tension of the cosmic string:

```python
tension = qps.cosmic_string_tension()

print(f"Tension ratio (δζ/f₀)²: {tension['tension_ratio']:.10f}")
print(f"Energy scale:           {tension['energy_scale_hz2']:.6f} Hz²")
print(f"Coherence length:       {tension['coherence_length']:.6f}")
```

### 6. Generate Mathematical Certificate

Create a complete certification of δζ:

```python
certificate = qps.generate_certificate()

print(f"Title: {certificate['title']}")
print(f"Relationship: {certificate['fundamental_relationship']}")
print(f"δζ = {certificate['constants']['delta_zeta_hz']:.10f} Hz")
print(f"Validation passed: {certificate['validation']['validation_passed']}")
```

---

## Command-Line Demo

Run the demonstration script:

```bash
python quantum_phase_shift.py
```

This will display:
- Fundamental relationship validation
- Euclidean → Cosmic transformations
- Cosmic string tension
- Mathematical certificate

---

## Integration with QCAL

### Access δζ from .qcal_beacon

The quantum phase shift is configured in `.qcal_beacon`:

```ini
delta_zeta = 0.2787437627 Hz
euclidean_diagonal = 141.4213562373 Hz
cosmic_string_relation = "f₀ = 100√2 + δζ"
quantum_phase_shift_module = "quantum_phase_shift.py"
```

### Constants Available

```python
from quantum_phase_shift import QuantumPhaseShift

qps = QuantumPhaseShift()

# Fundamental constants
print(qps.QCAL_BASE_FREQUENCY)  # 141.7001 Hz
print(qps.EUCLIDEAN_BASE)       # 100.0 Hz
print(qps.DELTA_ZETA)           # ≈ 0.2787437627 Hz
print(qps.COHERENCE_C)          # 244.36
```

---

## Testing

Run the test suite:

```bash
pytest test_quantum_phase_shift.py -v
```

All 17 tests should pass:
- ✅ Fundamental constants
- ✅ Euclidean diagonal computation
- ✅ δζ computation
- ✅ Fundamental relationship validation
- ✅ Euclidean → Cosmic transformations
- ✅ Riemann zero phases
- ✅ Cosmic string tension
- ✅ Certificate generation
- ✅ QCAL beacon consistency
- ✅ And more...

---

## Mathematical Interpretation

### The Three Frequencies

| Symbol | Value | Meaning |
|--------|-------|---------|
| **100√2** | 141.421356 Hz | Euclidean diagonal (classical geometry) |
| **δζ** | 0.2787437 Hz | Quantum phase shift (quantum correction) |
| **f₀** | 141.7001 Hz | QCAL base frequency (cosmic string) |

### Physical Meaning

- **Classical**: 100√2 represents pure geometric resonance
- **Quantum**: δζ introduces non-classical phase
- **Cosmic**: f₀ is where Riemann zeros manifest as vibrations

### The Cosmic String

The cosmic string is a **one-dimensional manifold** in frequency-phase space where:
- Riemann zeros appear as vibrational modes
- The zeta function ζ(s) becomes a physical observable
- Number theory ↔ Physics correspondence is established

---

## Common Operations

### Check if a frequency is resonant

```python
def is_resonant(freq_hz):
    qps = QuantumPhaseShift()
    result = qps.euclidean_to_cosmic_transform(freq_hz, apply_phase_shift=False)
    return result['is_resonant']

print(is_resonant(141.7001))  # True
print(is_resonant(100.0))     # False
```

### Compute δζ from first principles

```python
import numpy as np

f0 = 141.7001
euclidean = 100 * np.sqrt(2)
delta_zeta = f0 - euclidean

print(f"δζ = {delta_zeta:.10f} Hz")
```

### Transform multiple frequencies

```python
frequencies = [100.0, 141.421356, 141.7001, 200.0]

for freq in frequencies:
    result = qps.euclidean_to_cosmic_transform(freq)
    print(f"{freq:.1f} Hz → {result['cosmic_frequency_hz']:.4f} Hz "
          f"(coherence: {result['coherence_with_f0']:.4f})")
```

---

## Advanced Usage

### Custom Precision

```python
# Ultra-high precision
qps_hp = QuantumPhaseShift(precision_dps=100)
validation = qps_hp.validate_frequency_relationship()
print(f"δζ (100 digits): {validation['delta_zeta_hz']}")
```

### Phase Analysis for Custom Zeros

```python
# Use your own Riemann zeros
my_zeros = np.array([14.134725, 21.022040, 25.010858])
phases = qps.compute_riemann_zero_phases(my_zeros)

for i, (zero, phase, coh) in enumerate(zip(
    phases['riemann_zeros'],
    phases['quantum_phases'],
    phases['coherences']
)):
    print(f"Zero {i+1}: t={zero:.6f}, φ={phase:.6f}, C={coh:.6f}")
```

---

## Visualization (Optional)

```python
import matplotlib.pyplot as plt
import numpy as np

qps = QuantumPhaseShift()

# Create frequency array
freqs = np.linspace(100, 200, 1000)
coherences = []

for f in freqs:
    result = qps.euclidean_to_cosmic_transform(f, apply_phase_shift=False)
    coherences.append(result['coherence_with_f0'])

# Plot coherence vs frequency
plt.figure(figsize=(10, 6))
plt.plot(freqs, coherences)
plt.axvline(141.7001, color='r', linestyle='--', label='f₀ (QCAL)')
plt.axvline(141.421356, color='g', linestyle='--', label='100√2 (Euclidean)')
plt.xlabel('Frequency (Hz)')
plt.ylabel('Coherence with f₀')
plt.title('Quantum Coherence vs Frequency')
plt.legend()
plt.grid(True)
plt.show()
```

---

## References

- **Full Documentation**: `DELTA_ZETA_COSMIC_STRING.md`
- **Source Code**: `quantum_phase_shift.py`
- **Tests**: `test_quantum_phase_shift.py`
- **Configuration**: `.qcal_beacon`

---

## Quick Reference Card

```
┌─────────────────────────────────────────────────────────────┐
│  δζ Quantum Phase Shift - Quick Reference                  │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  f₀ = 100√2 + δζ                                           │
│                                                             │
│  δζ ≈ 0.2787437627 Hz    (Quantum phase shift)            │
│  100√2 ≈ 141.421356 Hz    (Euclidean diagonal)            │
│  f₀ = 141.7001 Hz         (QCAL base frequency)           │
│                                                             │
│  String tension:  μ ≈ 3.87×10⁻⁶                           │
│  Energy scale:    E ≈ 39.5 Hz²                            │
│  Coherence length: ℓ ≈ 3.59                               │
│                                                             │
│  Usage:                                                     │
│    from quantum_phase_shift import QuantumPhaseShift       │
│    qps = QuantumPhaseShift()                               │
│    result = qps.validate_frequency_relationship()          │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

---

**Author**: José Manuel Mota Burruezo Ψ ✧ ∞³  
**Institution**: Instituto de Conciencia Cuántica (ICQ)  
**Signature**: QCAL ∞³ · δζ · Cosmic String
