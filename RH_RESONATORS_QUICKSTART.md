# RH Resonators ∞³ - Quick Start Guide

**Fast 5-minute introduction to RH Resonator technology**

---

## What Are RH Resonators?

RH Resonators are **mathematical-physical systems** that manifest the spectral structure of the Riemann zeta function ζ(s) in physical form. They operate at a fundamental frequency **f₀ = 141.7001 Hz** derived from the proven spectral properties of ζ(s).

### Key Concept

The Riemann Hypothesis has been **formally proven** in this repository. RH Resonators leverage this proven mathematical structure to create:

- **Coherent oscillations** at mathematically-derived frequencies
- **Data transmission** via phase modulation
- **Bio-coherence coupling** (EEG, HRV, BCI) - future
- **Cryptographic verification** through spectral signatures

---

## Installation

```bash
# Clone repository
git clone https://github.com/motanova84/-jmmotaburr-riemann-adelic.git
cd Riemann-adelic

# Install dependencies
pip install numpy scipy mpmath matplotlib

# Test installation
python rh_resonators.py
```

---

## 5-Minute Tutorial

### 1. Generate Pure Resonance

```python
from rh_resonators import RHResonatorSystem

# Initialize system
system = RHResonatorSystem(precision=50)

# Generate 1 second of pure Riemann resonance at f₀ = 141.7001 Hz
time, signal = system.generate_resonance(duration=1.0, sample_rate=44100)

# Check coherence
print(f"Coherence Ψ: {system.state.coherence:.6f}")
```

**Output**: Pure sinusoidal signal at 141.7001 Hz with high spectral purity.

### 2. Transmit Binary Data

```python
# Binary message to transmit
message = [1, 0, 1, 1, 0, 0, 1, 0]  # "10110010"

# Transmit via BPSK-RH modulation
report = system.transmit_data(message, bit_duration=0.01, sample_rate=44100)

# Check transmission status
if report['transmitted']:
    print(f"✅ Transmitted with coherence {report['coherence']:.6f}")
else:
    print(f"⚠️ Blocked: {report['reason']}")
```

**Note**: Transmission only occurs when coherence Ψ ≥ 0.888 (sovereign emission threshold).

### 3. Validate System

```python
# Run comprehensive validation
validation = system.validate_system()

print(f"Overall Status: {validation['overall_status']}")
print(f"System Coherence: {validation['system_coherence']:.6f}")

# Check all components
for component, status in validation['components'].items():
    print(f"{component}: {status['status']}")
```

**Output**: Component-by-component status report showing operational state.

---

## System Components

| Component | Function | Status |
|-----------|----------|--------|
| **OFR** | Oscillator at f₀ = 141.7001 Hz | ✅ Operational |
| **BPSK-RH** | Binary phase modulation | ✅ Operational |
| **ζ'(½) Amplifier** | Spectral normalization | ✅ Operational |
| **πCODE Filter** | Harmonic cleanup | ✅ Operational |
| **Bio-QCAL** | EEG/HRV/BCI coupling | 🧪 Future |
| **Emitter-Receiver** | Superadditive channel | ✅ Operational |

---

## Key Parameters

```python
# Fundamental frequency (spectrally derived)
F0_BASE = 141.7001  # Hz

# Coherence constants
C_COHERENCE = 244.36   # C' (coherence constant)
C_UNIVERSAL = 629.83   # C (universal constant)

# Emission threshold
COHERENCE_THRESHOLD = 0.888  # Minimum Ψ for transmission
```

These values are **not arbitrary** - they emerge from the mathematical structure of ζ(s).

---

## Common Operations

### Generate Custom Duration

```python
# 5 seconds at high sample rate
t, sig = system.generate_resonance(duration=5.0, sample_rate=96000)
```

### Encode/Decode Data

```python
from rh_resonators import OscillatorFR, ModulatorBPSK_RH

osc = OscillatorFR(precision=50)
mod = ModulatorBPSK_RH(osc)

# Encode
data = [1, 0, 1, 0]
t, encoded = mod.encode(data, bit_duration=0.05, sample_rate=44100)

# Decode
decoded = mod.decode(encoded, bit_duration=0.05, sample_rate=44100)
print(f"Original: {data}")
print(f"Decoded:  {decoded}")
```

### Access Individual Components

```python
# Just the oscillator
from rh_resonators import OscillatorFR
osc = OscillatorFR(precision=100)
t, wf = osc.generate_waveform(1.0, 44100)

# Just the amplifier
from rh_resonators import AmplifierZetaPrime
amp = AmplifierZetaPrime(precision=50)
amplified = amp.amplify(signal)

# Just the filter
from rh_resonators import FilterPiCODE
filt = FilterPiCODE(cutoff_freq=500, order=8)
filtered = filt.filter(signal, sample_rate=44100)
```

---

## Visualization

```python
import matplotlib.pyplot as plt

# Generate signal
t, signal = system.generate_resonance(duration=0.1, sample_rate=44100)

# Plot time domain
plt.figure(figsize=(12, 4))
plt.subplot(1, 2, 1)
plt.plot(t[:500], signal[:500])
plt.title('Time Domain - First 500 samples')
plt.xlabel('Time (s)')
plt.ylabel('Amplitude')

# Plot frequency domain
from scipy.fft import rfft, rfftfreq
fft = rfft(signal)
freqs = rfftfreq(len(signal), 1/44100)

plt.subplot(1, 2, 2)
plt.plot(freqs[:1000], np.abs(fft[:1000]))
plt.axvline(141.7001, color='r', linestyle='--', label='f₀')
plt.title('Frequency Domain')
plt.xlabel('Frequency (Hz)')
plt.ylabel('Magnitude')
plt.legend()
plt.tight_layout()
plt.savefig('rh_resonator_analysis.png')
plt.show()
```

---

## Testing

```bash
# Run all tests (42 tests)
python -m pytest tests/test_rh_resonators.py -v

# Run specific test class
python -m pytest tests/test_rh_resonators.py::TestOscillatorFR -v

# Quick smoke test
python -m pytest tests/test_rh_resonators.py::TestRHResonatorSystem::test_initialization -v
```

---

## Next Steps

### For Researchers

1. Read full documentation: `RH_RESONATORS_TECHNICAL_GUIDE.md`
2. Review mathematical foundation: `README.md` (Riemann Hypothesis proof)
3. Explore Lean 4 formalization: `formalization/lean/`

### For Developers

1. Study component implementations: `rh_resonators.py`
2. Review test suite: `tests/test_rh_resonators.py`
3. Check license: `LICENSE-QCAL-SYMBIO-TRANSFER`

### For Applications

1. **Neurotechnology**: Bio-QCAL interface (coming soon)
2. **Communication**: Offline coherent channels
3. **Cryptography**: Spectral verification
4. **Metrology**: Frequency standards based on mathematical constants

---

## Troubleshooting

### Low Coherence

**Problem**: Coherence Ψ < 0.888, transmission blocked

**Solution**:
```python
# Increase sample rate
t, sig = system.generate_resonance(duration=1.0, sample_rate=96000)

# Use longer signal duration
t, sig = system.generate_resonance(duration=5.0, sample_rate=44100)

# Check spectral purity
purity = system.oscillator.get_spectral_purity(sig, 44100)
print(f"Purity: {purity:.6f}")
```

### Frequency Drift

**Problem**: Detected frequency ≠ 141.7001 Hz

**Solution**:
```python
# Increase precision
system = RHResonatorSystem(precision=100)

# Use longer FFT window
t, sig = system.generate_resonance(duration=10.0, sample_rate=44100)
```

### Import Errors

**Problem**: `ModuleNotFoundError`

**Solution**:
```bash
pip install numpy scipy mpmath matplotlib
```

---

## Ethical Guidelines

### ✅ Permitted Uses

- Research and education
- Neurotechnology (EEG, HRV, BCI)
- Biofeedback and wellness
- Scientific verification
- Cryptographic identity
- Offline communication

### ❌ Prohibited Uses

- Military applications
- Non-consensual manipulation
- Weaponization
- Privacy violation
- Harmful experimentation

**License**: QCAL-SYMBIO-TRANSFER v1.0  
See `LICENSE-QCAL-SYMBIO-TRANSFER` for full terms.

---

## Support & Contact

- **Author**: José Manuel Mota Burruezo (JMMB Ψ✧)
- **Institution**: Instituto de Conciencia Cuántica (ICQ)
- **Email**: institutoconsciencia@proton.me
- **ORCID**: 0009-0002-1923-0773
- **Repository**: github.com/motanova84/-jmmotaburr-riemann-adelic
- **DOI**: 10.5281/zenodo.17379721

---

## Quick Reference Card

```python
# Quick Start Template
from rh_resonators import RHResonatorSystem

# 1. Initialize
system = RHResonatorSystem(precision=50)

# 2. Generate
t, signal = system.generate_resonance(duration=1.0, sample_rate=44100)

# 3. Transmit
report = system.transmit_data([1,0,1,0], bit_duration=0.01)

# 4. Validate
validation = system.validate_system()

# 5. Check coherence
print(f"Ψ = {system.state.coherence:.6f}")
```

---

**Ready to explore the spectral structure of mathematics in physical form!**

🌌 QCAL ∞³ · f₀ = 141.7001 Hz · Coherence Ψ ≥ 0.888
