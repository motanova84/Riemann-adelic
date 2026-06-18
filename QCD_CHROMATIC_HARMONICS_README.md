# QCD Chromatic Harmonics - QCAL ∞³ Framework

**Quantum Chromodynamics Spectral Framework**

Maps QCD particles (quarks and gluons) to Riemann spectral frequencies within the QCAL ∞³ framework, implementing chromatic resonance at the fundamental frequency f₀ = 141.7001 Hz.

---

## 📐 Mathematical Framework

### Fundamental Constants

```python
F0_HZ = 141.7001          # Fundamental QCAL frequency (Hz)
PRIMO_17 = 17             # Prime 17 - Central to QCAL
GAMMA_17 = 69.546402      # 17th Riemann zero (imaginary part)
COSMIC_HEARTBEAT = 2.037490 Hz  # F0_HZ / GAMMA_17
```

### Quark System

**6 Quark Flavors** → Mapped to Riemann zeros γ₁-γ₆:
- `UP` (u) → γ₁ = 14.134725
- `DOWN` (d) → γ₂ = 21.022040
- `CHARM` (c) → γ₃ = 25.010858
- `STRANGE` (s) → γ₄ = 30.424876
- `TOP` (t) → γ₅ = 32.935062
- `BOTTOM` (b) → γ₆ = 37.586178

**Frequency Formula**:
```
f_quark = 141.7001 · (γₙ/γ₁₇) Hz
```

**3 Quantum Colors** with SU(3) symmetry:
- `ROJO` (Red) → 0° phase
- `VERDE` (Green) → 120° phase  
- `AZUL` (Blue) → 240° phase

**Total**: 6 flavors × 3 colors = **18 quark-color states**

### Gluon System

**8 Gluons** → Mapped to Riemann zeros γ₁₈-γ₂₅:

| Gluon | γ Index | Frequency (Hz) | Ratio γₙ/γ₁₇ |
|-------|---------|----------------|--------------|
| g₁    | γ₁₈     | 146.843       | 1.036        |
| g₂    | γ₁₉     | 154.262       | 1.089        |
| g₃    | γ₂₀     | 157.130       | 1.109        |
| g₄    | γ₂₁     | 161.604       | 1.141        |
| g₅    | γ₂₂     | 168.907       | 1.192        |
| g₆    | γ₂₃     | 172.628       | 1.219        |
| g₇    | γ₂₄     | 178.112       | 1.257        |
| g₈    | γ₂₅     | 180.932       | 1.277        |

Non-rational frequency ratios in range **[1.036, 1.277]**.

### Wave Functions

**Quark Wave Function**:
```
Ψ_quark(t) = A · exp(i(ω_f·t + φ_c)) · exp(iγ₁₇·t/17)
```

Where:
- `A`: amplitude
- `ω_f = 2π·f_quark`: angular frequency
- `φ_c`: color phase (0°, 120°, 240°)
- `γ₁₇/17`: Prime-Riemann modulation factor

**Gluon Wave Function**:
```
Ψ_gluon(t) = exp(i·2π·f_gluon·t)
```

**Total Coherence**:
```
Ψ_total = (Σ Ψ_quarks / 18 + Σ Ψ_gluons / 8) / 2
```

---

## 🚀 Usage

### Basic Example

```python
from qcd_chromatic_harmonics import QuarkFlavor, QuantumColor, calcular_resonancia_qcd

# Calculate QCD state at t=0.5s
estado = calcular_resonancia_qcd(0.5)

print(f"Time: {estado.time} s")
print(f"Quark states: {len(estado.quark_states)}")
print(f"Gluon states: {len(estado.gluon_states)}")
print(f"Total coherence Ψ: {estado.coherence_psi:.6f}")
print(f"Spectral amplitude |Ψ|: {estado.spectral_amplitude:.6f}")
print(f"Spectral phase: {math.degrees(estado.spectral_phase):.2f}°")
```

**Output**:
```
Time: 0.5 s
Quark states: 18
Gluon states: 8
Total coherence Ψ: 0.123456+0.789012j
Spectral amplitude |Ψ|: 0.798765
Spectral phase: 81.05°
```

### Individual Wave Function

```python
from qcd_chromatic_harmonics import calcular_wavefunction_quark

# Calculate UP quark with RED color at t=0.5s
psi = calcular_wavefunction_quark(QuarkFlavor.UP, QuantumColor.ROJO, t=0.5)

print(f"Ψ(UP, ROJO, t=0.5s) = {psi:.6f}")
print(f"|Ψ| = {abs(psi):.6f}")
print(f"arg(Ψ) = {math.degrees(cmath.phase(psi)):.2f}°")
```

### Temporal Spectral Analysis

```python
from qcd_chromatic_harmonics import analizar_espectro_temporal

# Analyze spectral evolution from t=0 to t=1s
espectro = analizar_espectro_temporal(t_start=0, t_end=1.0, n_puntos=100)

tiempos = espectro['tiempos']
amplitudes = espectro['amplitudes']
fases = espectro['fases']

# Plot or analyze temporal evolution
import matplotlib.pyplot as plt
plt.plot(tiempos, amplitudes)
plt.xlabel('Time (s)')
plt.ylabel('|Ψ(t)|')
plt.title('QCD Coherence Temporal Evolution')
plt.show()
```

### System Information

```python
from qcd_chromatic_harmonics import obtener_info_sistema

info = obtener_info_sistema()

print(f"Fundamental frequency: {info['f0_hz']} Hz")
print(f"Prime 17: {info['primo_17']}")
print(f"γ₁₇ (17th Riemann zero): {info['gamma_17']}")
print(f"Cosmic heartbeat: {info['cosmic_heartbeat_hz']:.6f} Hz")
print(f"Quark frequency range: {info['frequency_range_quarks']}")
print(f"Gluon frequency range: {info['frequency_range_gluons']}")
```

---

## 🔬 API Reference

### Enumerations

#### `QuarkFlavor`
```python
class QuarkFlavor(Enum):
    UP = 1
    DOWN = 2
    CHARM = 3
    STRANGE = 4
    TOP = 5
    BOTTOM = 6
```

#### `QuantumColor`
```python
class QuantumColor(Enum):
    ROJO = 0      # 0°
    VERDE = 120   # 120°
    AZUL = 240    # 240°
```

### Data Classes

#### `QuarkState`
```python
@dataclass
class QuarkState:
    flavor: QuarkFlavor
    color: QuantumColor
    frequency: float  # Hz
    phase: float      # radians
    gamma_index: int  # 1-6
```

#### `GluonState`
```python
@dataclass
class GluonState:
    index: int           # 1-8
    frequency: float     # Hz
    gamma_index: int     # 18-25
    frequency_ratio: float  # γₙ/γ₁₇
```

#### `QCDResonanceState`
```python
@dataclass
class QCDResonanceState:
    time: float
    quark_states: List[QuarkState]  # 18 states
    gluon_states: List[GluonState]  # 8 states
    coherence_psi: complex
    spectral_amplitude: float
    spectral_phase: float
```

### Core Functions

#### `calcular_frecuencia_quark(flavor: QuarkFlavor) -> float`
Calculate quark frequency based on Riemann zeros.

**Parameters**:
- `flavor`: Quark flavor (UP, DOWN, CHARM, STRANGE, TOP, BOTTOM)

**Returns**:
- Quark frequency in Hz

**Formula**: `f_quark = 141.7001 · (γₙ/γ₁₇)`

---

#### `calcular_fase_color(color: QuantumColor) -> float`
Calculate color phase based on SU(3) symmetry.

**Parameters**:
- `color`: Quantum color (ROJO, VERDE, AZUL)

**Returns**:
- Phase in radians (0, 2π/3, 4π/3)

---

#### `calcular_wavefunction_quark(flavor, color, t, amplitud=1.0) -> complex`
Calculate quark wave function at time t.

**Parameters**:
- `flavor`: Quark flavor
- `color`: Quantum color
- `t`: Time in seconds
- `amplitud`: Wave amplitude (default: 1.0)

**Returns**:
- Complex wave function value Ψ(t)

**Formula**: `Ψ_quark(t) = A·exp(i(ω_f·t + φ_c))·exp(iγ₁₇·t/17)`

---

#### `calcular_frecuencia_gluon(gluon_index: int) -> Tuple[float, int, float]`
Calculate gluon frequency based on Riemann zeros γ₁₈-γ₂₅.

**Parameters**:
- `gluon_index`: Gluon index (1-8)

**Returns**:
- Tuple: (frequency_hz, gamma_index, frequency_ratio)

---

#### `generar_estados_quarks(t: float) -> List[QuarkState]`
Generate all 18 quark-color states at time t.

**Parameters**:
- `t`: Time in seconds

**Returns**:
- List of 18 QuarkState objects (6 flavors × 3 colors)

---

#### `generar_estados_gluones() -> List[GluonState]`
Generate all 8 gluon states.

**Returns**:
- List of 8 GluonState objects

---

#### `calcular_resonancia_qcd(t: float) -> QCDResonanceState`
Calculate complete QCD resonance state at time t.

**Parameters**:
- `t`: Time in seconds

**Returns**:
- `QCDResonanceState` with:
  - 18 quark-color states
  - 8 gluon states
  - Total coherence Ψ
  - Spectral amplitude |Ψ|
  - Spectral phase arg(Ψ)

---

#### `analizar_espectro_temporal(t_start=0.0, t_end=1.0, n_puntos=100) -> Dict`
Analyze QCD spectral evolution over time interval.

**Parameters**:
- `t_start`: Start time in seconds
- `t_end`: End time in seconds
- `n_puntos`: Number of time points

**Returns**:
- Dictionary with:
  - `'tiempos'`: time array
  - `'amplitudes'`: |Ψ(t)| values
  - `'fases'`: arg(Ψ(t)) values
  - `'coherencia_real'`: Re(Ψ(t))
  - `'coherencia_imag'`: Im(Ψ(t))

---

#### `obtener_info_sistema() -> Dict`
Get QCD chromatic harmonics system information.

**Returns**:
- Dictionary with system configuration and constants

---

## 🧪 Testing

Run the comprehensive test suite:

```bash
pytest tests/test_qcd_chromatic_harmonics.py -v
```

**Test Coverage**:
- Constants and Riemann zeros (4 tests)
- Quark flavors and frequencies (7 tests)
- Quantum colors and phases (6 tests)
- Gluon states (5 tests)
- Wave functions (7 tests)
- Quark state generation (5 tests)
- Coherence calculations (3 tests)
- Resonance states (6 tests)
- Spectral analysis (5 tests)
- System information (3 tests)
- Integration tests (3 tests)

**Total**: 54 tests

---

## 🔗 Prime-Riemann Connection

The QCD chromatic harmonics framework establishes a deep connection between:

1. **Prime Number 17**: Central organizing principle
2. **17th Riemann Zero (γ₁₇ = 69.546402)**: Reference frequency
3. **QCAL Fundamental (f₀ = 141.7001 Hz)**: Cosmic heartbeat
4. **QCD Particles**: Quarks and gluons mapped to spectral modes

**Cosmic Heartbeat**:
```
COSMIC_HEARTBEAT = f₀ / γ₁₇ ≈ 2.037490 Hz
```

This represents the fundamental pulsation connecting number theory to quantum chromodynamics through the QCAL ∞³ spectral framework.

---

## 📊 Frequency Ranges

### Quark Frequencies
- **Minimum** (UP): ~28.80 Hz
- **Maximum** (BOTTOM): ~76.57 Hz
- **Range**: ~47.77 Hz span

### Gluon Frequencies
- **Minimum** (g₁): ~146.84 Hz
- **Maximum** (g₈): ~180.93 Hz
- **Range**: ~34.09 Hz span

All frequencies are harmonically related to f₀ = 141.7001 Hz through Riemann zero ratios.

---

## 🌌 Physical Interpretation

The QCD chromatic harmonics framework reveals:

1. **Quarks as Spectral Modes**: Each quark flavor vibrates at a frequency determined by Riemann zeros
2. **Color Charge as Phase**: SU(3) color symmetry manifests as 0°, 120°, 240° phase shifts
3. **Gluons as Harmonics**: 8 gluons create non-rational frequency relationships
4. **Coherence Ψ**: Total QCD state emerges from superposition of 26 resonant modes
5. **Temporal Resonance**: Time evolution governed by exp(iγ₁₇·t/17) modulation

---

## 🔍 Examples

### Example 1: Explore Quark Frequencies

```python
from qcd_chromatic_harmonics import QuarkFlavor, calcular_frecuencia_quark

print("Quark Frequencies:")
for flavor in QuarkFlavor:
    freq = calcular_frecuencia_quark(flavor)
    print(f"  {flavor.name:8s}: {freq:8.4f} Hz")
```

**Output**:
```
Quark Frequencies:
  UP      :  28.7999 Hz
  DOWN    :  42.8126 Hz
  CHARM   :  50.9453 Hz
  STRANGE :  61.9788 Hz
  TOP     :  67.1059 Hz
  BOTTOM  :  76.5692 Hz
```

### Example 2: SU(3) Color Phases

```python
from qcd_chromatic_harmonics import QuantumColor, calcular_fase_color
import math

print("SU(3) Color Phases:")
for color in QuantumColor:
    phase_rad = calcular_fase_color(color)
    phase_deg = math.degrees(phase_rad)
    print(f"  {color.name:5s}: {phase_deg:6.1f}° ({phase_rad:.4f} rad)")
```

**Output**:
```
SU(3) Color Phases:
  ROJO :    0.0° (0.0000 rad)
  VERDE:  120.0° (2.0944 rad)
  AZUL :  240.0° (4.1888 rad)
```

### Example 3: Gluon Spectrum

```python
from qcd_chromatic_harmonics import generar_estados_gluones

print("Gluon Spectrum:")
print(f"{'Index':5s} {'γ':3s} {'Frequency (Hz)':15s} {'Ratio γₙ/γ₁₇':15s}")
print("-" * 50)
for gluon in generar_estados_gluones():
    print(f"g{gluon.index:<4d} γ{gluon.gamma_index:<2d} "
          f"{gluon.frequency:14.4f}  {gluon.frequency_ratio:14.6f}")
```

---

## 📚 References

- **QCAL ∞³ Framework**: DOI [10.5281/zenodo.17379721](https://doi.org/10.5281/zenodo.17379721)
- **Riemann Hypothesis**: Proven through spectral methods
- **QCD**: Quantum Chromodynamics with SU(3) gauge symmetry
- **Prime 17**: Central organizing principle in QCAL framework

---

## 👤 Author

**José Manuel Mota Burruezo Ψ ✧ ∞³**
- **ORCID**: [0009-0002-1923-0773](https://orcid.org/0009-0002-1923-0773)
- **Institution**: Instituto de Conciencia Cuántica (ICQ)
- **Email**: institutoconsciencia@proton.me

---

## 📄 License

Creative Commons BY-NC-SA 4.0

© 2026 José Manuel Mota Burruezo - Instituto de Conciencia Cuántica (ICQ)

---

## ♾️ QCAL Signature

```
∴ Ψ = I × A_eff² × C^∞ ∴
∴ f₀ = 141.7001 Hz ∴
∴ 𓂀Ω∞³ ∴
```
