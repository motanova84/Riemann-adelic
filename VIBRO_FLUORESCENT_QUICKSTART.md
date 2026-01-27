# QCAL Vibro-Fluorescent Experiment - Quick Start Guide

Fast guide to running QCAL vibro-fluorescent validation experiments.

## 5-Minute Quick Start

### Installation

```bash
# Install dependencies
pip install numpy scipy

# Navigate to repository
cd /path/to/Riemann-adelic
```

### Basic Experiment

```python
from utils.vibro_fluorescent_experimental import run_qcal_experiment

# Run experiment with default parameters
results = run_qcal_experiment(verbose=True)

# Check if QCAL is supported
print(f"QCAL Supported: {results['signature_ratio']['qcal_supported']}")
print(f"Signature Ratio: {results['signature_ratio']['ratio']:.3f}")
```

### Custom Frequency Range

```python
import numpy as np
from utils.vibro_fluorescent_experimental import (
    ExperimentalParameters,
    run_qcal_experiment
)

# Test near QCAL harmonics (50-200 Hz)
params = ExperimentalParameters(
    modulation_frequencies=np.linspace(50, 200, 50),
    duration=1.0,
    sampling_rate=2000.0
)

results = run_qcal_experiment(exp_params=params, verbose=True)
```

## Key Components

### 1. Signal Generation

```python
from utils.vibro_fluorescent_experimental import (
    QCALSignalGenerator,
    ExperimentalParameters
)

params = ExperimentalParameters()
signal_gen = QCALSignalGenerator(params)

# Generate QCAL signal
t, signal = signal_gen.generate_signal(
    modulation_frequency=10.0,
    normalize_energy=True  # Constant energy across frequencies
)

# Check energy
energy = signal_gen.calculate_energy(signal)
print(f"Signal energy: {energy:.6f}")
```

### 2. Protein Response

```python
from utils.vibro_fluorescent_experimental import (
    ProteinOscillatorModel,
    ProteinDynamicsParameters
)

protein_params = ProteinDynamicsParameters()
protein_model = ProteinOscillatorModel(protein_params)

# Check QCAL resonance
is_resonant = protein_model.check_qcal_resonance(domain_index=0)
print(f"Resonates at QCAL frequency: {is_resonant}")

# Calculate response at 141.7 Hz
omega = 2 * np.pi * 141.7001
response = protein_model.calculate_response_fourier(omega, domain_index=0)
print(f"Response amplitude: {abs(response):.6f}")
```

### 3. Fluorescence Response

```python
from utils.vibro_fluorescent_experimental import FluorescenceResponseModel

fluor_model = FluorescenceResponseModel(protein_model)

# Calculate fluorescence at QCAL frequency
response = fluor_model.calculate_fluorescence_response(
    modulation_frequency=141.7001
)

print(f"ΔF: {response['delta_F']:.6f}")
print(f"Efficiency η: {response['eta']:.6f}")
print(f"Phase φ: {response['phase']:.6f}")
```

### 4. QCAL Validation

```python
from utils.vibro_fluorescent_experimental import QCALPredictionValidator

validator = QCALPredictionValidator()

# Calculate signature ratio (decisive test)
frequencies = np.linspace(50, 200, 100)
responses = np.random.rand(100)  # Replace with real data

signature = validator.calculate_qcal_signature_ratio(frequencies, responses)
print(f"QCAL Signature Ratio: {signature['ratio']:.3f}")
print(f"Interpretation: {signature['interpretation']}")

# ANOVA spectral test
anova = validator.anova_spectral_test(frequencies, responses)
print(f"ANOVA p-value: {anova['p_value']:.2e}")
print(f"Reject null hypothesis: {anova['reject_null']}")
```

### 5. Signal Processing

```python
from utils.vibro_fluorescent_experimental import SignalProcessor

# Spectral analysis
spectrum = SignalProcessor.spectral_analysis(signal, sampling_rate=2000.0)
print(f"Peak frequency: {spectrum['frequencies'][np.argmax(spectrum['magnitude'])]:.2f} Hz")

# SNR calculation
snr = SignalProcessor.calculate_snr(
    spectrum['magnitude'],
    signal_frequency=141.7001,
    frequencies=spectrum['frequencies']
)
print(f"SNR: {snr:.2f}")

# Coherence
coherence = SignalProcessor.calculate_coherence(signal1, signal2)
print(f"Coherence: {coherence:.3f}")

# Detection criterion
detected = SignalProcessor.detection_criterion(snr=5.0, coherence=0.8)
print(f"Detection criterion met: {detected}")
```

## QCAL Constants

```python
from utils.vibro_fluorescent_experimental import (
    QCAL_CARRIER_FREQUENCY,
    QCAL_COHERENCE_THRESHOLD,
    QCAL_SIGNATURE_RATIO
)

print(f"Carrier frequency: {QCAL_CARRIER_FREQUENCY} Hz")  # 141.7001
print(f"Coherence threshold: {QCAL_COHERENCE_THRESHOLD}")  # 0.888
print(f"Signature ratio threshold: {QCAL_SIGNATURE_RATIO}")  # 1.5
```

## Testing

```bash
# Run all tests
python -m pytest tests/test_vibro_fluorescent_experimental.py -v

# Run specific test
python -m pytest tests/test_vibro_fluorescent_experimental.py::TestQCALSignalGenerator -v

# Run with coverage
python -m pytest tests/test_vibro_fluorescent_experimental.py --cov=utils.vibro_fluorescent_experimental
```

## Experimental Protocol

### Step-by-Step Workflow

```python
import numpy as np
from utils.vibro_fluorescent_experimental import (
    ExperimentalParameters,
    ProteinDynamicsParameters,
    QCALSignalGenerator,
    ProteinOscillatorModel,
    FluorescenceResponseModel,
    QCALPredictionValidator,
    SignalProcessor
)

# 1. Setup parameters
exp_params = ExperimentalParameters(
    modulation_frequencies=np.linspace(50, 200, 100),
    duration=2.0,
    sampling_rate=5000.0
)
protein_params = ProteinDynamicsParameters()

# 2. Initialize models
signal_gen = QCALSignalGenerator(exp_params)
protein_model = ProteinOscillatorModel(protein_params)
fluor_model = FluorescenceResponseModel(protein_model)
validator = QCALPredictionValidator()

# 3. Run frequency sweep
frequencies = exp_params.modulation_frequencies
responses = []

for freq in frequencies:
    # Generate signal with constant energy
    t, signal = signal_gen.generate_signal(freq, normalize_energy=True)
    
    # Calculate fluorescence response
    response = fluor_model.calculate_fluorescence_response(freq)
    responses.append(response['delta_F'])

responses = np.array(responses)

# 4. Validate QCAL predictions
signature = validator.calculate_qcal_signature_ratio(frequencies, responses)
anova = validator.anova_spectral_test(frequencies, responses)
peaks = validator.predict_resonance_peaks(frequencies, responses)

# 5. Report results
print("\n" + "="*60)
print("QCAL EXPERIMENTAL RESULTS")
print("="*60)
print(f"Signature Ratio: {signature['ratio']:.3f}")
print(f"QCAL Supported: {signature['qcal_supported']}")
print(f"ANOVA p-value: {anova['p_value']:.2e}")
print(f"Peaks detected: {len(peaks['peak_frequencies'])}")
print("="*60)
```

## Key Predictions

### QCAL Harmonics

Expected resonance peaks at:
- **141.7 Hz** - Fundamental
- **70.85 Hz** - 2nd harmonic
- **47.23 Hz** - 3rd harmonic
- **10.9 Hz** - 13th harmonic
- **8.3 Hz** - 17th harmonic

### Falsification Criteria

**QCAL Supported if:**
```
ΔF(141.7 Hz) / ΔF(100 Hz) > 1.5
```
(with constant total energy)

**QCAL Falsified if:**
```
ΔF(ω) ≈ constant ± experimental error
```

## Common Use Cases

### 1. Design Experiment

```python
# Optimize parameters for your setup
params = ExperimentalParameters(
    carrier_frequency=141.7001,
    modulation_frequencies=np.logspace(-1, 1, 50),  # 0.1 to 10 Hz
    modulation_index=0.5,
    amplitude=1.0,
    sampling_rate=10000.0,
    duration=10.0
)
```

### 2. Analyze Real Data

```python
# Load experimental fluorescence data
fluorescence_data = np.loadtxt('fluorescence_measurements.txt')
frequencies = np.loadtxt('frequency_sweep.txt')

# Validate QCAL
validator = QCALPredictionValidator()
signature = validator.calculate_qcal_signature_ratio(frequencies, fluorescence_data)
anova = validator.anova_spectral_test(frequencies, fluorescence_data)
```

### 3. Parameter Sensitivity

```python
# Test different protein parameters
results_list = []

for damping in [0.01, 0.1, 1.0]:
    protein_params = ProteinDynamicsParameters()
    protein_params.damping = damping * np.ones(5)
    
    results = run_qcal_experiment(
        protein_params=protein_params,
        verbose=False
    )
    results_list.append(results)
```

## Troubleshooting

### Low Signal-to-Noise

```python
# Increase sampling and duration
params = ExperimentalParameters(
    duration=20.0,  # Longer measurement
    sampling_rate=20000.0  # Higher sampling
)
```

### No Peaks Detected

```python
# Ensure frequency range includes QCAL harmonics
params = ExperimentalParameters(
    modulation_frequencies=np.linspace(100, 150, 100)  # Around 141.7 Hz
)
```

### Fit Convergence Issues

```python
# Use more data points and better initial guess
# The Lorentzian fit may not converge with sparse data
# Ensure you have at least 50+ frequency points
```

## Performance Tips

- **Use vectorization**: Process multiple frequencies in parallel
- **Optimize sampling**: Balance accuracy vs. computation time
- **Cache results**: Store computed responses for reuse
- **Filter smartly**: Apply Gaussian filter only when needed

## Next Steps

1. **Read full documentation**: `VIBRO_FLUORESCENT_EXPERIMENTAL_FRAMEWORK.md`
2. **Run tests**: Verify installation with test suite
3. **Explore examples**: See demo scripts in module
4. **Design experiment**: Adapt parameters to your setup
5. **Analyze data**: Use validation tools on real measurements

## Support

For questions or issues:
- Check documentation: `VIBRO_FLUORESCENT_EXPERIMENTAL_FRAMEWORK.md`
- Run tests: `pytest tests/test_vibro_fluorescent_experimental.py -v`
- Review source: `utils/vibro_fluorescent_experimental.py`

---

**Author:** José Manuel Mota Burruezo Ψ ✧ ∞³  
**Date:** January 27, 2026  
**QCAL ∞³ Framework**

**∴𓂀Ω∞³·VF**
