# Unified Hierarchy Quick Reference

## 🌌 Quick Start

### Installation & Dependencies

```bash
pip install mpmath numpy scipy matplotlib
```

### Basic Usage

```python
from unified_hierarchy import UnifiedHierarchy, demonstrate_unified_hierarchy

# Quick demonstration
results = demonstrate_unified_hierarchy(n_zeros=50, verbose=True)

# Access results
convergence = results['convergence']
consciousness = results['consciousness']

print(f"All systems converge: {convergence['systems_converge_to_zeta']}")
print(f"Consciousness possible: {consciousness['consciousness_possible']}")
```

## 📊 The Five Systems

### System 5: ζ(s) - Fundamental Base

```python
from unified_hierarchy import ZetaBaseSystem

# Create system
zeta = ZetaBaseSystem(precision=50)

# Compute zeros
zeros = zeta.compute_zeros(n_zeros=100)

# Verify Riemann Hypothesis
verification = zeta.verify_critical_line(zeros)
print(f"All on Re(s) = 1/2: {verification['all_on_critical_line']}")
```

**Key Properties**:
- Computes non-trivial zeros: ρ_n = 1/2 + iγ_n
- Spectral frequencies: f_n = (γ_n/γ₁) × f₀
- Verifies critical line hypothesis

### System 1: φ Powers - Fractal Modulation

```python
from unified_hierarchy import PhiFractalSystem

# Create system
phi_system = PhiFractalSystem()

# Analyze golden structure
analysis = phi_system.analyze_golden_structure(zeros)

print(f"φ = {analysis['phi']}")
print(f"Mean modulation: {analysis['mean_modulation']}")
```

**Key Properties**:
- Spacing modulation: Δγ_n ∼ (2π/log n) × (1 + ε_n·φ^(-n))
- Frequency self-similarity: f_{n+k}/f_n ≈ φ^(α·k)
- Governs fine fluctuations in zero distribution

### System 2: ζ(n) Values - Analytic Structure

```python
from unified_hierarchy import ZetaValuesSystem

# Create system
zeta_vals = ZetaValuesSystem()

# Compute special values
values = zeta_vals.compute_special_values(max_n=10)

print(f"ζ(2) = π²/6 = {values[2]}")
print(f"ζ(4) = π⁴/90 = {values[4]}")

# Spectral moments
moments = zeta_vals.spectral_moments(zeros, order=4)
```

**Key Properties**:
- ζ(2) = π²/6, ζ(4) = π⁴/90, ...
- Moments encode zero distribution
- Trace formula coefficients

### System 3: QCAL Codons - Symbiotic Resonance

```python
from unified_hierarchy import QCALCodonSystem

# Create system
codons = QCALCodonSystem()

# Find resonant codons
resonant = codons.find_resonant_codons(zeros, tolerance=0.01)

for codon_info in resonant[:5]:
    print(f"Codon {codon_info['codon']}: "
          f"f = {codon_info['frequency']:.4f} Hz")
```

**Key Properties**:
- Codon frequency: f_codon = Σ f_{dᵢ}
- Resonance criterion: |f_codon - f_n| < ε
- Spectral chords in frequency space

### System 4: Harmonics - Vibrational Consequence

```python
from unified_hierarchy import HarmonicSystem

# Create system
harmonics = HarmonicSystem()

# Compute harmonics
f0_harmonics = harmonics.compute_harmonics(141.7001, max_harmonic=10)

print("f₀ harmonics:")
for k, harm in enumerate(f0_harmonics, 1):
    print(f"  {k}·f₀ = {harm:.4f} Hz")
```

**Key Properties**:
- Harmonics: f_n^(k) = k·f_n
- Euler product structure: log ζ(s) = Σ_p Σ_k p^(-ks)/k
- Natural overtones of fundamental frequencies

## 🎯 Complete Hierarchy Analysis

```python
from unified_hierarchy import UnifiedHierarchy

# Create complete hierarchy
hierarchy = UnifiedHierarchy(precision=50, n_zeros=100)

# Access all systems
zeta_base = hierarchy.zeta_base
phi_system = hierarchy.phi_system
zeta_values = hierarchy.zeta_values
codon_system = hierarchy.codon_system
harmonic_system = hierarchy.harmonic_system

# Verify convergence
results = hierarchy.verify_convergence()

# Check consciousness criterion
consciousness = hierarchy.consciousness_criterion()
```

## 📈 Visualization

```python
from demo_unified_hierarchy import visualize_hierarchy

# Create comprehensive visualization
fig = visualize_hierarchy(n_zeros=50)

# Shows:
# - Zero distribution on critical line
# - Spectral frequencies
# - φ modulation
# - Zero spacing histogram
# - ζ(n) special values
# - Spectral moments
# - f₀ harmonics
# - Frequency self-similarity
# - Convergence summary
```

## 🔬 Testing

```bash
# Run all tests
pytest tests/test_unified_hierarchy.py -v

# Run specific test class
pytest tests/test_unified_hierarchy.py::TestZetaBaseSystem -v

# Run with coverage
pytest tests/test_unified_hierarchy.py --cov=unified_hierarchy
```

## 📊 Key Constants

```python
from unified_hierarchy import F0, GAMMA_1, DELTA_ZETA, PHI, C_COHERENCE

print(f"f₀ = {F0} Hz")              # 141.7001 Hz
print(f"γ₁ = {GAMMA_1}")            # 14.134725142
print(f"δζ = {DELTA_ZETA} Hz")      # 0.2787 Hz
print(f"φ = {PHI}")                 # 1.618033988749895
print(f"C = {C_COHERENCE}")         # 244.36
```

## 🎓 Advanced Examples

### Custom Zero Analysis

```python
hierarchy = UnifiedHierarchy(precision=100, n_zeros=200)
zeros = hierarchy.zeros

# Analyze specific zero
z10 = zeros[9]
print(f"ρ₁₀ = {z10.rho}")
print(f"γ₁₀ = {z10.gamma}")
print(f"f₁₀ = {z10.frequency} Hz")

# Compute spectral density at γ₁₀
rho = hierarchy.zeta_base.spectral_density(z10.gamma)
print(f"ρ(γ₁₀) = {rho}")
```

### Codon Resonance Search

```python
# Search for highly resonant codons
resonant = hierarchy.codon_system.find_resonant_codons(
    zeros=hierarchy.zeros,
    codon_length=4,
    max_codons=10000,
    tolerance=0.005  # 0.5% tolerance
)

# Filter by resonance quality
high_quality = [c for c in resonant if c['relative_deviation'] < 0.001]
print(f"Found {len(high_quality)} high-quality resonances")
```

### Harmonic Spectrum Analysis

```python
# Generate full harmonic spectrum
spectrum = hierarchy.harmonic_system.harmonic_spectrum(
    zeros=hierarchy.zeros[:20],
    max_harmonic=10
)

# Analyze harmonic content
for zero_idx, harmonics in spectrum.items():
    print(f"Zero {zero_idx}: {len(harmonics)} harmonics")
```

## 🧪 Validation Workflow

```python
# Complete validation workflow
def validate_hierarchy():
    # 1. Create hierarchy
    h = UnifiedHierarchy(precision=50, n_zeros=50)
    
    # 2. Verify convergence
    conv = h.verify_convergence()
    assert conv['systems_converge_to_zeta'], "Convergence failed"
    
    # 3. Check critical line
    crit = conv['system_5_zeta_base']
    assert crit['all_on_critical_line'], "Zeros not on critical line"
    
    # 4. Verify consciousness
    consc = h.consciousness_criterion()
    assert consc['consciousness_possible'], "Consciousness criterion failed"
    
    print("✅ All validations passed")
    return True

validate_hierarchy()
```

## 💡 Tips & Best Practices

### Performance

- Start with `n_zeros=50` for quick tests
- Use `n_zeros=100-200` for detailed analysis
- Increase `precision` for higher accuracy (default: 50 dps)

### Accuracy

- Default precision (50 decimal places) is sufficient for most analyses
- Critical line verification uses tolerance of 1e-10
- Codon resonance uses 1% tolerance by default

### Visualization

- Save plots before showing: `plt.savefig()` then `plt.show()`
- Use `verbose=False` for batch processing
- Generate multiple plots for different zero ranges

## 🔗 Integration Points

### With V5 Coronación

```python
from validate_v5_coronacion import validate_v5_coronacion
from unified_hierarchy import UnifiedHierarchy

# Run both validations
v5_results = validate_v5_coronacion()
hierarchy = UnifiedHierarchy(precision=50, n_zeros=50)
unif_results = hierarchy.verify_convergence()

# Cross-validate
assert unif_results['systems_converge_to_zeta']
assert unif_results['system_5_zeta_base']['all_on_critical_line']
```

### With Spectral Constants

```python
from operators.spectral_constants import validate_dual_constants
from unified_hierarchy import UnifiedHierarchy

# Validate consistency
dual_const = validate_dual_constants(verbose=True)
hierarchy = UnifiedHierarchy(precision=50, n_zeros=30)

# Both should use same f₀
assert hierarchy.zeta_base.f0 == dual_const['constants']['f0']
```

## 📚 Further Reading

- **Main Documentation**: `UNIFIED_HIERARCHY_IMPLEMENTATION.md`
- **Mathematical Framework**: Problem statement in PR description
- **QCAL Beacon**: `.qcal_beacon`
- **Spectral Constants**: `operators/spectral_constants.py`
- **V5 Coronación**: `validate_v5_coronacion.py`

## 🌟 Key Insights

1. **All systems converge to ζ(s)**: Not independent systems, but projections
2. **φ governs fine structure**: Golden ratio appears in spacing fluctuations
3. **ζ(n) are moments**: Complete spectral information encoded
4. **Codons are chords**: Resonant combinations in frequency space
5. **Harmonics emerge naturally**: From Euler product structure

## 🎯 Quick Checks

```python
# Verify installation
python -c "from unified_hierarchy import UnifiedHierarchy; print('✓ Installed')"

# Run quick test
python -c "from unified_hierarchy import demonstrate_unified_hierarchy; demonstrate_unified_hierarchy(n_zeros=10, verbose=False)"

# Generate visualization
python demo_unified_hierarchy.py

# Run tests
pytest tests/test_unified_hierarchy.py -q
```

---

**QCAL ∞³ Active** · 141.7001 Hz · Ψ = I × A_eff² × C^∞

🕳️ → ☀️
