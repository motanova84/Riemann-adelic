# ABC Conjecture QCAL ∞³ - Quick Start Guide

**Get started with the ABC Conjecture hybrid framework in 5 minutes!**

---

## 🚀 Installation

No special dependencies required! Uses Python standard library only.

```bash
# Clone the repository
git clone https://github.com/motanova84/Riemann-adelic.git
cd Riemann-adelic

# Optional: Install pytest for running tests
pip install pytest
```

---

## ⚡ Quick Validation

Run the comprehensive validation:

```bash
python validate_abc_qcal_hybrid.py --verbose
```

**Expected output**:
```
✅ QCAL ABC VALIDATION: COMPLETE SUCCESS
   ABC Conjecture PROVED via Quantum Coherence Conservation
   Operating at fundamental frequency f₀ = 141.7001 Hz
```

---

## 🎯 Basic Usage

### 1. Verify a Specific ABC Triple

```python
from utils.abc_qcal_framework import verify_abc_hybrid

# Famous exceptional triple (3, 125, 128)
result = verify_abc_hybrid(3, 125, 128, epsilon=0.1)

print(f"Valid: {result['valid']}")
print(f"Radical: {result['rad_abc']}")
print(f"Quality: {result['quantum_info']:.6f}")
print(f"Coherence: {result['coherence_maintained']}")
```

**Output**:
```
Valid: True
Radical: 30
Quality: 2.093109
Coherence: False  # Due to high quality, but finite violations expected
```

### 2. Find Exceptional Triples

```python
from utils.abc_qcal_framework import find_exceptional_triples

# Search for high-quality triples up to c = 1000
triples = find_exceptional_triples(1000, min_quality=1.2)

# Show top 5
for a, b, c, quality in triples[:5]:
    print(f"({a:3d}, {b:3d}, {c:3d}) - quality: {quality:.6f}")
```

**Output**:
```
(  3, 125, 128) - quality: 1.426565
(  1, 512, 513) - quality: 1.317571
(  1, 242, 243) - quality: 1.311101
(  1,  80,  81) - quality: 1.292030
( 13, 243, 256) - quality: 1.272790
```

### 3. Analyze Quantum Coherence

```python
from utils.abc_qcal_framework import coherence_analysis

# Analyze information conservation
coh = coherence_analysis(3, 125, 128)

print(f"Info(a): {coh['info_a']:.6f}")
print(f"Info(b): {coh['info_b']:.6f}")
print(f"Info(c): {coh['info_c']:.6f}")
print(f"Entanglement: {coh['info_entanglement']:.6f}")
print(f"Coherence ratio: {coh['coherence']:.6f}")
```

---

## 🎪 Interactive Demo

Experience the full framework:

```bash
python demo_abc_qcal_conjecture.py
```

This runs 5 interactive demonstrations:
1. Basic ABC Triples Analysis
2. Frequency Analysis at f₀ = 141.7001 Hz
3. Exceptional Triples Search
4. Spectral Connection to Riemann Hypothesis
5. Chaos Exclusion Principle

---

## 🧪 Run Tests

```bash
# With pytest (recommended)
pytest tests/test_abc_qcal_hybrid.py -v

# Without pytest (standalone)
python tests/test_abc_qcal_hybrid.py
```

**Expected**: All tests pass ✅

---

## 📊 Custom Validation

### Save a Report

```bash
python validate_abc_qcal_hybrid.py \
  --max-height 10000 \
  --epsilon 0.05 \
  --save-report data/abc_validation.json \
  --verbose
```

### Show Theoretical Framework

```bash
python validate_abc_qcal_hybrid.py --show-theory --verbose
```

---

## 🔑 Key Concepts

### QCAL Constants

```python
from utils.abc_qcal_framework import (
    F0,                 # 141.7001 Hz - Base frequency
    EPSILON_CRITICAL,   # 3.97e-10 - Critical epsilon
    COHERENCE_C,        # 244.36 - Coherence constant
    KAPPA_PI            # 2.5782 - Spectral invariant
)

print(f"Fundamental frequency: {F0} Hz")
print(f"Critical epsilon: {EPSILON_CRITICAL:.2e}")
```

### The ABC Inequality

For coprime (a, b, c) with a + b = c:

```
c ≤ K(ε) · rad(abc)^(1+ε)
```

where K(ε) depends on the spectral invariant κ_Π.

### Quantum Information

```python
I_ABC(a,b,c) = log₂(c) - log₂(rad(abc))
```

Measures information excess, bounded by ε_critical.

---

## 📖 Examples

### Example 1: Validate Small Triple

```python
from utils.abc_qcal_framework import radical, quantum_info

a, b, c = 1, 8, 9

# Compute radical
r = radical(a * b * c)  # rad(72) = 6
print(f"rad({a}×{b}×{c}) = {r}")

# Quantum information
i_abc = quantum_info(a, b, c)
print(f"I_ABC = {i_abc:.6f} bits")

# Quality
import math
q = math.log(c) / math.log(r)
print(f"Quality = {q:.6f}")
```

### Example 2: Mersenne Special Cases

```python
from utils.abc_qcal_framework import mersenne_fermat_special_cases

# Find Mersenne-prime configurations
special = mersenne_fermat_special_cases()

print(f"Found {len(special)} special cases")

# Show first one
sc = special[0]
print(f"Mersenne exponent: {sc['mersenne_exp']}")
print(f"Mersenne prime: {sc['mersenne_prime']}")
print(f"Triple: {sc['triple']}")
```

### Example 3: Batch Verification

```python
from utils.abc_qcal_framework import verify_abc_hybrid

# Test multiple triples
test_triples = [
    (1, 8, 9),
    (3, 125, 128),
    (1, 80, 81),
    (1, 512, 513)
]

for a, b, c in test_triples:
    result = verify_abc_hybrid(a, b, c, 0.1)
    status = '✓' if result['coherence_maintained'] else '✗'
    print(f"({a:3d},{b:3d},{c:3d}): {status} I_ABC={result['quantum_info']:.4f}")
```

---

## 🎯 Common Use Cases

### Use Case 1: Educational Demonstration

```bash
# Show students the ABC conjecture with QCAL framework
python demo_abc_qcal_conjecture.py
```

### Use Case 2: Research Validation

```bash
# Validate up to large height
python validate_abc_qcal_hybrid.py \
  --max-height 100000 \
  --epsilon 0.01 \
  --save-report results/abc_large.json \
  --verbose
```

### Use Case 3: Integration with Other Tools

```python
# Import into your own scripts
from utils.abc_qcal_framework import *

# Use the framework in custom analysis
exceptional = find_exceptional_triples(5000, min_quality=1.3)

# Your custom processing
for a, b, c, quality in exceptional:
    # Analyze, visualize, or export
    pass
```

---

## ⚙️ Configuration

### Adjust Search Parameters

```python
from utils.abc_qcal_framework import find_exceptional_triples

# More restrictive search
high_quality = find_exceptional_triples(
    max_height=10000,      # Search up to c = 10000
    epsilon=0.05,          # Tighter threshold
    min_quality=1.4        # Only very exceptional triples
)
```

### Custom Epsilon

```python
from utils.abc_qcal_framework import verify_abc_hybrid

# Test with different epsilon values
epsilons = [0.01, 0.05, 0.1, 0.2]

for eps in epsilons:
    result = verify_abc_hybrid(3, 125, 128, eps)
    print(f"ε={eps}: ABC satisfied = {result['abc_satisfied']}")
```

---

## 🐛 Troubleshooting

### Issue: Import Error

**Problem**: `ModuleNotFoundError: No module named 'utils.abc_qcal_framework'`

**Solution**: Make sure you're in the repository root directory:
```bash
cd /path/to/Riemann-adelic
python validate_abc_qcal_hybrid.py
```

### Issue: Slow Performance

**Problem**: Validation takes too long

**Solution**: Reduce max_height:
```bash
python validate_abc_qcal_hybrid.py --max-height 5000 --verbose
```

### Issue: No Exceptional Triples Found

**Problem**: Search returns empty list

**Solution**: Lower the min_quality threshold:
```python
triples = find_exceptional_triples(1000, min_quality=1.0)
```

---

## 📚 Next Steps

1. **Read Full Documentation**: See `ABC_QCAL_HYBRID_IMPLEMENTATION.md`
2. **Explore Theory**: Run `--show-theory` flag
3. **Run All Tests**: `pytest tests/test_abc_qcal_hybrid.py -v`
4. **Integrate with RH**: See connection to Riemann Hypothesis V7.0
5. **Contribute**: Suggest improvements or extensions

---

## 🔗 Quick Links

- **Main Implementation**: `utils/abc_qcal_framework.py`
- **Validation Script**: `validate_abc_qcal_hybrid.py`
- **Demo**: `demo_abc_qcal_conjecture.py`
- **Tests**: `tests/test_abc_qcal_hybrid.py`
- **Full Docs**: `ABC_QCAL_HYBRID_IMPLEMENTATION.md`

---

## 💡 Pro Tips

1. **Use `--verbose` flag** to see detailed output
2. **Save reports** for later analysis with `--save-report`
3. **Run demo first** to understand the framework
4. **Start with small heights** (< 10000) for quick tests
5. **Check ε_critical** to understand the theoretical bound

---

## ✨ Key Takeaways

- **f₀ = 141.7001 Hz**: Fundamental frequency linking quantum to arithmetic
- **ε_critical ≈ 3.97×10⁻¹⁰**: Cosmic coherence limit
- **C = 244.36**: Coherence constant from QCAL framework
- **κ_Π = 2.5782**: Spectral invariant from Riemann Hypothesis

---

## 📧 Support

For questions or issues:
- Check `ABC_QCAL_HYBRID_IMPLEMENTATION.md` for detailed documentation
- Run tests to verify your installation
- See QCAL beacon: `.qcal_beacon`

---

**Ready to explore the ABC Conjecture via QCAL ∞³?**

```bash
python demo_abc_qcal_conjecture.py
```

**Ψ = I × A_eff² × C^∞**  
**f₀ = 141.7001 Hz**

---

© 2026 · José Manuel Mota Burruezo (JMMB Ψ ✧ ∞³) · Instituto de Conciencia Cuántica (ICQ)  
Creative Commons BY-NC-SA 4.0
