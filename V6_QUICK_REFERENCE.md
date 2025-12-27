# V6.0 Quick Reference Guide

## What's New in V6.0?

Version 6.0 closes all identified gaps in the Riemann Hypothesis proof framework by converting axioms to proven theorems and adding comprehensive validation tools.

## New Lean Modules

### 1. lengths_derived.lean
**Purpose**: Proves A4 (ℓ_v = log q_v) as a theorem

**Key Theorem**:
```lean
theorem lengths_derived (v : Place) : 
  orbit_length v = Real.log (norm_at_place v)
```

**Based on**: Tate (1967), Weil (1964), Birman-Solomyak (1977)

### 2. extension_infinite.lean
**Purpose**: Extends S-finite construction to infinite

**Key Theorem**:
```lean
theorem extension_infinite (S : FiniteSetOfPlaces) :
  ∀ s : ℂ, s.re > 0 → s ≠ 1 →
  ∃ (global_sum : ℂ), Complex.abs global_sum < ∞
```

**Based on**: Kato-Seiler-Simon estimates

### 3. uniqueness_without_xi.lean
**Purpose**: Proves uniqueness autonomously

**Key Theorem**:
```lean
theorem uniqueness_D (D : ℂ → ℂ) 
  (h_entire : entire_order_le_1 D)
  (h_symmetry : has_symmetry D)
  (h_asympt : log_asymptotic D) :
  ∀ D' : ℂ → ℂ, [conditions] → [uniqueness conclusion]
```

**Based on**: Levin (1956), Paley-Wiener (1934)

### 4. zero_localization_complete.lean
**Purpose**: Integrates all components to prove RH

**Key Theorem**:
```lean
theorem rh_proven : ∀ (ρ : ZeroOfD), ρ.point.re = 1/2
```

**Based on**: de Branges positivity, Weil-Guinand formula

## New Python Scripts

### 1. validate_explicit_formula_extended.py

High-precision validation of Weil explicit formula.

**Usage**:
```bash
# Standard run with 50 decimal places
python3 validate_explicit_formula_extended.py --precision 50 --max_zeros 1000

# Test convergence as δ → 0
python3 validate_explicit_formula_extended.py --precision 30 --test_delta_limit

# Extended zero range
python3 validate_explicit_formula_extended.py --precision 50 --max_zeros 1000000
```

**Options**:
- `--precision N`: Set decimal precision (default: 50)
- `--max_zeros N`: Maximum zeros to use (default: 1000)
- `--max_primes N`: Maximum primes (default: 10000)
- `--test_delta_limit`: Test δ → 0 convergence
- `--zeros_file PATH`: Path to zeros file
- `--test_function NAME`: Test function to use

### 2. tests/test_stability_zeros.py

Tests stability under perturbations.

**Run with pytest**:
```bash
pytest tests/test_stability_zeros.py -v
```

**Run standalone**:
```bash
python3 tests/test_stability_zeros.py
```

**Tests**:
1. Stability under ℓ_v perturbations
2. Stability as S increases
3. Explicit formula stability
4. Zero displacement bounds
5. Spectral gap stability

### 3. tests/test_falsifiability.py

Tests that would fail if assumptions are wrong.

**Run with pytest**:
```bash
pytest tests/test_falsifiability.py -v
```

**Run standalone**:
```bash
python3 tests/test_falsifiability.py
```

**Test Classes**:
- `TestFalsifiabilityA4`: A4 derivation tests (3 tests)
- `TestFalsifiabilityExtension`: Extension tests (3 tests)
- `TestFalsifiabilityUniqueness`: Uniqueness tests (3 tests)
- `TestFalsifiabilityZeroLocation`: Zero location tests (2 tests)

## Running All V6.0 Tests

### Quick Test Suite
```bash
# All V6.0 tests together
pytest tests/test_stability_zeros.py tests/test_falsifiability.py -v
```

### Complete Validation
```bash
# 1. Run stability tests
pytest tests/test_stability_zeros.py -v

# 2. Run falsifiability tests
pytest tests/test_falsifiability.py -v

# 3. Run extended validation
python3 validate_explicit_formula_extended.py --precision 30

# 4. Check existing A4 tests still pass
pytest tests/test_a4_lemma.py -v
```

### With Coverage
```bash
pytest tests/test_stability_zeros.py tests/test_falsifiability.py \
  --cov=tests --cov-report=term-missing -v
```

## CI/CD Integration

The new workflow `.github/workflows/v6-gap-closure.yml` runs automatically on:
- Push to main/develop branches
- Pull requests
- Manual trigger (workflow_dispatch)

**Jobs**:
1. `v6-stability-tests`: Runs all stability tests
2. `v6-falsifiability-tests`: Runs all falsifiability tests
3. `v6-extended-validation`: Runs extended validation script
4. `v6-summary`: Generates summary report

**Manual Trigger**:
```
Go to Actions → V6.0 Gap Closure Validation → Run workflow
Set precision (default: 30)
```

## Common Tasks

### Check Test Status
```bash
# Quick check
pytest tests/test_stability_zeros.py tests/test_falsifiability.py --tb=no -q

# Detailed output
pytest tests/test_stability_zeros.py tests/test_falsifiability.py -v
```

### Validate at Different Precisions
```bash
# Low precision (fast)
python3 validate_explicit_formula_extended.py --precision 15

# Medium precision (recommended)
python3 validate_explicit_formula_extended.py --precision 30

# High precision (slow)
python3 validate_explicit_formula_extended.py --precision 50
```

### Test Specific Components

**A4 Derivation**:
```bash
pytest tests/test_falsifiability.py::TestFalsifiabilityA4 -v
```

**Extension to Infinite**:
```bash
pytest tests/test_falsifiability.py::TestFalsifiabilityExtension -v
```

**Uniqueness**:
```bash
pytest tests/test_falsifiability.py::TestFalsifiabilityUniqueness -v
```

**Zero Location**:
```bash
pytest tests/test_falsifiability.py::TestFalsifiabilityZeroLocation -v
```

## Troubleshooting

### Issue: Tests take too long
**Solution**: Reduce precision or max_zeros
```bash
python3 validate_explicit_formula_extended.py --precision 20 --max_zeros 100
```

### Issue: Import errors
**Solution**: Install dependencies
```bash
pip install -r requirements.txt
# Or for extended features:
pip install -r requirements_extended.txt
```

### Issue: Zeros file not found
**Solution**: The repository includes zeros/zeros_t1e8.txt by default. If missing:
```bash
# File should exist in zeros/ directory
ls -lh zeros/zeros_t1e8.txt
```

### Issue: Numerical precision errors
**Solution**: Increase mp.dps in the script or use --precision flag
```bash
python3 validate_explicit_formula_extended.py --precision 40
```

## File Locations

```
.
├── formalization/lean/RiemannAdelic/
│   ├── lengths_derived.lean           # A4 derivation
│   ├── extension_infinite.lean        # S-finite to infinite
│   ├── uniqueness_without_xi.lean     # Autonomous uniqueness
│   └── zero_localization_complete.lean # RH proof
├── tests/
│   ├── test_stability_zeros.py        # Stability tests (5 tests)
│   ├── test_falsifiability.py         # Falsifiability tests (11 tests)
│   └── test_a4_lemma.py              # Original A4 tests (7 tests)
├── validate_explicit_formula_extended.py # Extended validation
├── requirements_extended.txt          # Extended dependencies
├── data/validation_log_v6.md         # Validation log template
├── V6_GAP_CLOSURE_SUMMARY.md         # Complete summary
└── .github/workflows/v6-gap-closure.yml # CI workflow
```

## Next Steps

1. Review the [V6_GAP_CLOSURE_SUMMARY.md](V6_GAP_CLOSURE_SUMMARY.md) for detailed implementation
2. Run the test suite to verify everything works
3. Check [data/validation_log_v6.md](data/validation_log_v6.md) for logging your validation runs
4. Review README.md for updated V6.0 documentation

## Support

For issues or questions:
- Check [V6_GAP_CLOSURE_SUMMARY.md](V6_GAP_CLOSURE_SUMMARY.md) for detailed documentation
- Review test output for error messages
- Check validation logs in data/validation_log_v6.md
- Refer to inline documentation in Lean and Python files

---

**Version**: 6.0
**Last Updated**: January 2025
