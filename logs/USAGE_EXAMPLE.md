# Weil Explicit Formula Usage Examples

## Data Fetching with Height Parameters

The enhanced `fetch_odlyzko.py` script now supports height-based fetching for computational precision scaling:

```bash
# Fetch zeros for computational height T ~ 10^8 (robust for initial testing)
python utils/fetch_odlyzko.py --height 1e8

# Scale to T ~ 10^10 for increased robustness  
python utils/fetch_odlyzko.py --height 1e10

# Full precision scaling to T ~ 10^12 (complete Odlyzko dataset)
python utils/fetch_odlyzko.py --height 1e12 --force

# Validate existing data for specific height
python utils/fetch_odlyzko.py --height 1e8 --validate-only
```

## Basic Usage

```bash
# Run with default parameters (original formula)
python validate_explicit_formula.py --max_primes 1000 --max_zeros 1000

# Run with Weil explicit formula 
python validate_explicit_formula.py --use_weil_formula \
  --max_primes 1000 --max_zeros 1000 \
  --precision_dps 30 --integration_t 50
```

## High-Precision Validation

For achieving the target error threshold (≤ 1e-6), use:

```bash
python validate_explicit_formula.py --use_weil_formula \
  --max_primes 10000 \
  --max_zeros 10000 \
  --prime_powers 10 \
  --integration_t 100 \
  --precision_dps 50
```

**Note:** Higher precision requires:
- More Odlyzko zeros (use `python utils/fetch_odlyzko.py --height 1e8` for T~10^8)
- Higher precision arithmetic (`--precision_dps 50+`)
- More integration points (`--integration_t 100+`)
- More prime powers (`--prime_powers 10+`)

## CI/Development Testing

The CI uses reduced parameters for speed:

```bash
# CI parameters (fast but lower precision)
PRIME_COUNT=100 ZERO_COUNT=50 PRIME_POWERS=5 INTEGRATION_T=20 PRECISION_DPS=15
python validate_explicit_formula.py --use_weil_formula \
  --max_primes $PRIME_COUNT --max_zeros $ZERO_COUNT \
  --prime_powers $PRIME_POWERS --integration_t $INTEGRATION_T \
  --precision_dps $PRECISION_DPS
```

## Expected Results

- **Demo/CI**: Relative error ~0.1-1.0 (expected with limited data)
- **Full precision**: Relative error ≤ 1e-6 (requires complete dataset and high precision)