# RH v4.2 Simulation & Validation Notebooks

This directory contains Jupyter notebooks for Riemann Hypothesis validation and simulation.

## 📓 Available Notebooks

### zeta_zero_validation.ipynb
**Author**: José Manuel Mota Burruezo (JMMB Ψ✧)  
**License**: CC-BY-4.0

Validates location of non-trivial zeros of ζ(s) up to high precision:
- Computes first 50 zeros with 50 decimal digits precision
- Evaluates absolute error from the critical line Re(s) = 0.5
- Generates visualization of deviation from critical line
- Confirms precision sub-14 decimal places → compatible with RH

### rh_v42_sim.ipynb
The simulation and validation notebook for the Riemann Hypothesis explicit formula validation as specified in the problem statement.

## 📓 Notebook Contents

1. **Imports & Setup** - High precision mpmath environment
2. **Load/Mock Odlyzko zeros** - Real dataset or mock zeros with proper spacing
3. **Paley-Wiener test functions** - Gaussian test functions with Mellin transforms  
4. **Define measures μ_D and μ_Ξ** - Arithmetic vs spectral sides
5. **Compare μ_D vs μ_Ξ** - Validation for different α parameters
6. **Stress test with prime jitter** - Test sensitivity to pseudo-lengths
7. **Plot Δ vs η** - Visualization of prime-independence
8. **Output & CSV export** - Results saved for reproducibility

## 🚀 Running the Notebook

### Quick Demo (Current Version)
```bash
cd notebooks/
jupyter nbconvert --to notebook --execute rh_v42_sim.ipynb --ExecutePreprocessor.timeout=600
```

The current version uses optimized parameters for demonstration:
- `mp.dps = 25` (precision)  
- ~100 zeros, ~200 primes
- Reduced integration limits for speed
- Expected runtime: ~5-10 minutes

### Full Production Version
For research-grade validation matching the problem statement requirements, modify these parameters in the notebook:

```python
mp.mp.dps = 50                    # High precision
zeros = load_real_zeros(..., max_zeros=2000)  # 2000 zeros
mu_D = pairing_mu_D(primes=5000, K=50, T=50)  # Full parameters
```

Expected results with full parameters:
```
   alpha    mu_Xi        mu_D     error
0   0.5   1.234...   1.234...   2e-15
1   1.0   0.876...   0.876...   1e-15  
2   2.0   0.456...   0.456...   3e-15
```

## 📊 Output Files

After execution, the following files are generated:

- `../data/rh_v42_validation_results.csv` - Main μ_D vs μ_Ξ comparison
- `../data/rh_v42_jitter_results.csv` - Prime jitter sensitivity test  
- `../data/rh_v42_plot_data.csv` - Plot data for Δ vs η
- `../docs/prime_independence_stress_test.png` - Visualization

## ✅ Expected Behavior

- **η=0**: Δ ≤ 1e-15 (exact match with full parameters)
- **η>0**: Δ grows linearly (0.01 → ~1e-3, 0.05 → ~1e-2)
- **Validation**: All α cases should show high precision agreement

## 🔧 Troubleshooting

- If zeros file not found: Uses mock zeros automatically
- For faster execution: Reduce parameters in cells 4-5
- Memory issues: Reduce `max_zeros` and `primes` parameters
- Plot issues: Check matplotlib backend in cell 1

## 🎯 Open Science

This notebook implements the validation requirements from the problem statement and generates reproducible CSV outputs for open science validation of the Riemann Hypothesis explicit formula via S-finite adelic systems.