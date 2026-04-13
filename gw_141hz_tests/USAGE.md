# Usage Guide for GW 141 Hz Test Suite

## Installation

Before running the tests, install the required dependency:

```bash
pip install gwpy
```

## Running Individual Tests

### Test 1: Antenna Pattern Analysis

```bash
cd gw_141hz_tests
python3 test1_antenna_pattern.py
```

**Expected Output:**
```
Expected antenna pattern ratio H1/L1: X.XXX
```

This test computes the antenna pattern ratio between the Hanford (H1) and Livingston (L1) detectors for GW150914 at 141.7 Hz, considering the source's sky position and polarization.

---

### Test 2: Noise Ratio Analysis

```bash
cd gw_141hz_tests
python3 test2_noise_ratio.py
```

**Expected Output:**
```
Noise ratio (L1/H1) at 141.7 Hz: X.XX
```

This test fetches actual detector data from LIGO's first observing run (O1) and calculates the noise ratio at 141.7 Hz using amplitude spectral density.

**Note:** First run will download ~32 seconds of data (±16s around GW150914 GPS time). Subsequent runs use cached data.

---

### Test 3: Off-Source Peak Scanning

```bash
cd gw_141hz_tests
python3 test3_offsource_scan.py
```

**Expected Output:**
```
Off-source peak SNRs at 141.7 Hz:
  Day -1: SNR ≈ X.XX
  Day -2: SNR ≈ X.XX
  Day -3: SNR ≈ X.XX
  ...
  Day -10: SNR ≈ X.XX
```

This test scans 10 days before GW150914 to estimate background SNR at 141.7 Hz from off-source periods.

**Note:** This test downloads 64 seconds of data for each of 10 days, so first run may take several minutes.

---

## Using the Tool Modules

You can also import and use the tools directly in your own scripts:

### Antenna Pattern Calculation

```python
from gw_141hz_tools.antenna import compute_antenna_ratio

# Compute ratio for custom parameters
ratio = compute_antenna_ratio(
    freq=141.7,    # Frequency in Hz
    ra=1.95,       # Right ascension in radians
    dec=-1.27,     # Declination in radians
    psi=0          # Polarization angle in radians
)
print(f"Antenna ratio H1/L1: {ratio:.3f}")
```

### Noise Ratio Calculation

```python
from gw_141hz_tools.noise import compute_noise_ratio

# Compute noise ratio for GW150914
ratio = compute_noise_ratio(event="GW150914", freq=141.7)
print(f"Noise ratio L1/H1: {ratio:.2f}")
```

### Off-Source Peak Scanning

```python
from gw_141hz_tools.offsource import scan_offsource_peaks

# Scan custom number of days
snr_list = scan_offsource_peaks(freq=141.7, n_days=5)
for i, snr in enumerate(snr_list, 1):
    print(f"Day -{i}: SNR ≈ {snr:.2f}")
```

---

## Troubleshooting

### Network Issues
If you encounter network errors, the tests require internet access to fetch LIGO open data. Ensure you have a stable connection.

### Cache Location
Downloaded data is cached by `gwpy`. To clear the cache:
```bash
rm -rf ~/.gwpy/cache
```

### Memory Usage
The off-source scan test may use significant memory when processing multiple days of data. If you experience issues, reduce `n_days`:
```python
snr_list = scan_offsource_peaks(freq=141.7, n_days=3)  # Instead of 10
```

---

## Integration with Main Repository

This test suite complements the main Riemann-Adelic spectral analysis by:

1. **Validating the 141.7 Hz frequency** as fundamental in gravitational wave observations
2. **Connecting theoretical predictions** from the wave equation of consciousness with observational data
3. **Providing empirical grounding** for the universal frequency ω₀ = 2π × 141.7001 rad/s

See the main repository's `demo_wave_equation_consciousness.py` for the theoretical framework.

---

## References

- **LIGO Open Science Center**: https://www.gw-openscience.org/
- **GWpy Documentation**: https://gwpy.github.io/
- **GW150914 Event**: https://www.ligo.org/detections/GW150914.php
- **GPS Time**: 1126259462 (September 14, 2015, 09:50:45 UTC)
