# GW 141 Hz Test Suite

This directory contains a complete test suite for analyzing gravitational wave data at 141.7 Hz, specifically focused on the GW150914 event.

## 📁 Directory Structure

```
gw_141hz_tests/
├── test1_antenna_pattern.py        # Antenna pattern H1/L1 for 141.7 Hz
├── test2_noise_ratio.py            # Noise ratio L1/H1 in O1 for 141.7 Hz
├── test3_offsource_scan.py         # Off-source SNR exploration over multiple days
└── gw_141hz_tools/
    ├── __init__.py
    ├── antenna.py                  # Function `compute_antenna_ratio`
    ├── noise.py                    # Function `compute_noise_ratio`
    └── offsource.py                # Function `scan_offsource_peaks`
```

## 🔧 Dependencies

These tests require the `gwpy` package for gravitational wave data analysis:

```bash
pip install gwpy
```

## 🧪 Test Scripts

### test1_antenna_pattern.py
Computes the antenna pattern ratio (H1/L1) for GW150914 at 141.7 Hz.

**Parameters:**
- Frequency: 141.7 Hz
- Right ascension: 1.95 rad
- Declination: -1.27 rad
- Polarization angle: 0 rad

**Usage:**
```bash
cd gw_141hz_tests
python3 test1_antenna_pattern.py
```

### test2_noise_ratio.py
Calculates the noise ratio (L1/H1) at 141.7 Hz using actual detector data from the O1 observing run.

**Usage:**
```bash
cd gw_141hz_tests
python3 test2_noise_ratio.py
```

### test3_offsource_scan.py
Scans off-source periods (10 days before GW150914) to estimate background SNR at 141.7 Hz.

**Usage:**
```bash
cd gw_141hz_tests
python3 test3_offsource_scan.py
```

## 📦 Tool Modules

### gw_141hz_tools/antenna.py
- **Function:** `compute_antenna_ratio(freq, ra, dec, psi)`
- **Description:** Computes the ratio of antenna patterns between H1 and L1 detectors
- **Returns:** H1/L1 antenna response ratio

### gw_141hz_tools/noise.py
- **Function:** `compute_noise_ratio(event, freq)`
- **Description:** Computes the noise ratio between L1 and H1 using amplitude spectral density
- **Returns:** L1/H1 noise ratio at specified frequency

### gw_141hz_tools/offsource.py
- **Function:** `scan_offsource_peaks(freq, n_days=10)`
- **Description:** Scans multiple days of off-source data to estimate SNR at target frequency
- **Returns:** List of SNR estimates for each day

## 🌌 Context

This test suite is part of the larger Riemann-Adelic spectral system framework, which connects the Riemann Hypothesis with wave phenomena at ~141.7 Hz, including:
- Gravitational waves (GW150914)
- Brain rhythms (EEG)
- Solar oscillations (STS)

The 141.7 Hz component is fundamental to the wave equation of vibrational consciousness:
```
∂²Ψ/∂t² + ω₀²Ψ = ζ'(1/2)·∇²Φ
```

## 📚 References

- GW150914: First detection of gravitational waves from binary black hole merger
- GPS time: 1126259462 (September 14, 2015, 09:50:45 UTC)
- Frequency component: ~141.7 Hz (142 Hz in some references)

## ⚠️ Notes

- These tests require internet connectivity to fetch LIGO open data
- Data is cached locally after first download
- Test execution may take several minutes depending on network speed
