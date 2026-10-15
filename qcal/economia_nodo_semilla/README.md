# QCAL Economía Nodo Semilla

**QCAL Economic Node** - Bitcoin-anchored coherence score implementation.

## 🌀 Overview

This module implements the QCAL economic framework that bridges Bitcoin blockchain data with the QCAL coherence formula:

```
Ψ = I × A²_eff × C^∞
```

Where:
- **I**: Intensity (normalized BTC value)
- **A_eff**: Effective quantum area = √φ × ln(888)
- **C^∞**: Infinite coherence factor = (141.7001 × 888.888) / 888

## 📐 QCAL Constants

| Constant | Value | Description |
|----------|-------|-------------|
| **f₀** | 141.7001 Hz | Base frequency (from .qcal_beacon) |
| **f_manifest** | 888 Hz | Manifestation frequency |
| **f_signature** | 888.888 Hz | Signature frequency |
| **φ (kappa_pi)** | 1.618033988749895 | Golden ratio |
| **C** | 244.36 | Coherence constant |

## 🔧 Usage

### Direct Python execution

```bash
# Run with default 1 BTC
python qcal/economia_nodo_semilla/main.py

# Run with specific BTC amount
python qcal/economia_nodo_semilla/main.py 2.5
```

### Using the launcher script

```bash
# Run with default 1 BTC
bash qcal/economia_nodo_semilla/launcher.sh

# Run with specific BTC amount  
bash qcal/economia_nodo_semilla/launcher.sh 0.5
```

## 📊 Output

The script outputs QCAL certification metadata in JSON format:

```json
{
    "token_id": 1,
    "btc_value_satoshis": 100000000,
    "btc_value_btc": 1.0,
    "cs_value_full": 10577.91,
    "cs_value_blockchain": 626675633.0,
    "coherence_score": 626675.633,
    "certified": true,
    "quantum_constants": {
        "freq_base": 141.7001,
        "freq_manifest": 888,
        "freq_signature": 888.888,
        "kappa_pi": 1.618033988749895,
        "coherence_c": 244.36
    },
    "bitcoin_reference": {
        "block_number": 888888,
        "coinbase": "Mined by AntPool",
        "fees_btc": 0.144,
        "timestamp": "2024-09-10T00:00:00Z"
    },
    "formula": "Ψ = I × A²_eff × C^∞",
    "signature": "∴ ✧ JMMB Ψ @ 888.888 Hz",
    "timestamp": "2026-03-06T21:52:28+00:00"
}
```

## 📈 Coherence Calculations

### Full Coherence Score (cs_value_full)

Uses the complete QCAL formula:

```python
I = btc_satoshis / 100_000_000
A_eff = √φ × ln(888)
C_inf = (141.7001 × 888.888) / 888
cs_full = I × A_eff² × C_inf
```

### Blockchain Coherence Score (cs_value_blockchain)

Calibrated to Bitcoin block 888888:

```python
cs_blockchain = 626675633 × (btc_satoshis / 100_000_000)
```

### Coherence Score

Final calibrated score:

```python
coherence_score = cs_blockchain / 1000
```

## 🎯 Bitcoin Block 888888

The implementation is anchored to Bitcoin block 888888, a cosmic alignment milestone:

- **Block Number**: 888888
- **Miner**: AntPool
- **Fees**: 0.144 BTC
- **Timestamp**: 2024-09-10T00:00:00Z

This block represents a significant numerical alignment in blockchain history and serves as the calibration point for QCAL coherence scores.

## 🧪 Testing

Basic validation tests:

```bash
# Run basic tests
python -c "
import sys
from pathlib import Path
sys.path.insert(0, str(Path('qcal/economia_nodo_semilla')))
from main import calculate_cs_full, FREQ_BASE

assert FREQ_BASE == 141.7001
cs1 = calculate_cs_full(100_000_000)
assert 10000 < cs1 < 11000
print('✅ Tests passed')
"
```

Full test suite:

```bash
python -m pytest tests/test_economia_nodo_semilla.py -v
```

## 📚 Integration with QCAL Framework

This economic node is fully integrated with the QCAL ∞³ framework:

- **Frequency alignment**: Uses f₀ = 141.7001 Hz from `.qcal_beacon`
- **Coherence constant**: Uses C = 244.36 from QCAL spectral theory
- **Golden ratio**: Uses φ = 1.618033988749895 in area calculations
- **Signature**: Includes QCAL signature ∴ ✧ JMMB Ψ @ 888.888 Hz

## 🔐 Certification

All outputs are marked as `certified: true` and include:

- Complete quantum constants
- Bitcoin blockchain reference (Block 888888)
- QCAL formula: Ψ = I × A²_eff × C^∞
- Timestamp in ISO format with timezone
- QCAL signature: ∴ ✧ JMMB Ψ @ 888.888 Hz

## 👤 Author

**José Manuel Mota Burruezo Ψ ✧ ∞³**
- Institution: Instituto de Conciencia Cuántica (ICQ)
- ORCID: 0009-0002-1923-0773
- Email: institutoconsciencia@proton.me

## 📜 License

- Content: Creative Commons BY-NC-SA 4.0
- Code: MIT License
- QCAL Framework: Sovereign Noetic License

## 🌌 Signature

```
∴𓂀Ω∞³
Canal Noēsico activo — Frecuencia 141.7001 Hz
```

---

*Part of the QCAL ∞³ framework for the Riemann Hypothesis proof.*
*DOI: 10.5281/zenodo.17379721*
