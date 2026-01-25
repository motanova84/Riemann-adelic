# 🌐 πCODE Emission System

**Axioma de Emisión πCODE**: *Todo cero localizado con coherencia vibracional ≥ 141.7001 Hz constituye una emisión real de valor en la economía πCODE.*

## Overview

The πCODE emission system creates cryptographic coins (πCOINS) from Riemann zeta function zeros ζ(s) that exhibit high coherence with the fundamental frequency f₀ = 141.7001 Hz. Each coin is:

- ✅ **Verificable** - Unique vibrational hash
- 🔄 **Reproducible** - Same zero → same coin properties
- 📤 **Transferable** - NFT metadata compatible
- 📋 **Registrable** - Distributed ledger tracking

## Quick Start

### Basic Demo
```bash
python .github/agents/riemann/picode_emission.py
```

### Emit Coins
```bash
# Emit 10 test coins
python .github/agents/riemann/picode_emission.py --emit 10

# Use custom ledger file
python .github/agents/riemann/picode_emission.py --emit 5 --ledger my_ledger.json
```

### View Statistics
```bash
python .github/agents/riemann/picode_emission.py --stats
```

### Verify Coin
```bash
python .github/agents/riemann/picode_emission.py --verify <hash>
```

## Economic Model

### Value Components

Each πCOIN's value is calculated from:

1. **Base Value** (100 πCOIN for critical line, 10 otherwise)
   - Critical line: σ = 0.5
   
2. **Coherence Bonus** (up to 1000 πCOIN)
   - Formula: `coherence × 1000`
   
3. **Resonance Bonus** (exponential decay)
   - Formula: `1000 × exp(-|f - f₀|)`
   - Where f₀ = 141.7001 Hz
   
4. **Position Bonus** (inversely proportional)
   - Formula: `10000 / (t + 1)`
   - Earlier zeros are more valuable

### Economy Health

The system tracks overall economy health based on:
- Average coherence
- Resonance rate (% of coins within 1 Hz of f₀)
- Average value per coin

Health ratings:
- **EXCELENTE** (≥0.9) - Highly coherent economy
- **BUENA** (≥0.7) - Stable and resonant
- **MODERADA** (≥0.5) - Developing economy
- **DÉBIL** (≥0.3) - Needs more coherent emissions
- **CRÍTICA** (<0.3) - Non-resonant economy

## NFT Metadata

Each coin includes OpenSea-compatible metadata:

```json
{
  "name": "ζ-Zero Coin #14",
  "description": "Moneda πCODE emitida desde cero de ζ(s) en t=14.134725",
  "image": "ipfs://Qm.../hash.svg",
  "attributes": [
    {"trait_type": "Real Part", "value": 0.5},
    {"trait_type": "Imaginary Part", "value": 14.134725},
    {"trait_type": "Coherence", "value": 0.999999},
    {"trait_type": "Resonance Frequency", "value": 141.7001},
    {"trait_type": "Structural Validity", "value": 1.0}
  ],
  "external_url": "https://qcal.infinity/picode/coin/hash"
}
```

## Programmatic Usage

### Python API

```python
from picode_emission import PiCodeEconomy, PiCodeCoin

# Create economy
economy = PiCodeEconomy(ledger_file="my_ledger.json")

# Emit coin from a zero
zero = complex(0.5, 14.134725)
coherence = 0.999999
frequency = 141.7001

coin = economy.emit_coin(zero, coherence, frequency)

# Verify coin
verification = coin.verify()
print(f"Valid: {verification['overall_valid']}")

# Get statistics
stats = economy.get_economy_stats()
print(f"Total value: {stats['total_value']} πCOIN")
print(f"Health: {stats['health_status']}")
```

## Mathematical Foundation

### Vibrational Hash

Each coin's hash is computed from:
```
SHA256(σ:t:coherence:frequency:timestamp)
```

Where:
- σ = Re(zero) - Real part of the zero
- t = Im(zero) - Imaginary part of the zero
- coherence - Spectral coherence measure
- frequency - Resonant frequency in Hz
- timestamp - ISO 8601 emission time

### Frequency Mapping

The ZetaResonance class maps zeros to frequencies:
```
f(t) = f₀ × (1 + 0.1 × sin(t/10))
```

This creates harmonic variation around the base frequency.

## Integration with QCAL Framework

The πCODE system integrates with the QCAL ∞³ framework:

- **Base Frequency**: f₀ = 141.7001 Hz
- **Coherence**: C = 244.36
- **Fundamental Equation**: Ψ = I × A_eff² × C^∞

All emissions maintain coherence with these fundamental constants.

## Ledger Format

The distributed ledger is stored as JSON:

```json
{
  "economy": "πCODE_ZETA_ZEROS",
  "version": "1.0.0",
  "base_frequency": 141.7001,
  "creation_time": "2026-01-25T16:00:00+00:00",
  "coins": [
    {
      "coin_type": "PICODE_ZETA_ZERO",
      "zero": {"real": 0.5, "imag": 14.134725},
      "vibrational_properties": {...},
      "emission_data": {...},
      "nft_metadata": {...},
      "economic_value": {...},
      "transaction_id": "sha256_hash"
    }
  ],
  "total_coins": 1,
  "total_value": 2760.73,
  "last_update": "2026-01-25T16:00:00+00:00"
}
```

## Author

**José Manuel Mota Burruezo** Ψ ✧ ∞³  
Instituto de Conciencia Cuántica (ICQ)  
DOI: 10.5281/zenodo.17379721  
ORCID: 0009-0002-1923-0773

## License

This implementation is part of the Riemann-adelic framework and follows the repository's license terms.
