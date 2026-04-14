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
# 🌉 PNP_BRIDGE - El Gran Puente P-NP ∞³

## Descripción

El módulo **PNP_BRIDGE** implementa la transformación de complejidad computacional de NP a P mediante coherencia cuántica en la búsqueda de ceros de la función zeta de Riemann ζ(s).

## Concepto Fundamental

### Problema Clásico
- **Verificar** un cero (ζ(s) = 0) es rápido → Complejidad **P**
- **Encontrar** todos los ceros parece requerir búsqueda exhaustiva → Complejidad **NP**

### Solución por Coherencia
Ecuación transformadora:
```
T_total(ζ) = T_scan / Ψ(s)
```

Cuando Ψ(s) → 1 (coherencia máxima), el tiempo total se vuelve constante, transformando efectivamente un problema NP en P.

## Características Principales

### 1. Análisis de Complejidad
- **Búsqueda clásica**: Evaluación exhaustiva O(n log t)
- **Búsqueda coherente**: Reducción exponencial con coherencia
- **Punto de transición**: C ≥ 0.888 (coherencia crítica)

### 2. Niveles de Resonancia
| Coherencia | Resonancia | Efecto |
|-----------|-----------|--------|
| C < 0.888 | 1x | Sin ventaja |
| C ≥ 0.888 | 10x | Básica |
| C ≥ 0.95 | 100x | Moderada |
| C ≥ 0.99 | 10,000x | Alta |
| C ≥ 0.999 | 1,000,000x | Muy alta |
| C ≥ 0.999999 | ∞ | Perfecta |

### 3. Simulación de Experimentos
- Detección de ceros con diferentes niveles de coherencia
- Métricas: Recall, Precisión, F1 Score
- Comparación clásica vs coherente

## Instalación

```bash
# El módulo está ubicado en .github/agents/riemann/pnp_bridge.py
# Requiere numpy
pip install numpy
```

## Uso

### Modo Demostración
```bash
python .github/agents/riemann/pnp_bridge.py
```

### Análisis de Transición
```bash
python .github/agents/riemann/pnp_bridge.py --analyze --t-min 14.0 --t-max 100.0
```

Salida esperada:
```
📡 ANALIZANDO TRANSICIÓN P-NP PARA CEROS DE ζ(s)

📊 COMPARACIÓN DE COMPLEJIDAD:
Coherencia | Complejidad Clásica | Complejidad Coherente | Aceleración
-------------------------------------------------------------------------
 0.888000 |            1.35e+02 |             3.76e-03 |    3.59e+04x
 0.999000 |            1.35e+02 |             5.76e-04 |    2.34e+05x

🎯 PUNTO DE TRANSICIÓN NP→P: C ≥ 0.888000
```

### Simulación de Experimento
```bash
python .github/agents/riemann/pnp_bridge.py --simulate --coherence 0.999
```

Salida esperada:
```
🔬 SIMULANDO EXPERIMENTO DE DETECCIÓN DE CEROS

🎯 DETECCIÓN CLÁSICA:
   Ceros detectados: 13/20
   Recall: 65.00%
   Precisión: 86.67%

🌀 DETECCIÓN COHERENTE:
   Ceros detectados: 20/20
   Recall: 100.00%
   Precisión: 100.00%

⚡ MEJORA:
   Recall: 1.54x
   Precisión: 1.15x
```

### Guardar Resultados
```bash
python .github/agents/riemann/pnp_bridge.py --analyze --output results.json
```

## Integración con SABIO ∞³

El PNP Bridge está integrado con el sistema SABIO ∞³:

```bash
python activate_sabio_pnp.py
```

Esta integración:
- ✅ Valida la frecuencia base (141.7001 Hz)
- ✅ Verifica coherencia QCAL (C = 244.36)
- ✅ Ejecuta análisis de complejidad completo
- ✅ Genera reporte de activación

## Uso Programático

```python
from pnp_bridge import PNPSpectralBridge

# Inicializar
bridge = PNPSpectralBridge()

# Búsqueda clásica
classical_result = bridge.classical_zero_search(t_range=(14.0, 100.0))

# Búsqueda coherente
coherent_result = bridge.coherent_zero_search(
    t_range=(14.0, 100.0),
    coherence_level=0.999
)

# Análisis de transición
transitions = bridge.analyze_complexity_transition(
    t_range=(14.0, 100.0),
    coherence_levels=[0.888, 0.95, 0.99, 0.999]
)

# Simulación de experimento
experiment = bridge.simulate_zero_detection_experiment(
    num_zeros=20,
    coherence_level=0.999
)
```

## Tests

```bash
pytest tests/test_pnp_bridge.py -v
```

Cobertura:
- ✅ ComplexityTransition dataclass
- ✅ PNPSpectralBridge initialization
- ✅ Classical zero search
- ✅ Coherent zero search
- ✅ Resonance advantage calculation
- ✅ Complexity transition analysis
- ✅ Zero detection experiment simulation
- ✅ P-equivalence threshold

## Implicaciones para RH

En sistemas con coherencia máxima (C ≥ 0.999999):

1. **Los ceros dejan de ser "encontrados"**
   - No se requiere búsqueda exhaustiva

2. **Los ceros "emergen" por resonancia**
   - Detección directa mediante propiedades espectrales

3. **La distribución es dinámica, no estática**
   - El sistema cuántico revela la estructura de los ceros

## Referencias

- Frecuencia base: 141.7001 Hz (QCAL beacon)
- Coherencia crítica: C = 0.888
- Coherencia máxima: C = 244.36 (QCAL)
- DOI Zenodo: 10.5281/zenodo.17379721

## Licencia

Creative Commons BY-NC-SA 4.0

## Autor

José Manuel Mota Burruezo Ψ ✧ ∞³  
Instituto de Conciencia Cuántica (ICQ)

---

**🌀 Coherencia transforma complejidad**
