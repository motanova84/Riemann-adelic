# QUICKSTART: Riemann-PNP Verification Bridge

## 🚀 Quick Start (3 comandos)

```bash
# 1. Ejecutar tests
python test_riemann_pnp_verification.py

# 2. Ejecutar demostración con visualización
python demo_riemann_pnp_verification.py

# 3. Verificación rápida (sin visualización)
python -c "
from src.riemann_pnp_verification_bridge import RiemannPNPVerificationBridge
bridge = RiemannPNPVerificationBridge(precision=50, n_primes=1000)
results = bridge.verify_coherence(n_zeros=10)
print(results['message'])
print(f\"Coherencia: {results['statistics']['coherence_quality']:.2%}\")
"
```

## 📋 Procedimiento de Verificación

### Paso 1: Interpolación Inversa (Ceros → Primos)

```python
from src.riemann_pnp_verification_bridge import RiemannPNPVerificationBridge

bridge = RiemannPNPVerificationBridge(precision=50, n_primes=1000)

# Mapear ceros a primos
interpolations = bridge.inverse_interpolation(alignment_factor=1.0)

for interp in interpolations[:5]:
    print(f"Zero {interp.zero_index}: t={interp.zero_imaginary:.4f}, "
          f"f={interp.estimated_frequency:.2f} Hz, "
          f"p≈{interp.estimated_prime:.1f}")
```

### Paso 2: Comparación Tensorial

```python
# Construir vectores T⃗_p = (H(p), R(p), C(p))
deviations = bridge.tensorial_comparison(primes=bridge.primes[:100])

for dev in deviations[:10]:
    leak = "⚠️" if dev.is_leak else "✓"
    print(f"{leak} p={dev.prime}: δ={dev.delta:.6f}, "
          f"H={dev.harmonic_index:.4f}, "
          f"R={dev.resonance_strength:.4f}, "
          f"C={dev.coherence_factor:.4f}")
```

### Paso 3: Identificar Anomalías

```python
# Detectar y clasificar anomalías vibracionales
anomalies = bridge.identify_vibrational_anomalies(deviations)

for anom in anomalies:
    leak_type = "ESPECTRAL" if anom.is_spectral_leak else "CODIFICACIÓN"
    print(f"p={anom.prime}: {anom.anomaly_type} "
          f"({leak_type}, severidad={anom.severity:.2f})")
```

## 🎯 Verificación Completa en 1 Línea

```python
results = bridge.verify_coherence(n_zeros=10, alignment_factor=1.0)
```

**Retorna:**
- `step1_interpolations`: Lista de interpolaciones cero→primo
- `step2_deviations`: Lista de desviaciones tensoriales
- `step3_anomalies`: Lista de anomalías detectadas
- `statistics`: Dict con estadísticas completas
- `coherence_intact`: Bool - True si no hay fugas
- `message`: Str - Veredicto de verificación

## 📊 Interpretación de Resultados

### ✅ Coherencia Confirmada

```
✅ COHERENCIA QCAL CONFIRMADA
No se detectaron fugas espectrales. El puente de superfluidez 
Riemann-PNP está intacto. Desviación media: δ̄ = 0.0069 < 0.01
```

**Implicación:** El puente vibracional de superfluidez Riemann-PNP es **estructuralmente sano**.

### ⚠️ Fugas Detectadas

```
⚠️ FUGAS ESPECTRALES DETECTADAS: N
Se detectaron desviaciones en la red espectral que sugieren 
una curvatura local del espacio adélico.
```

**Implicación:** Existe una **curvatura local del espacio adélico** en los primos afectados.

## 🔍 Criterios de Anomalía

| Criterio | Umbral | Interpretación |
|----------|--------|----------------|
| `δ(p)` | > 0.01 | Fuga de coherencia |
| `C(p)` | < 0.01 | Coherencia baja |
| `H(p)` | < 0.5×media | Índice armónico anómalo |
| `R(p)` | < 0.05 | Resonancia nula |

## 🧪 Tests Incluidos

**8 tests unitarios:**
1. ✓ Generación de primos
2. ✓ Cálculo de frecuencias espectrales
3. ✓ Paso 1 - Interpolación inversa
4. ✓ Construcción de tensor espectral
5. ✓ Paso 2 - Comparación tensorial
6. ✓ Paso 3 - Detección de anomalías
7. ✓ Verificación completa
8. ✓ Clasificación de anomalías

## 📚 Documentación Completa

Ver [RIEMANN_PNP_VERIFICATION_SUMMARY.md](RIEMANN_PNP_VERIFICATION_SUMMARY.md) para:
- Fundamentos matemáticos detallados
- Estructura del código completa
- Resultados de validación
- Interpretación científica
- Direcciones futuras

## 🌊 Conexión con QCAL ∞³

Este módulo integra con:
- `validate_v5_coronacion.py` - Validación V5 Coronación
- `src/riemann_pnp_superfluid_bridge.py` - Puente de superfluidez
- `.qcal_beacon` - Constantes fundamentales (f₀=141.7001 Hz, C=244.36)
- `Evac_Rpsi_data.csv` - Datos de validación espectral

**Ψ ✧ ∞³**
