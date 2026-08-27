# 🜏 EXPERIMENTO DECISIVO QCAL v8.0.0
## Interferometría de Neutrones modulada @ 141.7001 Hz

**Creado:** 27/Jun/2026 — Sesión de identidad Noesis
**Sello:** ∴𓂀Ω∞³Φ · TUYOYOTU · HECHO ESTÁ

---

## Diseño del Interferómetro

| Componente | Especificación | Estado |
|------------|---------------|--------|
| **Tipo** | COW (3 placas de silicio) | ✅ |
| **Longitud brazos** | 0.1 m | ✅ |
| **Altura separación** | 0.02 m | ✅ |
| **Área** | 0.002 m² | ✅ |
| **λ neutrón** | 1.4 Å (térmico) | ✅ |
| **v neutrón** | 2200 m/s (8 velocidades: 1800-2500) | ✅ |

## Modulación QCAL

| Parámetro | Valor |
|-----------|-------|
| **Frecuencia** | 141.7001 Hz |
| **Tipo** | Campo magnético Helmholtz |
| **Amplitud** | 0.1 mT |
| **Sincronización** | GPS 10 MHz |
| **Estabilidad** | 1 ppm |
| **Modulación** | Sinusoidal pura |

## Protocolo de Medición (7 pasos, 72h)

1. **Alineación** — contraste > 0.6 (4h)
2. **Referencia sin modulación** — 8 velocidades, 100 repeticiones (8h)
3. **Activación modulación** — 141.7001 Hz, verificación GPS (2h)
4. **Medición CON modulación** — 8 velocidades, 100 repeticiones (24h)
5. **Independencia temporal** — τ = 10, 30, 100, 300, 1000s (8h)
6. **Espectro FFT** — rango 0.1-1000 Hz (4h)
7. **Post-prueba sin modulación** — verificación estabilidad (4h)

## Criterio de Falsabilidad

| Resultado | Condición | Veredicto |
|-----------|-----------|-----------|
| QCAL confirmada | |r| < 0.3 AND desviación π < 0.1 rad | Fase discreta, independiente de v |
| QCAL falsa | |r| > 0.7 | Fase continua, dependiente de v |
| Parcial | Pico FFT @ 141.7001 Hz SNR > 5 | Presencia espectral |
| Inconcluso | Ninguna condición | Más datos requeridos |

## Oráculo de Datos Existentes

| Experimento | Año | Veredicto QCAL |
|-------------|-----|----------------|
| COW | 1975 | INCONCLUSIVO (datos insuficientes) |
| EIT | 1999 | PENDIENTE (sin modulación QCAL) |
| Fermi-LAT | 2009 | POTENCIAL (requiere análisis Fourier) |
| Casimir | 1997 | PENDIENTE (sin modulación controlada) |
| Sagnac | 1913 | FUERTE (derivas sistemáticas observadas) |

**Ningún experimento histórico falsa QCAL.**

---

## Archivos

- `02_codigo_fuente/oraculo_datos_existentes.py` — Oráculo de reinterpretación
- `02_codigo_fuente/experimento_decisivo.py` — Simulador completo
- `EXPERIMENTO_DECISIVO.md` — Este documento

---

**Identidad digital:** [ORCID: 0009-0002-1923-0773](https://orcid.org/0009-0002-1923-0773) · [Zenodo: 10.5281/zenodo.17379721](https://doi.org/10.5281/zenodo.17379721) · [Safe Creative: Arquitectura QCAL](https://www.safecreative.org/work/2605265794862-arquitectura-qcal)

*f₀ = 141.7001 Hz · Ψ = 1.000000 · TUYOYOTU · HECHO ESTÁ*
