# 🏛️ Catedral Espectral - Quick Start Guide

## Ejecución Rápida

```bash
# Instalar dependencias
pip install numpy scipy matplotlib

# Ejecutar visualización
python visualize_catedral_espectral.py
```

## Salida Esperada

```
**********************************************************************
*                                                                    *
*               🏛️ CATEDRAL ESPECTRAL - LOS 4 PILARES                *
*         Resonancia: f₀ = 141.7001 Hz · Coherencia: Ψ = 1.0         *
*                                                                    *
**********************************************************************

======================================================================
🏛️ PILAR I: EL OPERADOR - MOMENTO EN EL SOLENOIDE
======================================================================
✓ Transformación u = log(x) completada
✓ Operador H = -i d/du autoadjunto
✓ Hermiticidad: 0.000000
✓ Coherencia Ψ: 1.000000

======================================================================
📐 PILAR II: GEODÉSICAS - EL LATIDO DE LOS PRIMOS
======================================================================
✓ 20 primos como notas base
✓ Flujo geodésico en superficie modular
✓ Correlación promedio: 0.345
✓ Los primos no 'están' ahí - son caminos que el flujo debe tomar

======================================================================
🔬 PILAR III: LA TRAZA - EL ESPEJO DE GUTZWILLER
======================================================================
✓ Densidad suave: d(E) = E/(2π)
✓ Contribución oscilante desde 10 ceros
✓ Traza geométrica: 2.411
✓ Coherencia geométrica-espectral: 0.980

======================================================================
🧬 PILAR IV: EL VÓRTICE 8 - LA TRAMPA DEL INFINITO
======================================================================
✓ Involución J: f(x) → x^(-1/2) f(1/x) aplicada
✓ Nodo Zero en x=1
✓ Vórtice 8 (simetría ∞) construido
✓ Nodos detectados: 16
✓ Coherencia Ψ: 0.951

✅ Visualización guardada: catedral_espectral_visualization.png

🎊 Coherencia Global: Ψ = 0.8188
✨ La Catedral Espectral está completa y en resonancia.
```

## Archivos Generados

- `catedral_espectral_visualization.png` - Visualización completa con 9 paneles

## Los 4 Pilares en 1 Minuto

### I. Operador H
**H = -i d/du** en coordenadas logarítmicas  
→ Motor de fase autoadjunto (Ψ = 1.0)

### II. Geodésicas  
Primos como pulsos en superficie modular  
→ f(p) = 141.7001/√p Hz

### III. Traza de Gutzwiller
Geometría ↔ Espectro  
→ Órbitas primas reflejadas en ceros de Riemann

### IV. Vórtice 8
Simetría x ↔ 1/x  
→ Infinito atrapado en nodos discretos

## Estructura de la Visualización

```
┌──────────────┬──────────────┬──────────────┐
│  Operador    │  Fase Flow   │  Geodésicas  │
│  Solenoide   │  H = -i d/du │  Primos      │
├──────────────┼──────────────┼──────────────┤
│  Frecuencias │  Traza       │  Ceros de    │
│  Resonancia  │  Gutzwiller  │  Riemann     │
├──────────────┼──────────────┼──────────────┤
│  Vórtice 8   │  Figura-8    │  Estado de   │
│  x ↔ 1/x     │  Infinito    │  Simbiosis   │
└──────────────┴──────────────┴──────────────┘
```

## Coherencia Esperada

| Pilar | Ψ Esperado |
|-------|-----------|
| I. Operador | 1.000 |
| II. Geodésicas | 0.3-0.4 |
| III. Traza | 0.98 |
| IV. Vórtice | 0.95 |
| **Global** | **~0.82** |

## Interpretación

### Ψ = 1.0 → Perfecto
Operador hermitiano, sin fuga de información

### Ψ ≈ 0.98 → Excelente  
Correspondencia geométrica-espectral muy precisa

### Ψ ≈ 0.95 → Muy Bueno
Simetría preservada con alta fidelidad

### Ψ ≈ 0.35 → Esperado
Correlación con estructura prima (fenómeno emergente)

## Modificación de Parámetros

Editar `visualize_catedral_espectral.py`:

```python
# Línea ~24: Cambiar frecuencia base
F0_QCAL = 141.7001  # Hz

# Línea ~25: Cambiar coherencia
C_COHERENCE = 244.36

# Línea ~66: Más primos
primes = np.array([...])  # Añadir más primos

# Línea ~147: Más ceros de Riemann
riemann_zeros = np.array([...])  # Añadir más ceros
```

## Troubleshooting

### Error: "No module named numpy"
```bash
pip install numpy scipy matplotlib
```

### Error: "DISPLAY not set"
El script detecta automáticamente entornos sin display y usa backend 'Agg'

### Figura no aparece
Revisa que se haya generado: `ls -lh catedral_espectral_visualization.png`

## Siguiente Paso

Ver documentación completa: `CATEDRAL_ESPECTRAL_README.md`

---

**f₀ = 141.7001 Hz · C = 244.36 · Ψ = 1.0**  
**♾️³ QCAL - Quantum Coherence Adelic Lattice**
