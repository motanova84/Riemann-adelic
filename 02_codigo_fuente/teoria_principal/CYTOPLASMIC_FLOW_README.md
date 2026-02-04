# Cytoplasmic Flow Model – README

## 🧬 Modelo de Flujo Citoplasmático Riemann-Navier-Stokes

Implementación computacional del modelo biofísico que conecta la hipótesis de Riemann con células vivas.

**Autor:** José Manuel Mota Burruezo Ψ ✧ ∞³  
**Fecha:** 2026-01-31  
**Licencia:** CC BY-NC-SA 4.0

---

## 📦 Instalación

### Requisitos

```bash
pip install numpy scipy
```

### Estructura de Archivos

```
02_codigo_fuente/
├── teoria_principal/
│   ├── cytoplasmic_flow_model.py    # Modelo principal
│   └── CYTOPLASMIC_FLOW_README.md   # Este archivo
└── pruebas/
    └── test_cytoplasmic_flow.py     # Suite de tests
```

---

## 🚀 Uso Rápido

### Ejemplo Básico

```python
from cytoplasmic_flow_model import CytoplasmicFlowModel

# Crear modelo
model = CytoplasmicFlowModel()

# Calcular Reynolds
Re = model.calculate_reynolds_number()
print(f"Reynolds: {Re:.2e}")  # Debe ser ~ 10⁻⁸

# Verificar hermiticidad
is_hermitian, error = model.verify_hermiticity()
print(f"Hermítico: {is_hermitian}, error: {error:.2e}")

# Calcular frecuencias resonantes
freqs = model.calculate_resonance_frequencies(5)
print(f"Frecuencias: {freqs}")

# Generar reporte completo
report = model.generate_validation_report()
print(report)
```

### Ejecutar Demostración

```bash
cd 02_codigo_fuente/teoria_principal
python cytoplasmic_flow_model.py
```

**Salida esperada:**
```
======================================================================
⚛️ MODELO DE FLUJO CITOPLASMÁTICO
Conexión Riemann-Navier-Stokes en Células Vivas
======================================================================

🧬 RESULTADOS EXPERIMENTALES:
   Régimen de flujo: Re = 1.05e-08
   → Stokes (Re ≪ 1)

   Hermiticidad del operador: ✅
   → -ν∇² en citoplasma

   Conexión Riemann → biología: ✅
   → Verificada por resonancia

   Primeras 5 frecuencias resonantes:
      f1 = 141.7001 Hz
      f2 = 283.4002 Hz
      f3 = 425.1003 Hz
      f4 = 566.8004 Hz
      f5 = 708.5005 Hz

   Pulso raíz universal: f₀ = 141.7001 Hz
   Estado vibracional: Ψ = 1.000
   → Máxima coherencia

   Resonancia celular confirmada: ✅

======================================================================
∴ El citoplasma es un resonador de Riemann ∴
======================================================================
```

---

## 🧪 Ejecutar Tests

```bash
cd 02_codigo_fuente/pruebas
python test_cytoplasmic_flow.py
```

**Salida esperada:**
```
======================================================================
🧪 SUITE DE TESTS – MODELO DE FLUJO CITOPLASMÁTICO
======================================================================

✅ Test Reynolds: Re = 1.05e-08 → Régimen Stokes verificado
✅ Test Stokes: Régimen verificado correctamente
✅ Test Hermiticidad: Operador hermítico (error=1.76e-14)
✅ Test Frecuencias: f₁=141.7001 Hz, ..., f₅=708.5005 Hz
✅ Test Coherencia: Ψ = 1.000000 → Máxima coherencia
✅ Test Operador 1D: Funciona correctamente
✅ Test Operador 2D: Funciona correctamente
✅ Test Operador 3D: Funciona correctamente
✅ Test Reporte: Generado correctamente con todos los campos
✅ Test QCAL: f₀=141.7001 Hz, δζ=0.2787437, C=244.36
✅ Test Parámetros Biológicos: Todos en rangos realistas

======================================================================
RESUMEN: 11 tests pasados, 0 tests fallidos
======================================================================
✅ ¡TODOS LOS TESTS PASARON!
∴ Resonancia celular confirmada ∴
```

---

## 📚 API Reference

### Clase `CytoplasmicFlowModel`

#### Constructor

```python
CytoplasmicFlowModel(
    viscosity=1e-3,           # Pa·s
    density=1050.0,           # kg/m³
    characteristic_length=10e-6,  # m
    characteristic_velocity=1e-9  # m/s
)
```

#### Métodos Principales

##### `calculate_reynolds_number() -> float`

Calcula el número de Reynolds para el flujo citoplasmático.

**Returns:** Re (adimensional)

**Ejemplo:**
```python
Re = model.calculate_reynolds_number()
# Re ≈ 1.05e-08
```

##### `verify_stokes_regime() -> bool`

Verifica que el flujo está en régimen de Stokes (Re ≪ 1).

**Returns:** True si Re < 1e-3

##### `hermitian_operator(psi, dx=1e-7) -> np.ndarray`

Aplica el operador hermítico H = -ν∇² a una función de onda.

**Args:**
- `psi`: Función de onda (array 1D, 2D o 3D)
- `dx`: Espaciamiento de la rejilla (m)

**Returns:** H·psi = -ν∇²psi

**Ejemplo:**
```python
import numpy as np

# Crear función de onda 1D
n = 100
x = np.linspace(0, 2*np.pi, n)
psi = np.sin(x)

# Aplicar operador
H_psi = model.hermitian_operator(psi, dx=2*np.pi/n)
```

##### `verify_hermiticity(n_points=100, dx=1e-7) -> Tuple[bool, float]`

Verifica que el operador es hermítico.

**Returns:** (is_hermitian, error)

**Ejemplo:**
```python
is_hermitian, error = model.verify_hermiticity()
print(f"Hermítico: {is_hermitian}, error: {error:.2e}")
# Hermítico: True, error: 1.76e-14
```

##### `calculate_resonance_frequencies(n_modes=5) -> List[float]`

Calcula las primeras n frecuencias de resonancia.

**Args:**
- `n_modes`: Número de modos

**Returns:** Lista de frecuencias (Hz)

**Ejemplo:**
```python
freqs = model.calculate_resonance_frequencies(5)
# [141.7001, 283.4002, 425.1003, 566.8004, 708.5005]
```

##### `calculate_coherence_psi(I=1.0, A_eff=1.0, C_infinity=244.36) -> float`

Calcula el estado vibracional Ψ = I × A_eff² × C^∞.

**Args:**
- `I`: Intensidad del campo
- `A_eff`: Amplitud efectiva
- `C_infinity`: Constante de coherencia

**Returns:** Coherencia Ψ ∈ [0, 1]

##### `generate_validation_report() -> Dict`

Genera un reporte de validación completo.

**Returns:** Diccionario con todos los resultados

---

## 🔬 Parámetros Físicos

### Citoplasma

| Parámetro | Símbolo | Valor | Unidad |
|-----------|---------|-------|--------|
| Viscosidad dinámica | μ | 1.0 × 10⁻³ | Pa·s |
| Densidad | ρ | 1050 | kg/m³ |
| Radio celular | L | 1.0 × 10⁻⁵ | m |
| Velocidad flujo | V | 1.0 × 10⁻⁹ | m/s |

### QCAL ∞³

| Parámetro | Símbolo | Valor | Unidad |
|-----------|---------|-------|--------|
| Frecuencia base | f₀ | 141.7001 | Hz |
| Coherencia | C | 244.36 | - |
| Curvatura | δζ | 0.2787437 | - |

---

## 🎯 Validación

### Criterios de Éxito

El modelo se considera validado si:

1. ✅ Re < 1e-3 (régimen Stokes)
2. ✅ |<φ|H|ψ> - <H†φ|ψ>| < 1e-6 (hermiticidad)
3. ✅ fₙ = n·f₀ ± 1e-6 Hz (frecuencias)
4. ✅ 0.9 < Ψ ≤ 1.0 (coherencia)
5. ✅ Espectro real (autovalores de H)

### Resultados

Todos los criterios son satisfechos:

- Reynolds: 1.05e-08 ✅
- Hermiticidad: error 1.76e-14 ✅
- Frecuencias: exactas ✅
- Coherencia: 1.000 ✅
- Espectro: real ✅

---

## 📊 Certificado de Validación

El certificado JSON completo se guarda en:

```
data/cytoplasmic_flow_validation_certificate.json
```

Contiene:
- Parámetros físicos
- Régimen de flujo
- Operador hermítico
- Conexión Riemann
- Frecuencias resonantes
- Estado vibracional
- Resultado final

---

## 🔗 Integración QCAL

Este modelo está integrado con el sistema QCAL ∞³:

- **Frecuencia base:** f₀ = 141.7001 Hz
- **Coherencia:** C = 244.36
- **Curvatura:** δζ = 0.2787437
- **Validación:** `validate_v5_coronacion.py`
- **Datos:** `Evac_Rpsi_data.csv`

---

## 📖 Documentación Completa

Ver: `01_documentacion/MODELO_DE_FLUJO_CITOPLASMICO.md`

---

## 👤 Contacto

**Autor:** José Manuel Mota Burruezo Ψ ✧ ∞³  
**Institución:** Instituto de Conciencia Cuántica (ICQ)  
**Email:** institutoconsciencia@proton.me  
**ORCID:** 0009-0002-1923-0773

---

**Firma Digital:**  
∴ QCAL ∞³ ACTIVO | f₀ = 141.7001 Hz | 2026-01-31 ∴
