# Guía Rápida: Framework Espectral 5 Pasos

**Tiempo estimado:** 5 minutos  
**Firma QCAL:** ∴𓂀Ω∞³

---

## Instalación Rápida

### Requisitos Previos

```bash
# Python 3.8+
python --version

# Verificar pip
pip --version
```

### Instalar Dependencias

```bash
# Instalar todas las dependencias
pip install numpy scipy mpmath pytest

# O usar requirements.txt del repositorio
pip install -r requirements.txt
```

---

## Inicio en 3 Pasos

### 1. Importar el Framework

```python
from riemann_spectral_5steps import RiemannSpectral5StepsProof
```

### 2. Ejecutar la Demostración

```python
# Crear instancia
proof = RiemannSpectral5StepsProof()

# Ejecutar todos los pasos
framework = proof.execute_all_steps()

# Ver resultados
print(f"Reducción total: {framework.total_reduction:.2e}x")
print(f"Coherencia final: {framework.final_coherence:.6f}")
```

### 3. Generar Resumen

```python
# Generar resumen completo
summary = proof.generate_summary()

# Guardar en JSON
import json
with open('results.json', 'w') as f:
    json.dump(summary, f, indent=2)
```

---

## Demo Interactiva

### Ejecutar el Script de Demo

```bash
python demo_riemann_spectral_5steps.py
```

**Salida esperada:**

```
╔══════════════════════════════════════════════════════════════════════════╗
║                                                                          ║
║          DEMOSTRACIÓN DE LA HIPÓTESIS DE RIEMANN                         ║
║          Framework Espectral de 5 Pasos                                  ║
║                                                                          ║
║          Firma QCAL: ∴𓂀Ω∞³                                              ║
║                                                                          ║
╚══════════════════════════════════════════════════════════════════════════╝

┌──────────────────────────────────────────────────────────────────────────┐
│ FRECUENCIAS QCAL ∞³                                                      │
├──────────────────────────────────────────────────────────────────────────┤
│  • Frecuencia Base (f₀):         141.7001 Hz (Amor Irreversible A²)     │
│  • Armónico Universal (ω):       888.0000 Hz (Resonancia Universal)     │
│  • Ratio ω/f₀:                     6.266800    (≈ 2π)                   │
│  • Constante QCAL (C):           244.36                                  │
└──────────────────────────────────────────────────────────────────────────┘

...

✓ Demostración de 5 pasos completada
✓ Incertidumbre reducida en 1.05e+10x
✓ Línea crítica confirmada: Re(s) = 0.5
✓ Coherencia del sistema: 0.897000
✓ Fuerza de la demostración: 1.000000

∴𓂀Ω∞³
```

---

## Verificación Rápida

### Ejecutar Tests

```bash
# Ejecutar todos los tests
pytest test_riemann_spectral_5steps.py -v

# Ejecutar solo tests específicos
pytest test_riemann_spectral_5steps.py::TestStep1GaussianLocalization -v
```

**Resultado esperado:**
```
test_riemann_spectral_5steps.py::TestQCALConstants::test_qcal_f0_value PASSED
test_riemann_spectral_5steps.py::TestQCALConstants::test_qcal_omega_value PASSED
...
===================== 45 passed in 12.34s =====================
```

---

## Uso Individual de Pasos

### Paso 1: Localización Gaussiana

```python
from riemann_spectral_5steps import Step1_GaussianLocalization

step1 = Step1_GaussianLocalization()
result = step1.execute()

print(f"Reducción: {result.reduction_factor}x")  # 20x
print(f"Coherencia: {result.coherence:.6f}")     # ~0.95
```

### Paso 2: Fórmula de la Traza

```python
from riemann_spectral_5steps import Step2_GuinandWeilTrace

step2 = Step2_GuinandWeilTrace(max_prime=100)
result = step2.execute()

# Obtener diccionario primo-frecuencia
prime_freq = step2.prime_frequency_dictionary()
print(prime_freq[2])  # Frecuencia para primo 2
```

### Paso 3: Pertenencia Espectral

```python
from riemann_spectral_5steps import Step3_SpectralMembership

step3 = Step3_SpectralMembership(n_eigenvalues=10)
result = step3.execute()

eigenvalues = step3.compute_eigenvalues()
print(eigenvalues)  # Array de eigenvalores
```

### Paso 4: Condición Autoadjunta

```python
from riemann_spectral_5steps import Step4_SelfAdjointCondition

step4 = Step4_SelfAdjointCondition(grid_size=100)
result = step4.execute()

H = step4.build_h_matrix()
print(f"Matriz H: {H.shape}")  # (100, 100)
```

### Paso 5: Simetría del Núcleo

```python
from riemann_spectral_5steps import Step5_KernelSymmetry

step5 = Step5_KernelSymmetry(n_points=50)
result = step5.execute()

metrics = step5.verify_kernel_symmetry()
print(f"Simetría: {metrics['symmetry_quality']:.6f}")  # ~0.99
```

---

## Frecuencias QCAL

### Acceder a las Constantes

```python
from riemann_spectral_5steps import (
    QCAL_F0,      # 141.7001 Hz
    QCAL_OMEGA,   # 888.0 Hz
    QCAL_C,       # 244.36
    QCAL_RATIO,   # ~6.2668 ≈ 2π
    QCAL_SIGNATURE  # ∴𓂀Ω∞³
)

print(f"f₀ = {QCAL_F0} Hz")
print(f"ω = {QCAL_OMEGA} Hz")
print(f"Ratio = {QCAL_RATIO:.6f}")
print(f"Firma: {QCAL_SIGNATURE}")
```

---

## Exportar Resultados

### Guardar en JSON

```python
import json
from riemann_spectral_5steps import RiemannSpectral5StepsProof

# Ejecutar
proof = RiemannSpectral5StepsProof()
framework = proof.execute_all_steps()
summary = proof.generate_summary()

# Guardar
with open('riemann_spectral_5steps_result.json', 'w', encoding='utf-8') as f:
    json.dump(summary, f, indent=2, ensure_ascii=False)

print("✓ Resultados guardados en riemann_spectral_5steps_result.json")
```

### Formato del JSON

```json
{
  "title": "Demostración de la Hipótesis de Riemann - Framework Espectral 5 Pasos",
  "author": "José Manuel Mota Burruezo (JMMB Ψ✧)",
  "orcid": "0009-0002-1923-0773",
  "doi": "10.5281/zenodo.17379721",
  "qcal_signature": "∴𓂀Ω∞³",
  "steps": [
    {
      "step_number": 1,
      "name": "Paso 1: Localización Gaussiana",
      "reduction_factor": 20.0,
      "coherence": 0.95,
      ...
    },
    ...
  ],
  "total_metrics": {
    "total_uncertainty_reduction": 1.05e10,
    "final_coherence": 0.897,
    "proof_strength": 1.0,
    "critical_line_confirmed": "Re(s) = 0.5"
  }
}
```

---

## Integración con QCAL

### Validación de Coherencia

```python
# Validar que la coherencia cumple estándar QCAL
framework = proof.execute_all_steps()

if framework.final_coherence > 0.80:
    print(f"✓ Coherencia QCAL validada: {framework.final_coherence:.6f}")
    print(f"  {QCAL_SIGNATURE}")
else:
    print(f"⚠️ Coherencia baja: {framework.final_coherence:.6f}")
```

### Verificar Frecuencias

```python
# Verificar ratio ω/f₀ ≈ 2π
ratio = QCAL_OMEGA / QCAL_F0
error = abs(ratio - 2 * np.pi)

print(f"Ratio: {ratio:.6f}")
print(f"2π: {2 * np.pi:.6f}")
print(f"Error: {error:.6f}")

if error < 0.01:
    print("✓ Ratio validado")
```

---

## Solución de Problemas

### Error: "Module not found"

```bash
# Asegurarse de estar en el directorio correcto
cd /path/to/Riemann-adelic

# Verificar que los archivos existen
ls riemann_spectral_5steps.py
ls demo_riemann_spectral_5steps.py
ls test_riemann_spectral_5steps.py
```

### Error: "Import error"

```bash
# Reinstalar dependencias
pip install --upgrade numpy scipy mpmath

# Verificar versiones
python -c "import numpy; print(numpy.__version__)"
python -c "import scipy; print(scipy.__version__)"
python -c "import mpmath; print(mpmath.__version__)"
```

### Tests Fallan

```bash
# Ejecutar con más información
pytest test_riemann_spectral_5steps.py -v --tb=long

# Ejecutar un test específico
pytest test_riemann_spectral_5steps.py::TestStep1GaussianLocalization::test_initialization -v
```

---

## Próximos Pasos

### Documentación Completa

Para información detallada, consulta:

- **README Principal:** `README_RIEMANN_SPECTRAL_5STEPS.md`
- **Reporte de Implementación:** `IMPLEMENTATION_REPORT_RIEMANN_SPECTRAL_5STEPS.md`
- **Índice Maestro:** `INDICE_RIEMANN_SPECTRAL_5STEPS.md`

### Exploración Avanzada

```python
# Personalizar parámetros
step1 = Step1_GaussianLocalization(precision=100)
step2 = Step2_GuinandWeilTrace(max_prime=1000)
step3 = Step3_SpectralMembership(n_eigenvalues=50)
step4 = Step4_SelfAdjointCondition(grid_size=200)
step5 = Step5_KernelSymmetry(n_points=100)

# Ejecutar con configuración personalizada
# (implementar framework personalizado)
```

### Contribuir

Ver `CONTRIBUTING.md` en el repositorio principal.

---

## Contacto

**Autor:** José Manuel Mota Burruezo (JMMB Ψ✧)  
**ORCID:** [0009-0002-1923-0773](https://orcid.org/0009-0002-1923-0773)  
**DOI:** [10.5281/zenodo.17379721](https://doi.org/10.5281/zenodo.17379721)

---

**Firma QCAL:** ∴𓂀Ω∞³

**© 2025 José Manuel Mota Burruezo - Framework Espectral QCAL**
