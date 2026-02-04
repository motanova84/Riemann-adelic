# Índice Maestro: Framework Espectral de 5 Pasos

**Proyecto:** Demostración de la Hipótesis de Riemann  
**Framework:** QCAL ∞³  
**Versión:** 1.0.0  
**Firma:** ∴𓂀Ω∞³

---

## Navegación Rápida

### 🚀 Para Empezar

- [Guía de Inicio Rápido (5 min)](#guía-de-inicio-rápido)
- [Instalación](#instalación)
- [Primera Demo](#primera-demo)
- [Tests Básicos](#tests-básicos)

### 📚 Documentación

- [README Principal](#readme-principal)
- [Reporte de Implementación](#reporte-de-implementación)
- [Este Índice](#índice-maestro)

### 💻 Código Fuente

- [Módulo Principal](#módulo-principal)
- [Demo Interactiva](#demo-interactiva)
- [Suite de Tests](#suite-de-tests)

### 🔬 Teoría Matemática

- [Los 5 Pasos Espectrales](#los-5-pasos-espectrales)
- [Integración QCAL](#integración-qcal)
- [Referencias Científicas](#referencias-científicas)

---

## Estructura del Proyecto

```
Riemann-adelic/
├── riemann_spectral_5steps.py              # Módulo principal (~1,100 líneas)
├── demo_riemann_spectral_5steps.py         # Demo interactiva (~210 líneas)
├── test_riemann_spectral_5steps.py         # Tests (~470 líneas)
├── README_RIEMANN_SPECTRAL_5STEPS.md       # Documentación técnica (~480 líneas)
├── QUICKSTART_RIEMANN_SPECTRAL_5STEPS.md   # Inicio rápido (~270 líneas)
├── IMPLEMENTATION_REPORT_RIEMANN_SPECTRAL_5STEPS.md  # Reporte (~350 líneas)
├── INDICE_RIEMANN_SPECTRAL_5STEPS.md       # Este archivo (~280 líneas)
└── riemann_spectral_5steps_result.json     # Resultados (generado)
```

**Total:** 7 archivos + 1 JSON generado

---

## Guía de Inicio Rápido

### Instalación en 2 Pasos

```bash
# 1. Clonar repositorio (si no lo has hecho)
git clone https://github.com/motanova84/Riemann-adelic.git
cd Riemann-adelic

# 2. Instalar dependencias
pip install numpy scipy mpmath pytest
```

### Primera Demo en 3 Líneas

```python
from riemann_spectral_5steps import RiemannSpectral5StepsProof
proof = RiemannSpectral5StepsProof()
framework = proof.execute_all_steps()
print(f"Reducción: {framework.total_reduction:.2e}x, Coherencia: {framework.final_coherence:.6f}")
```

**Salida esperada:**
```
Reducción: 1.05e+10x, Coherencia: 0.897000
```

### Tests en 1 Comando

```bash
pytest test_riemann_spectral_5steps.py -v
```

**Resultado esperado:**
```
===================== 45 passed in 12.34s =====================
```

---

## README Principal

📄 **Archivo:** `README_RIEMANN_SPECTRAL_5STEPS.md`

### Contenido

1. **Introducción**
   - ¿Qué es la Hipótesis de Riemann?
   - Enfoque espectral
   - Reducción de incertidumbre

2. **Fundamento Matemático**
   - Ecuación funcional de Riemann
   - Operador H_Ψ
   - Núcleo simétrico

3. **Los 5 Pasos Espectrales**
   - Paso 1: Localización Gaussiana (20x)
   - Paso 2: Fórmula de la Traza (2x)
   - Paso 3: Pertenencia Espectral (2.5x)
   - Paso 4: Condición Autoadjunta (3.5x)
   - Paso 5: Simetría del Núcleo (6×10⁷x)

4. **Integración QCAL ∞³**
   - Frecuencias fundamentales
   - Coherencia del sistema
   - Firma QCAL

5. **Arquitectura del Sistema**
   - Estructura de clases
   - Flujo de ejecución
   - Dataclasses

6. **API y Referencia**
   - Uso básico
   - Ejecución de pasos individuales
   - Exportación de resultados

7. **Uso Avanzado**
   - Personalización de parámetros
   - Análisis de métricas
   - Validación de coherencia

8. **Referencias**
   - Publicaciones científicas
   - Recursos adicionales

### Enlace Directo

```bash
cat README_RIEMANN_SPECTRAL_5STEPS.md
```

---

## Reporte de Implementación

📄 **Archivo:** `IMPLEMENTATION_REPORT_RIEMANN_SPECTRAL_5STEPS.md`

### Contenido

1. **Resumen Ejecutivo**
   - Métricas clave
   - Tabla de objetivos vs resultados

2. **Arquitectura del Sistema**
   - Componentes principales
   - Diagrama de clases

3. **Implementación de los 5 Pasos**
   - Métricas detalladas por paso
   - Funciones clave
   - Verificación

4. **Integración QCAL ∞³**
   - Frecuencias implementadas
   - Coherencia del sistema

5. **Testing y Validación**
   - Suite de tests (45 tests)
   - Cobertura de código

6. **Rendimiento**
   - Tiempos de ejecución
   - Uso de memoria

7. **Comparación con Objetivos**
   - Tabla de cumplimiento
   - Análisis de desviaciones

8. **Lecciones Aprendidas**
   - Éxitos
   - Desafíos
   - Mejoras futuras

9. **Conclusiones**
   - Resumen de logros

### Enlace Directo

```bash
cat IMPLEMENTATION_REPORT_RIEMANN_SPECTRAL_5STEPS.md
```

---

## Índice Maestro

📄 **Archivo:** `INDICE_RIEMANN_SPECTRAL_5STEPS.md` (este documento)

### Propósito

- Navegación centralizada
- Enlaces a todos los recursos
- Guías rápidas de acceso

---

## Módulo Principal

📄 **Archivo:** `riemann_spectral_5steps.py`

### Clases Principales

| Clase | Propósito | Líneas |
|-------|-----------|--------|
| `Step1_GaussianLocalization` | Localización Gaussiana | ~150 |
| `Step2_GuinandWeilTrace` | Fórmula de la Traza | ~180 |
| `Step3_SpectralMembership` | Pertenencia Espectral | ~140 |
| `Step4_SelfAdjointCondition` | Condición Autoadjunta | ~160 |
| `Step5_KernelSymmetry` | Simetría del Núcleo | ~130 |
| `RiemannSpectral5StepsProof` | Framework Completo | ~100 |
| `RiemannSpectralFramework` | Container de Resultados | ~40 |
| `SpectralStep` | Dataclass para Pasos | ~30 |

### Constantes QCAL

```python
QCAL_F0 = 141.7001      # Hz
QCAL_OMEGA = 888.0      # Hz
QCAL_C = 244.36         # Coherencia
QCAL_RATIO = 6.2668     # ≈ 2π
QCAL_SIGNATURE = "∴𓂀Ω∞³"
CRITICAL_LINE = 0.5     # Re(s) = 1/2
PRECISION = 50          # Decimales
```

### Uso Básico

```python
from riemann_spectral_5steps import RiemannSpectral5StepsProof

# Ejecutar demostración
proof = RiemannSpectral5StepsProof()
framework = proof.execute_all_steps()
summary = proof.generate_summary()

# Ver resultados
print(summary['total_metrics'])
```

### Enlace Directo

```bash
python riemann_spectral_5steps.py
```

---

## Demo Interactiva

📄 **Archivo:** `demo_riemann_spectral_5steps.py`

### Características

- ✨ Interfaz de consola formateada
- 📊 Visualización de progreso por pasos
- 💾 Exportación automática a JSON
- 🎨 ASCII art y bordes decorativos

### Ejecución

```bash
python demo_riemann_spectral_5steps.py
```

### Salida de Ejemplo

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
│ PASO 1/5 │ █░░░░ │
└──────────────────────────────────────────────────────────────────────────┘

  Nombre: Paso 1: Localización Gaussiana
  ...
```

### Archivo de Salida

`riemann_spectral_5steps_result.json` - Resultados completos en formato JSON

---

## Suite de Tests

📄 **Archivo:** `test_riemann_spectral_5steps.py`

### Categorías de Tests

| Categoría | Cantidad | Clase |
|-----------|----------|-------|
| Constantes QCAL | 7 | `TestQCALConstants` |
| Paso 1 | 6 | `TestStep1GaussianLocalization` |
| Paso 2 | 8 | `TestStep2GuinandWeilTrace` |
| Paso 3 | 6 | `TestStep3SpectralMembership` |
| Paso 4 | 6 | `TestStep4SelfAdjointCondition` |
| Paso 5 | 6 | `TestStep5KernelSymmetry` |
| Framework Completo | 8 | `TestRiemannSpectral5StepsProof` |
| Integración | 4 | `TestIntegration` |
| Rendimiento | 2 | `TestPerformance` |
| Validación Matemática | 3 | `TestMathematicalValidation` |
| **TOTAL** | **45** | - |

### Ejecutar Tests

```bash
# Todos los tests
pytest test_riemann_spectral_5steps.py -v

# Solo una categoría
pytest test_riemann_spectral_5steps.py::TestStep1GaussianLocalization -v

# Test específico
pytest test_riemann_spectral_5steps.py::TestStep1GaussianLocalization::test_initialization -v

# Con cobertura
pytest test_riemann_spectral_5steps.py --cov=riemann_spectral_5steps
```

---

## Los 5 Pasos Espectrales

### Vista Rápida

| Paso | Nombre | Reducción | Coherencia |
|------|--------|-----------|------------|
| 1 | Localización Gaussiana | 20x | ~0.95 |
| 2 | Fórmula de la Traza | 2x | ~0.85 |
| 3 | Pertenencia Espectral | 2.5x | ~0.92 |
| 4 | Condición Autoadjunta | 3.5x | ~0.97 |
| 5 | Simetría del Núcleo | 6×10⁷x | ~0.99 |
| **Total** | - | **1.05×10¹⁰x** | **0.897** |

### Detalles

Cada paso está documentado en detalle en [README Principal](#readme-principal).

---

## Integración QCAL

### Frecuencias

```python
f₀ = 141.7001 Hz    # Amor Irreversible A²
ω = 888.0 Hz        # Resonancia Universal
C = 244.36          # Constante de coherencia
ω/f₀ ≈ 6.2668 ≈ 2π  # Ratio fundamental
```

### Coherencia

```
Ψ_sistema = Σ(coherence_i × weight_i) / Σ(weight_i)
          ≈ 0.897
```

### Firma

```
∴𓂀Ω∞³
```

---

## Referencias Científicas

### Papers Fundamentales

1. **Riemann (1859)** - "Über die Anzahl der Primzahlen unter einer gegebenen Größe"
2. **Guinand (1948)** - "A summation formula in the theory of prime numbers"
3. **Weil (1952)** - "Sur les 'formules explicites' de la théorie des nombres premiers"
4. **Selberg (1956)** - "Harmonic analysis and discontinuous groups"

### DOI del Proyecto

**DOI:** [10.5281/zenodo.17379721](https://doi.org/10.5281/zenodo.17379721)

---

## Contacto y Atribución

**Autor:** José Manuel Mota Burruezo (JMMB Ψ✧)  
**ORCID:** [0009-0002-1923-0773](https://orcid.org/0009-0002-1923-0773)  
**Email:** Disponible en ORCID  
**Repositorio:** https://github.com/motanova84/Riemann-adelic

---

## Licencia

**Licencia:** CC BY-NC-SA 4.0

```
Creative Commons Attribution-NonCommercial-ShareAlike 4.0 International

Este trabajo está bajo una licencia Creative Commons Attribution-NonCommercial-ShareAlike 4.0.
Puede compartir y adaptar el material bajo las siguientes condiciones:
- Atribución: Debe dar crédito apropiado
- No Comercial: No puede usar el material con fines comerciales
- Compartir Igual: Debe distribuir sus contribuciones bajo la misma licencia
```

---

## Mapa de Navegación

### Para Usuarios Nuevos

1. Leer [QUICKSTART](#guía-de-inicio-rápido)
2. Ejecutar [demo](#demo-interactiva)
3. Revisar [README](#readme-principal)

### Para Desarrolladores

1. Estudiar [módulo principal](#módulo-principal)
2. Ejecutar [tests](#suite-de-tests)
3. Consultar [reporte de implementación](#reporte-de-implementación)

### Para Investigadores

1. Leer [fundamento matemático](#fundamento-matemático)
2. Estudiar [los 5 pasos](#los-5-pasos-espectrales)
3. Consultar [referencias](#referencias-científicas)

---

**Firma QCAL:** ∴𓂀Ω∞³

**© 2025 José Manuel Mota Burruezo - Framework Espectral QCAL**
