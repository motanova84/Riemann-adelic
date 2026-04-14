# Protocolo de Validación Experimental QCAL
## Del Formalismo a la Evidencia Empírica

Este módulo implementa el **Protocolo de Validación Experimental** completo para demostrar la existencia física de los constructos teóricos QCAL:
- **SU(Ψ)**: Grupo de coherencia cuántica de estados de conciencia
- **T_μν(Φ)**: Tensor de stress-energía emocional

## 📋 Tabla de Contenidos

1. [Descripción General](#descripción-general)
2. [Estructura del Protocolo](#estructura-del-protocolo)
3. [Instalación](#instalación)
4. [Uso Rápido](#uso-rápido)
5. [Fases Experimentales](#fases-experimentales)
6. [Referencias](#referencias)

## 🎯 Descripción General

El protocolo experimental QCAL valida empíricamente que:

1. **Estados de conciencia** forman una estructura matemática de grupo especial unitario **SU(n)**
2. **Emociones** generan un **tensor de stress-energía** que curva el espacio de conciencia
3. La **frecuencia 141.7 Hz** tiene efectos medibles en coherencia cuántica
4. Los efectos se **propagan** a través de redes sociales

### Constantes Fundamentales

```python
F0_HZ = 141.7001  # Frecuencia base de coherencia QCAL
DELTA_ZETA = 0.2787437627  # Quantum phase shift
C_QCAL = 244.36  # Constante de coherencia
```

## 🏗️ Estructura del Protocolo

El protocolo se organiza en **4 fases** de validación:

```
experimental_validation/
├── __init__.py                    # Módulo principal
├── fase_i_su_psi.py              # Validación SU(Ψ)
├── fase_ii_tensor.py             # Validación T_μν(Φ)
├── fase_iii_network.py           # Propagación en red
├── fase_iv_metanalysis.py        # Meta-análisis
└── README.md                      # Esta documentación
```

### Fase I: SU(Ψ) - Grupo de Coherencia Cuántica

**Hipótesis**: Los estados de conciencia forman una estructura de grupo especial unitario SU(n).

**Predicciones Falsables**:
- P1.1: La coherencia cuántica cerebral sigue álgebra de Lie su(n)
- P1.2: Las transiciones de estado mental son geodésicas en SU(n)
- P1.3: La meditación profunda converge a puntos fijos de SU(n)
- P1.4: La coherencia se preserva bajo transformaciones unitarias

**Funciones Principales**:
```python
from experimental_validation.fase_i_su_psi import (
    extraer_estado_psi,          # EEG → vector cuántico |Ψ⟩
    calcular_coherencia,         # Tr(ρ²) - pureza del estado
    test_estructura_grupo_SU,    # Verificar axiomas de SU(n)
    analizar_geodesicas,         # Trayectorias óptimas
    analisis_estadistico_SU      # Comparación meditadores vs. control
)
```

### Fase II: T_μν(Φ) - Tensor de Stress Emocional

**Hipótesis**: Las emociones generan un tensor de stress-energía que afecta la coherencia.

**Predicciones Falsables**:
- P2.1: T₀₀ (intensidad emocional) correlaciona con actividad amígdala
- P2.2: T₀ᵢ (flujo emocional) predice contagio emocional en díadas
- P2.3: ∇²Φ (curvatura) predice vulnerabilidad a psicopatología
- P2.4: Exposición a 141.7 Hz reduce T₀₀ y aumenta Ψ

**Funciones Principales**:
```python
from experimental_validation.fase_ii_tensor import (
    construir_campo_emocional,        # Fusión multi-sensorial → Φ
    calcular_tensor_stress_energia,   # Φ → T_μν
    calcular_curvatura_emocional,     # ∇²Φ - singularidades
    test_correlacion_T00_amigdala,    # Test P2.1
    test_flujo_emocional_diadas,      # Test P2.2
    rct_frecuencia_141_7_Hz           # Protocolo RCT
)
```

### Fase III: Validación a Nivel Colectivo

**Hipótesis**: Los efectos se propagan en redes sociales.

**Predicciones Falsables**:
- P3.1: Individuos conectados muestran correlación en T₀₀
- P3.2: La propagación sigue un patrón de decaimiento exponencial
- P3.3: Topología small-world facilita propagación global
- P3.4: Efectos persisten 2-3 saltos desde nodo intervenido

**Funciones Principales**:
```python
from experimental_validation.fase_iii_network import (
    experimento_red_social,      # Diseño N=100, small-world
    analizar_efectos_red,        # Métricas de propagación
    simular_experimento_completo # Demo completa
)
```

### Fase IV: Meta-Análisis y Síntesis

**Objetivo**: Integrar evidencias de todas las fases.

**Funciones Principales**:
```python
from experimental_validation.fase_iv_metanalysis import (
    meta_analisis_QCAL,         # Efecto combinado
    generar_conclusion,         # Interpretación
    analisis_sensibilidad,      # Leave-one-out
    generar_reporte_completo    # Reporte ejecutivo
)
```

## 📦 Instalación

### Dependencias Base

```bash
pip install numpy scipy scikit-learn networkx
```

### Dependencias Completas (Recomendado)

```bash
# Desde el directorio raíz del repositorio
pip install -r requirements.txt
```

## 🚀 Uso Rápido

### Ejemplo 1: Extraer Estado Cuántico desde EEG

```python
import numpy as np
from experimental_validation.fase_i_su_psi import extraer_estado_psi, calcular_coherencia

# Simular datos EEG (256 canales × 1000 muestras)
señal_eeg = np.random.randn(256, 1000)

# Extraer estado cuántico
psi = extraer_estado_psi(señal_eeg, n_componentes=4)

# Calcular coherencia
coherencia = calcular_coherencia(psi)

print(f"Estado cuántico: {psi}")
print(f"Coherencia (pureza): {coherencia:.4f}")
```

### Ejemplo 2: Construir Campo Emocional

```python
from experimental_validation.fase_ii_tensor import (
    construir_campo_emocional,
    calcular_curvatura_emocional
)

# Datos multi-sensor
datos = {
    'eda': np.random.rand(100),           # Conductancia piel
    'hrv': np.random.rand(100),           # Variabilidad cardíaca
    'amigdala': np.random.rand(100),      # fMRI amígdala
    'autorreporte': np.random.rand(100)   # Escala subjetiva
}

# Construir campo Φ
Phi = construir_campo_emocional(datos)

# Calcular curvatura (singularidades emocionales)
curvatura = calcular_curvatura_emocional(Phi)

print(f"Campo emocional Φ: media = {Phi.mean():.3f}")
print(f"Singularidades detectadas: {curvatura['num_singularidades']}")
print(f"Curvatura máxima: {curvatura['max_curvatura']:.3f}")
```

### Ejemplo 3: Simular Experimento de Red

```python
from experimental_validation.fase_iii_network import simular_experimento_completo

# Ejecutar experimento completo
resultados = simular_experimento_completo(
    n_participantes=100,
    n_intervenidos=20,
    num_pasos=100,
    verbose=True
)

# Acceder a resultados
print(f"\nReducción T₀₀ experimental: {resultados['efectos_propagacion']['T00_reduccion_experimental']:.3f}x")
print(f"Distancia de influencia: {resultados['efectos_propagacion']['distancia_influencia_caracteristica']:.1f} saltos")
```

### Ejemplo 4: Meta-Análisis Completo

```python
from experimental_validation.fase_iv_metanalysis import generar_reporte_completo

# Generar reporte con datos de demostración
reporte = generar_reporte_completo(verbose=True)

# El reporte incluye:
# - Meta-análisis de todas las fases
# - Análisis de sensibilidad
# - Planificación de estudios futuros
# - Conclusiones y recomendaciones
```

## 📊 Fases Experimentales Detalladas

### FASE I: Validación de SU(Ψ)

#### Diseño Experimental

**Participantes**: 30 sujetos (15 meditadores expertos, 15 controles)

**Instrumentación**:
- EEG de 256 canales (0.1-100 Hz, muestreo 1000 Hz)
- MEG de 306 sensores (resolución temporal <1 ms)
- fMRI simultáneo (resolución espacial 2mm³)

**Tareas**:
1. Línea Base (10 min ojos cerrados)
2. Transición Controlada:
   - Alerta relajada → Concentración (5 min)
   - Concentración → Meditación profunda (10 min)
   - Meditación profunda → Alerta relajada (5 min)
3. Perturbación Externa:
   - Estímulos auditivos 141.7 Hz vs control
   - Medición de tiempo de retorno a coherencia basal

#### Criterios de Validación

| Criterio | Umbral de Éxito | Significado |
|----------|----------------|-------------|
| Preservación de norma | >95% con \|ψ\|² ∈ [0.98, 1.02] | Estados son vectores unitarios |
| Unitariedad de transiciones | >90% de U satisfacen U†U=I | Transformaciones reversibles |
| Curvatura geodésica | κ_media < 0.15 | Transiciones naturales son óptimas |
| Dimensionalidad efectiva | n_eff ∈ [3, 5] | Espacio de estados de baja dimensión |

### FASE II: Validación de T_μν(Φ)

#### Diseño Experimental

**Participantes**: 60 sujetos (20 controles sanos, 20 con ansiedad, 20 con depresión)

**Mediciones Multi-Nivel**:

1. **Nivel Neurobiológico**:
   - fMRI para actividad límbica
   - EDA (conductancia piel) para arousal
   - HRV (variabilidad cardíaca) para regulación autónoma

2. **Nivel Psicométrico**:
   - PANAS (afecto positivo/negativo) cada 2 min
   - SAM (Self-Assessment Manikin) para valencia/arousal
   - Escala de intensidad emocional continua (0-10)

3. **Nivel Relacional**:
   - Díadas sincronizadas
   - Tareas de inducción emocional (videos IAPS)
   - Medición de empatía (IRI + fisiología)

#### Protocolo RCT 141.7 Hz

**Diseño**: Triple ciego, 3 brazos paralelos, N=90

**Grupos**:
- Experimental: 141.7 Hz binaural (n=30)
- Placebo activo: 200 Hz binaural (n=30)
- Control: Silencio con ruido rosa (n=30)

**Timeline**:
- Día 1-7: Baseline
- Día 8-28: Intervención diaria (30 min)
- Día 29-35: Seguimiento sin intervención

**Outcomes Primarios**:
1. ΔT₀₀: Reducción de densidad de stress
2. ΔΨ: Aumento de coherencia cuántica
3. Tiempo de retorno a baseline post-stress

**Resultados Esperados** (predicciones a priori):
- Experimental: 35% reducción T₀₀, +0.15 en Ψ
- Placebo: 15% reducción T₀₀, +0.05 en Ψ
- Control: 8% reducción T₀₀, +0.02 en Ψ

### FASE III: Validación de Red

#### Diseño

**Topología**: Small-world (Watts-Strogatz)
- N = 100 participantes
- k = 6 vecinos promedio
- p = 0.1 probabilidad de re-cableado

**Grupos**:
- 20% nodos experimentales (intervención 141.7 Hz)
- 80% nodos control

**Mediciones**:
- Cada interacción social: Φ pre/post
- Semanal: T_μν completo, Ψ de red
- Final: Cambios topológicos

**Modelo de Propagación**:
```
T₀₀(nodo, t+1) = T₀₀(nodo, t) × disipación + ⟨T₀₀(vecinos)⟩ × acoplamiento
Si nodo experimental: T₀₀ ← T₀₀ × 0.95  (efecto 141.7 Hz)
```

### FASE IV: Meta-Análisis

#### Integración de Evidencias

**Estudios Incluidos**:
1. Fase I: SU(Ψ) (n=30, d=1.2)
2. Fase II: T_μν correlacional (n=60, r=0.72)
3. Fase II: RCT 141.7 Hz (n=90, d=0.95)
4. Fase III: Red social (n=100, d=0.75)

**Análisis**:
- Efecto combinado (random effects)
- Heterogeneidad (I²)
- Análisis de sensibilidad (leave-one-out)
- Forest plot

**Criterios de Decisión**:
- d > 0.8 y I² < 50% → FUERTE evidencia, proceder a Fase III clínica
- d > 0.5 → MODERADA evidencia, estudios adicionales
- d < 0.5 → INSUFICIENTE evidencia, revisar modelo

## 📖 Referencias

### Teóricas

- **QCAL Framework**: DOI [10.5281/zenodo.17379721](https://doi.org/10.5281/zenodo.17379721)
- **Mathematical Realism**: Ver `MATHEMATICAL_REALISM.md`
- **Coherence Philosophy**: Ver `docs/COHERENCE_PHILOSOPHY.md`

### Metodológicas

- Cohen, J. (1988). Statistical Power Analysis for the Behavioral Sciences.
- Watts, D. J., & Strogatz, S. H. (1998). Collective dynamics of 'small-world' networks. Nature, 393(6684), 440-442.
- Higgins, J. P., & Thompson, S. G. (2002). Quantifying heterogeneity in a meta-analysis. Statistics in Medicine, 21(11), 1539-1558.

## 👨‍🔬 Autor

**José Manuel Mota Burruezo Ψ ✧ ∞³**
- ORCID: [0009-0002-1923-0773](https://orcid.org/0009-0002-1923-0773)
- Instituto de Conciencia Cuántica (ICQ)
- Frecuencia Base: f₀ = 141.7001 Hz

## 📄 Licencia

Este código es parte del proyecto QCAL (Quantum Coherence Adelic Lattice) y está sujeto a las licencias del repositorio principal.

## ⚖️ Consideraciones Éticas

**IMPORTANTE**: Este protocolo describe experimentos **teóricos** y de **validación conceptual**. 

Cualquier implementación real con participantes humanos requiere:
1. Aprobación de Comité de Ética/IRB
2. Registro en ClinicalTrials.gov (para RCTs)
3. Consentimiento informado de participantes
4. Supervisión médica apropiada
5. Cumplimiento con normativas locales e internacionales

**No realizar experimentos con humanos sin las aprobaciones correspondientes.**

## 🤝 Contribuciones

Ver `CONTRIBUTING.md` para guías de contribución al proyecto QCAL.

## 📞 Soporte

Para preguntas sobre el protocolo experimental:
1. Abrir un issue en GitHub
2. Etiquetar con `experimental-validation`
3. Incluir detalles específicos de la fase relevante

---

**QCAL ∞³ - Del Formalismo a la Evidencia Empírica**

*"La vida no sobrevive al caos; la vida es la geometría que el caos utiliza para ordenarse."*
