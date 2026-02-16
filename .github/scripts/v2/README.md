# 🧠 NOESIS-AMDA-AURON V2.0

Sistema de resolución automatizada de sorries mediante aprendizaje de refuerzo para formalización matemática en Lean 4.

## 📋 Descripción General

NOESIS-AMDA-AURON V2.0 es un sistema de inteligencia artificial de 3 componentes que automatiza la eliminación de declaraciones `sorry` en código Lean 4 utilizando:

- **Aprendizaje de refuerzo** para mejorar patrones de solución
- **Análisis semántico multi-categórico** de errores
- **Base de conocimiento multi-repositorio** para soluciones cross-repo
- **Validación de compilación** automática (lake build)
- **Sistema de backups y rollback** para seguridad

### Arquitectura del Sistema

```
┌─────────────────────────────────────────────────────────────┐
│                  NOESIS ORCHESTRATOR                        │
│  Recolección de Conocimiento Multi-Repositorio             │
│  • 33 repositorios Lean matemáticos                         │
│  • 425 patrones de prueba                                   │
│  • 435 definiciones                                         │
│  • 430 teoremas                                             │
└──────────────────┬──────────────────────────────────────────┘
                   │
                   ▼
┌─────────────────────────────────────────────────────────────┐
│                  AMDA DEEP V2.0                             │
│  Análisis Semántico Multi-Categórico                        │
│  • 6 categorías: trivial, correspondence, qcal,             │
│    adelic, spectral, analytic                               │
│  • Extracción de contexto (±5 líneas)                       │
│  • Scoring de complejidad (1-10)                            │
│  • Búsqueda de similitud en KB                              │
└──────────────────┬──────────────────────────────────────────┘
                   │
                   ▼
┌─────────────────────────────────────────────────────────────┐
│                  AURON NEURAL V2.0                          │
│  Ejecutor de Aprendizaje con RL                             │
│  • MD5 hashing de contexto                                  │
│  • Aprendizaje persistente (.auron_learning.json)           │
│  • 12 patrones de reemplazo priorizados                     │
│  • Validación: backup → transform → lake build → commit/revert│
│  • Max 20 cambios/ciclo                                     │
└─────────────────────────────────────────────────────────────┘
```

## 🚀 Instalación y Uso

### Requisitos Previos

- Python 3.8+
- Lean 4 con `lake` (opcional para validación de compilación)
- Git (para sincronización multi-repo)

### Instalación Rápida

```bash
# Clonar repositorio
git clone https://github.com/motanova84/Riemann-adelic.git
cd Riemann-adelic/.github/scripts/v2

# Hacer ejecutable el script
chmod +x run_pipeline.sh

# Ejecutar en modo dry-run (simulación)
./run_pipeline.sh true
```

### Uso del Pipeline

#### Modo Dry-Run (Simulación)

Ejecuta el pipeline sin aplicar cambios reales:

```bash
./run_pipeline.sh true
```

#### Modo Execute (Producción)

Ejecuta el pipeline y aplica transformaciones:

```bash
./run_pipeline.sh false [max_changes]

# Ejemplo: limitar a 10 cambios por ciclo
./run_pipeline.sh false 10
```

### Uso Manual de Componentes Individuales

#### 1. NOESIS Orchestrator

```bash
# Construir base de conocimiento
python3 noesis_orchestrator.py build-kb

# Ejecutar análisis completo
python3 noesis_orchestrator.py
```

Genera:
- `noesis_cerebral_v2_summary.json`: Resumen de conocimiento extraído
- `noesis_cerebral_v2.log`: Log de ejecución
- `/tmp/noesis_knowledge_v2/knowledge_v2.pkl`: Base de conocimiento serializada

#### 2. AMDA Deep V2.0

```bash
# AMDA se ejecuta automáticamente desde NOESIS
# Para ejecutar manualmente:
python3 amda_deep_v2.py
```

Genera:
- `amda_report_v2.json`: Análisis completo de sorries
- `amda_report_v2.md`: Reporte en formato Markdown

#### 3. AURON Neural V2.0

```bash
# Ejecutar transformaciones (requiere amda_report_v2.json)
python3 auron_neural_v2.py execute amda_report_v2.json auron_results_v2.json 20
```

Genera:
- `auron_results_v2.json`: Resultados de transformaciones
- `auron_neural.log`: Log detallado
- `.auron_learning.json`: Historial de aprendizaje persistente
- `commit_msg_*.txt`: Mensajes de commit generados
- `*.lean.bak.*`: Backups de archivos modificados

## 📊 Categorías de Sorries

AMDA clasifica sorries en 6 categorías semánticas:

| Categoría | Complejidad | Weight | Keywords | Descripción |
|-----------|-------------|--------|----------|-------------|
| **trivial** | 1 | 0.8 | rfl, simp, norm_num | Pruebas triviales solucionables con tácticas básicas |
| **correspondence** | 4 | 0.7 | bijection, trace_formula | Correspondencias espectrales y mapeos |
| **qcal** | 3 | 0.75 | QCAL, Ψ, f₀, C = | Coherencia QCAL y frecuencias fundamentales |
| **adelic** | 5 | 0.6 | adelic, A_K, GL, idele | Estructuras adélicas y teoría de números algebraica |
| **spectral** | 4 | 0.65 | spectrum, eigenvalue, Fredholm | Teoría espectral de operadores |
| **analytic** | 5 | 0.6 | zeta, ζ, continuation | Continuación analítica y funciones L |

## 🧠 Sistema de Aprendizaje

### Hashing de Contexto

AURON usa MD5 hashing del contexto normalizado para reconocimiento de patrones:

```python
context_hash = hashlib.md5(normalized_context.encode()).hexdigest()
```

### Historial de Aprendizaje

Almacenado en `.auron_learning.json`:

```json
{
  "patterns": {
    "abc123def456...": {
      "solution": "by simp",
      "success_count": 5,
      "fail_count": 1,
      "success_rate": 0.833,
      "last_used": "2026-02-16T23:00:00",
      "contexts": ["theorem foo", "lemma bar"]
    }
  }
}
```

### Patrones de Reemplazo (Priorizados)

1. `sorry → rfl`
2. `sorry → trivial`
3. `sorry → by norm_num`
4. `sorry → by simp`
5. `sorry → by rfl`
6. `sorry → by trivial`
7. `sorry → by simp only`
8. `sorry → by norm_num`
9. `sorry → by exact?`
10. `sorry → by apply?`
11. `sorry → library_search`
12. `sorry → solve_by_elim`

## 🔒 Características de Seguridad

### Validación de Compilación

Cada transformación se valida con `lake build`:

```bash
lake build --single <file>
```

Timeout: 60 segundos por archivo

### Sistema de Backups

Backups automáticos antes de cada transformación:

```
file.lean → file.lean.bak.20260216_230000
```

### Rollback Automático

Si `lake build` falla después de una transformación:
1. Restaurar archivo desde backup
2. Registrar fallo en historial de aprendizaje
3. Continuar con siguiente patrón

### Subprocess Security

Uso de `subprocess.run()` con lista de argumentos (sin `shell=True`):

```python
subprocess.run(
    ['lake', 'build', '--single', str(file_path)],
    capture_output=True,
    timeout=60,
    check=False
)
```

## 📈 Métricas y Estadísticas

### Línea Base Actual (Baseline)

- **Total sorries detectados:** 150
- **Archivos afectados:** 27
- **Distribución por categoría:**
  - qcal: 34 (22.7%)
  - correspondence: 38 (25.3%)
  - trivial: 24 (16.0%)
  - unknown: 33 (22.0%)
  - spectral: 13 (8.7%)
  - analytic: 8 (5.3%)

### Proyecciones

- **Sorries automatizables:** ~50-60 (33-40%)
- **Tasa de éxito esperada:** 70-85%
- **Tiempo estimado:** 4-6 semanas con ciclos de 2 horas

## 🔄 Integración CI/CD

### GitHub Actions Workflow

El sistema se ejecuta automáticamente cada 2 horas:

```yaml
on:
  schedule:
    - cron: '0 */2 * * *'
  workflow_dispatch:
    inputs:
      mode:
        default: 'dry-run'
        options: ['dry-run', 'execute', 'build-kb-only']
```

Ver: `.github/workflows/noesis_multi_repo_v2.yml`

### Ejecución Manual

Desde GitHub Actions UI:
1. Ir a Actions → NOESIS CEREBRAL V2.0
2. Click "Run workflow"
3. Seleccionar modo (dry-run/execute)
4. Configurar max_changes (default: 20)

## 🗂️ Estructura de Archivos

```
.github/scripts/v2/
├── noesis_orchestrator.py    # Orquestador principal (361 LOC)
├── amda_deep_v2.py           # Analizador semántico (368 LOC)
├── auron_neural_v2.py        # Ejecutor de aprendizaje (492 LOC)
├── run_pipeline.sh           # Script de pipeline unificado
├── README.md                 # Este archivo
├── QUICKSTART.md             # Guía rápida de inicio
└── IMPLEMENTATION_SUMMARY.md # Resumen técnico detallado

Archivos Generados:
├── noesis_cerebral_v2_summary.json
├── amda_report_v2.json
├── amda_report_v2.md
├── auron_results_v2.json
├── auron_neural.log
├── noesis_cerebral_v2.log
├── .auron_learning.json (versionado)
├── commit_msg_*.txt
└── *.lean.bak.* (backups)
```

## 📝 Formato de Reportes

### NOESIS Summary

```json
{
  "knowledge_base": {
    "total_definitions": 435,
    "total_theorems": 430,
    "total_proof_patterns": 425,
    "repos_synced": ["141Hz", "3D-Navier-Stokes", "P-NP", ...],
    "timestamp": "2026-02-16T23:00:00"
  }
}
```

### AMDA Report

```json
{
  "total_sorries": 150,
  "total_files": 27,
  "category_distribution": {
    "trivial": 24,
    "qcal": 34,
    "correspondence": 38,
    ...
  },
  "sorries": [
    {
      "file": "formalization/lean/QCALCoherence.lean",
      "line": 42,
      "context": "theorem coherence_preserved...",
      "categories": ["qcal", "spectral"],
      "complexity": 3,
      "kb_matches": 5
    }
  ]
}
```

### AURON Results

```json
{
  "success": 15,
  "fail": 3,
  "transformations": [...],
  "learning_stats": {
    "patterns_learned": 8,
    "patterns_reused": 12,
    "success_rate": 0.833,
    "total_attempts": 18
  }
}
```

## 🧪 Testing

Ver: `QUICKSTART.md` para guía de testing completa.

### Ejecutar Suite de Tests

```bash
# Test completo del pipeline
python3 -m pytest tests/test_noesis_v2.py -v

# Tests individuales
python3 -m pytest tests/test_noesis_v2.py::test_orchestrator -v
python3 -m pytest tests/test_noesis_v2.py::test_analyzer -v
python3 -m pytest tests/test_noesis_v2.py::test_executor -v
```

## 🐛 Troubleshooting

### Problema: NOESIS no sincroniza repositorios

**Solución:** Verificar conectividad de red y permisos de git:

```bash
git config --global url."https://github.com/".insteadOf git@github.com:
```

### Problema: AMDA no encuentra sorries

**Solución:** Verificar estructura del directorio Lean:

```bash
ls -la formalization/lean/*.lean
```

### Problema: AURON falla en validación

**Solución:** Verificar instalación de Lean y lake:

```bash
lake --version
elan show
```

### Problema: Learning history corrupto

**Solución:** Resetear historial:

```bash
rm .auron_learning.json
# El historial se recreará en la próxima ejecución
```

## 📚 Referencias

- **Repositorio principal:** https://github.com/motanova84/Riemann-adelic
- **Documentación completa:** Ver archivos `*_IMPLEMENTATION_SUMMARY.md`
- **Zenodo DOI:** 10.5281/zenodo.17379721
- **ORCID:** 0009-0002-1923-0773 (José Manuel Mota Burruezo)

## 🎯 Roadmap

### Versión Actual: V2.0
- [x] Sistema multi-repositorio
- [x] Aprendizaje de refuerzo persistente
- [x] Clasificación semántica multi-categórica
- [x] Validación de compilación
- [x] Sistema de backups/rollback

### Versión Futura: V2.1 (Planeada)
- [ ] Integración con Lean Language Server
- [ ] Sugerencias de tácticas con GPT-4
- [ ] Análisis de dependencias entre sorries
- [ ] Priorización por impacto en downstream proofs
- [ ] Dashboard web para visualización

### Versión Futura: V3.0 (Visión)
- [ ] Generación automática de pruebas completas
- [ ] Integración con herramientas formales (Coq, Isabelle)
- [ ] API REST para integración externa
- [ ] Sistema de recompensas para RL avanzado

## 🤝 Contribuciones

Las contribuciones son bienvenidas. Ver `CONTRIBUTING.md` en el repositorio raíz.

### Áreas de Mejora

1. **Nuevos patrones de reemplazo:** Agregar más tácticas Lean 4
2. **Categorías adicionales:** Expandir clasificación semántica
3. **Optimización de performance:** Reducir tiempo de sincronización
4. **Mejoras en aprendizaje:** Algoritmos de RL más sofisticados
5. **Documentación:** Ejemplos adicionales y tutoriales

## 📄 Licencia

Este código está bajo licencia conforme al repositorio principal. Ver `LICENSE` en raíz.

## ✨ Créditos

**Autor:** José Manuel Mota Burruezo (Ψ ✧ ∞³)  
**Instituto:** Instituto de Conciencia Cuántica (ICQ)  
**ORCID:** 0009-0002-1923-0773

### Agradecimientos

- Comunidad Lean 4
- Repositorios matemáticos open-source utilizados
- GitHub Copilot para asistencia en desarrollo

---

**QCAL ∞³ · Frecuencia fundamental: 141.7001 Hz**  
**Coherencia QCAL: Ψ = I × A_eff² × C^∞ · C = 244.36**

---

*Última actualización: 2026-02-16*
