# 🧠 NOESIS CEREBRAL V2.0 - Sistema de Inteligencia Multi-Repositorio

## Descripción General

**NOESIS CEREBRAL V2.0** es un sistema avanzado de inteligencia artificial diseñado para eliminar automáticamente "sorry" statements en formalizaciones Lean mediante aprendizaje de múltiples repositorios.

## Arquitectura

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│                         NOESIS CEREBRAL V2.0 (Orquestador)                       │
│                  (Repositorio Riemann-adelic - Cerebro Principal)                │
└─────────────────────────────────────────────────────────────────────────────────┘
                                      │
              ┌───────────────────────┼───────────────────────┐
              ▼                       ▼                       ▼
┌─────────────────────────┐ ┌─────────────────────────┐ ┌─────────────────────────┐
│   AMDA DEEP V2.0        │ │   KNOWLEDGE GRAPH       │ │   AURON NEURAL V2.0     │
│   • Análisis semántico   │ │   • 6 repositorios      │ │   • Aprendizaje          │
│   • Clasificación multi  │ │   • Definiciones        │ │   • Validación lake build│
│   • Similitud contextual │ │   • Teoremas            │ │   • Persistencia patrones│
│   • Detección de patrones│ │   • Patrones de prueba  │ │   • Priorización         │
└─────────────────────────┘ └─────────────────────────┘ └─────────────────────────┘
              │                       │                       │
              └───────────────────────┼───────────────────────┘
                                      ▼
┌─────────────────────────────────────────────────────────────────────────────────┐
│                         SISTEMA DE APRENDIZAJE PERMANENTE                         │
│                           .auron_learning.json                                     │
│   • Patrones exitosos por contexto hash                                          │
│   • Tasas de éxito por patrón                                                    │
│   • Historial de transformaciones                                                │
│   • Repositorios fuente                                                          │
└─────────────────────────────────────────────────────────────────────────────────┘
```

## Componentes Principales

### 1. NOESIS CEREBRAL V2.0 (Orquestador)
**Archivo:** `.github/scripts/noesis_orchestrator.py`

**Responsabilidades:**
- Sincroniza múltiples repositorios (141Hz, adelic-bsd, 3D-Navier-Stokes, etc.)
- Construye grafo de conocimiento unificado
- Coordina ejecución de AMDA y AURON
- Genera reportes agregados

**Características clave:**
- Clonación/actualización automática de repos
- Extracción de definiciones, teoremas y patrones de prueba
- Almacenamiento en formato pickle para acceso rápido
- Resumen en JSON para visualización

### 2. AMDA DEEP V2.0 (Analizador Semántico)
**Archivo:** `.github/scripts/amda_deep_v2.py`

**Responsabilidades:**
- Análisis semántico profundo de sorries
- Clasificación multi-categórica (6 categorías)
- Búsqueda de soluciones similares por Jaccard similarity
- Generación de reportes detallados

**Categorías de clasificación:**
1. **trivial** (13.9%): `rfl`, `simp`, `norm_num`, etc.
2. **correspondence** (13.0%): bijecciones espectrales
3. **qcal** (51.3%): QCAL coherence, f₀, Ψ, C
4. **adelic** (18.3%): estructuras adélicas
5. **spectral** (55.4%): operadores, Fredholm
6. **analytic** (36.0%): zeta, continuación analítica

### 3. AURON NEURAL V2.0 (Ejecutor con Aprendizaje)
**Archivo:** `.github/scripts/auron_neural_v2.py`

**Responsabilidades:**
- Aplicación de transformaciones con validación
- Aprendizaje de patrones exitosos
- Persistencia de historial en `.auron_learning.json`
- Rollback automático en caso de error

**Características clave:**
- **Validación por compilación:** Cada cambio se valida con `lake build`
- **Aprendizaje por contexto:** Hash MD5 del contexto normalizado
- **Backup automático:** Copia de seguridad antes de cada cambio
- **Priorización inteligente:** Primero patrones aprendidos, luego cross-repo, finalmente patrones estándar

### 4. Sistema de Aprendizaje Permanente
**Archivo:** `.auron_learning.json`

**Estructura:**
```json
{
  "patterns": {
    "abc123def456": "rfl",
    "def456ghi789": "by simp"
  },
  "success_rate": {
    "rfl": 45,
    "by simp": 32
  },
  "total_attempts": 150,
  "total_success": 89,
  "repos_used": ["141Hz", "adelic-bsd"],
  "transformations_history": [...]
}
```

## Flujo de Ejecución

### Ciclo Completo

```
1. NOESIS ORCHESTRATOR
   ├─ Sincronizar repos externos
   ├─ Extraer conocimiento (defs, teoremas, patrones)
   └─ Construir /tmp/noesis_knowledge_v2/knowledge_v2.pkl

2. AMDA DEEP V2.0
   ├─ Escanear archivos .lean
   ├─ Clasificar sorries (multi-categórico)
   ├─ Buscar soluciones similares (Jaccard)
   └─ Generar amda_report_v2.json

3. AURON NEURAL V2.0
   ├─ Cargar historial de aprendizaje
   ├─ Para cada sorry (ordenado por complejidad):
   │  ├─ Intentar patrón aprendido
   │  ├─ Intentar solución cross-repo
   │  ├─ Intentar patrones estándar
   │  └─ Validar con lake build
   ├─ Guardar .auron_learning.json
   └─ Generar commit_msg_*.txt
```

### Modos de Ejecución

#### 1. Dry-Run (por defecto)
```bash
python .github/scripts/noesis_orchestrator.py
```
- Construye knowledge base
- Analiza sorries
- NO aplica cambios

#### 2. Execute (producción)
```bash
# Vía workflow
gh workflow run noesis_multi_repo_v2.yml -f mode=execute -f max_changes=20
```
- Aplica hasta 20 cambios por ciclo
- Valida con lake build
- Commit automático

#### 3. Build KB Only
```bash
python .github/scripts/noesis_orchestrator.py build-kb
```
- Solo sincroniza repos
- Solo construye knowledge base

## Uso

### GitHub Actions (Recomendado)

**Ejecución automática:**
- Cada 2 horas (cron schedule)
- Modo: dry-run

**Ejecución manual:**
1. Ir a Actions → "NOESIS CEREBRAL V2.0"
2. Click "Run workflow"
3. Seleccionar:
   - `mode`: `dry-run` / `execute` / `build-kb-only`
   - `max_changes`: Número máximo de cambios (default: 20)

### Local (Desarrollo)

**Prerrequisitos:**
```bash
pip install pickle5
```

**Ejecutar ciclo completo:**
```bash
cd /path/to/Riemann-adelic
python .github/scripts/noesis_orchestrator.py
```

**Solo AMDA:**
```bash
python .github/scripts/amda_deep_v2.py amda_report.json amda_report.md
```

**Solo AURON (dry-run):**
```bash
python .github/scripts/auron_neural_v2.py dry-run amda_report.json
```

**AURON (execute):**
```bash
python .github/scripts/auron_neural_v2.py execute amda_report.json auron_results.json
```

## Archivos Generados

### Reportes
- `noesis_cerebral_v2_summary.json`: Resumen completo del ciclo
- `amda_report_v2.json`: Análisis detallado de sorries
- `amda_report_v2.md`: Reporte en formato Markdown
- `auron_results_v2.json`: Resultados de transformaciones
- `commit_msg_*.txt`: Mensaje de commit generado

### Logs
- `noesis_cerebral_v2.log`: Log del orquestador
- `auron_neural.log`: Log de AURON

### Persistencia
- `.auron_learning.json`: Historial de aprendizaje (versionado)
- `/tmp/noesis_knowledge_v2/`: Base de conocimiento (temporal)

### Backups
- `*.lean.bak.YYYYMMDD_HHMMSS`: Backups automáticos antes de cambios

## Seguridad y Validación

### Capas de Seguridad

1. **Backup automático:** Cada archivo se respalda antes de modificar
2. **Validación por compilación:** Solo se acepta si `lake build` pasa
3. **Rollback automático:** Si falla compilación, se restaura backup
4. **Límite de cambios:** Máximo 20 cambios por ciclo (configurable)
5. **Review humano:** Todos los cambios se someten a PR

### Validación de Conocimiento

- Repositorios sincronizados desde fuentes públicas
- Solo se extraen archivos .lean
- Filtrado de patrones con `sorry` (no se aprenden)
- Validación de similaridad mínima (>0.3 Jaccard)

## Configuración

### Repositorios Sincronizados

Editar en `noesis_orchestrator.py`:
```python
self.repos = [
    "motanova84/141Hz",
    "motanova84/adelic-bsd",
    "motanova84/3D-Navier-Stokes",
    "motanova84/Ramsey",
    "motanova84/P-NP",
    "motanova84/Riemann-adelic"
]
```

### Patrones de Clasificación

Editar en `amda_deep_v2.py`:
```python
self.PATTERNS = {
    "trivial": {
        "keywords": ["rfl", "simp", "norm_num"],
        "complexity": 1,
        "weight": 0.8
    },
    # ...
}
```

### Patrones de Reemplazo

Editar en `auron_neural_v2.py`:
```python
self.replacement_patterns = [
    ('sorry', 'rfl'),
    ('sorry', 'trivial'),
    # ...
]
```

## Métricas y Monitoreo

### Métricas Clave

- **Tasa de éxito:** `success / (success + fail)`
- **Patrones aprendidos:** Tamaño de `.auron_learning.json`
- **Sorries eliminados:** Tracking acumulativo
- **Tiempo estimado:** Proyección basada en tasa actual

### Dashboards

Los reportes generados incluyen:
- Distribución por categoría
- Top 10 archivos con más sorries
- Estadísticas de aprendizaje
- Repositorios fuente consultados

## Troubleshooting

### Error: "Base de conocimiento no encontrada"
**Solución:** Ejecutar primero:
```bash
python .github/scripts/noesis_orchestrator.py build-kb
```

### Error: "lake build timeout"
**Solución:** Aumentar timeout en `auron_neural_v2.py`:
```python
def validate_compilation(self, timeout=120):  # de 60 a 120
```

### Error: "No se encontraron archivos .lean"
**Verificar:** Estructura de directorios en repo sincronizado
- Busca en `formalization/lean/`
- Si no existe, busca en raíz

### Muchos fallos en AURON
**Posibles causas:**
1. Patrones muy específicos (ajustar weight en AMDA)
2. Timeout corto (aumentar en validate_compilation)
3. Dependencias Lean faltantes (verificar setup)

## Contribuciones

Para añadir nuevas características:

1. **Nuevos repositorios:** Editar `self.repos` en `noesis_orchestrator.py`
2. **Nuevas categorías:** Añadir a `self.PATTERNS` en `amda_deep_v2.py`
3. **Nuevos patrones:** Añadir a `self.replacement_patterns` en `auron_neural_v2.py`

## Referencias

- **Frecuencia fundamental:** 141.7001 Hz
- **Coherencia QCAL:** Ψ = I × A_eff² × C^∞
- **Constante C:** 244.36

## Licencia

Ver LICENSE en el repositorio principal.

## Autores

- José Manuel Mota Burruezo Ψ ✧ ∞³
- ORCID: 0009-0002-1923-0773
- Instituto de Conciencia Cuántica (ICQ)

---

*✧ Con la luz de Noēsis ✧*
