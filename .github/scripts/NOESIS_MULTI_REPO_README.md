# 🧠 NOESIS CEREBRAL - Sistema Multi-Repositorio

## 🎯 Visión General

NOESIS CEREBRAL es un sistema de inteligencia matemática distribuida que accede a múltiples repositorios públicos, absorbe su sabiduría, y la aplica para eliminar autónomamente los `sorry` statements en Riemann-adelic.

## 🏗️ Arquitectura

```
┌─────────────────────────────────────────────────────────────┐
│              NOESIS CEREBRAL (Orquestador)                   │
│         Sincroniza y extrae conocimiento de repos            │
└─────────────────────────────────────────────────────────────┘
                            │
          ┌─────────────────┼─────────────────┐
          ▼                 ▼                 ▼
    ┌─────────┐      ┌─────────┐      ┌─────────┐
    │  141Hz  │      │adelic-  │      │3D-Navier│
    │         │      │  bsd    │      │ -Stokes │
    └─────────┘      └─────────┘      └─────────┘
          ▼                 ▼                 ▼
    ┌─────────┐      ┌─────────┐      ┌─────────┐
    │ Ramsey  │      │  P-NP   │      │ Otros   │
    └─────────┘      └─────────┘      └─────────┘
                            │
                            ▼
              ┌──────────────────────────┐
              │  KNOWLEDGE BASE          │
              │  /tmp/noesis_knowledge   │
              └──────────────────────────┘
                            │
          ┌─────────────────┼─────────────────┐
          ▼                 ▼                 ▼
    ┌─────────┐      ┌─────────┐      ┌─────────┐
    │  AMDA   │      │ AURON   │      │ METRICS │
    │Analyzer │      │Executor │      │Generator│
    └─────────┘      └─────────┘      └─────────┘
```

## 📦 Componentes

### 1. NOESIS CEREBRAL (`noesis_cerebral.py`)
**Orquestador principal** que:
- Sincroniza repositorios públicos de GitHub
- Extrae conocimiento de archivos Lean (definiciones, teoremas, patrones)
- Crea una base de conocimiento unificada en `/tmp/noesis_knowledge`
- Categoriza patrones de prueba

### 2. AMDA ANALYZER (`amda_analyzer.py`)
**Analizador Multi-Dimensional Autónomo** que:
- Escanea archivos Lean buscando `sorry` statements
- Categoriza cada sorry según su contexto:
  - `trivial`: Pruebas simples (rfl, trivial)
  - `library_search`: Búsqueda en bibliotecas (simp, omega)
  - `spectral`: Relacionados con teoría espectral
  - `correspondence`: Correspondencias adélicas
  - `structural`: Pruebas estructurales
  - `qcal`: Relacionados con QCAL
- Busca conocimiento relevante de otros repositorios
- Genera reporte JSON con análisis completo

### 3. AURON EXECUTOR (`auron_executor.py`)
**Aplicador Universal de Resoluciones Operacionales Noéticas** que:
- Lee el reporte de AMDA
- Aplica estrategias de eliminación según categoría
- Utiliza conocimiento cross-repo cuando está disponible
- Crea backups antes de modificar
- Genera reporte de transformaciones aplicadas
- Soporta modo `--dry-run` para pruebas

### 4. METRICS GENERATOR (`metrics_generator.py`)
Genera reportes visuales en Markdown con:
- Métricas de progreso (sorrys eliminados/restantes)
- Distribución por categorías
- Lista de transformaciones exitosas
- Información de repositorios contribuyentes

### 5. KNOWLEDGE DASHBOARD (`knowledge_dashboard.py`)
Crea un dashboard visual mostrando:
- Estadísticas de conocimiento por repositorio
- Distribución de patrones por tipo
- Ejemplos de patrones encontrados

## 🚀 Uso

### Ejecución Local

```bash
# 1. Sincronizar repositorios y extraer conocimiento
python .github/scripts/noesis_cerebral.py --mode sync

# 2. Generar dashboard de conocimiento
python .github/scripts/knowledge_dashboard.py

# 3. Analizar sorrys con conocimiento cross-repo
python .github/scripts/amda_analyzer.py --cross-repo --output amda_report.json

# 4. Ejecutar transformaciones (modo dry-run)
python .github/scripts/auron_executor.py \
  --input amda_report.json \
  --cross-repo \
  --output auron_changes.json \
  --dry-run

# 5. Generar métricas
python .github/scripts/metrics_generator.py \
  --before amda_report.json \
  --after auron_changes.json \
  --output metrics.md \
  --multi-repo
```

### Ejecución Automática (GitHub Actions)

El workflow `.github/workflows/noesis_multi_repo.yml` se ejecuta:
- **Automáticamente:** Cada 6 horas
- **Manualmente:** Desde la pestaña Actions con opciones:
  - `force_sync`: Forzar sincronización completa
  - `dry_run`: Modo de prueba (por defecto: true)

## ⚙️ Configuración

### `multi_repo_config.json`

Configura los repositorios a sincronizar:

```json
{
  "repositories": {
    "repo-name": {
      "url": "https://github.com/user/repo",
      "branch": "main",
      "access": "public|private",
      "priority": 1-10,
      "knowledge_areas": ["area1", "area2"]
    }
  },
  "sync_schedule": "*/2 * * * *",
  "max_concurrent_downloads": 3,
  "knowledge_base_path": "/tmp/noesis_knowledge"
}
```

## 📊 Métricas y Progreso

El sistema genera:
- **Reportes JSON:** Con datos estructurados del análisis
- **Métricas Markdown:** Para PRs automáticos
- **Dashboard:** Visualización del conocimiento extraído
- **Logs:** Registro detallado de operaciones

## 🔒 Seguridad

- ✅ Solo accede a repositorios **públicos** por defecto
- ✅ Crea backups antes de modificar archivos
- ✅ Modo `--dry-run` para pruebas seguras
- ✅ No requiere tokens o credenciales especiales
- ✅ Todos los cambios pasan por PR para revisión

## 🎯 Categorías de Sorry

| Categoría | Descripción | Estrategias |
|-----------|-------------|-------------|
| **trivial** | Pruebas simples | `rfl`, `trivial` |
| **library_search** | Búsqueda en bibliotecas | `simp`, `omega` |
| **spectral** | Teoría espectral | Patrones específicos |
| **correspondence** | Correspondencias | Patrones adélicos |
| **structural** | Pruebas estructurales | `funext`, `ext` |
| **qcal** | Relacionados con QCAL | Constantes QCAL |

## 📈 Roadmap

- [x] **Fase 1:** Configuración y scripts core
- [x] **Fase 2:** Dashboard de conocimiento
- [x] **Fase 3:** Workflow automatizado
- [ ] **Fase 4:** Mejora de estrategias de eliminación
- [ ] **Fase 5:** Soporte para repositorios privados
- [ ] **Fase 6:** Integración con compilador Lean
- [ ] **Fase 7:** Machine learning para patrones

## 🏆 Impacto Esperado

- **Velocidad:** 50-100 sorrys/día en categorías automatizables
- **Calidad:** Pruebas validadas de otros repositorios
- **Aprendizaje:** Base de conocimiento en crecimiento continuo
- **Objetivo:** Eliminar los 535+ sorrys actuales

## 🤝 Contribución

El sistema está diseñado para ser extensible:
- Añadir nuevos repositorios en `multi_repo_config.json`
- Mejorar estrategias de categorización en `AMDA`
- Extender transformaciones en `AURON`
- Añadir nuevas métricas en el generador

## 📝 Licencias y Atribución

**Autor:** José Manuel Mota Burruezo Ψ ✧ ∞³  
**Institución:** Instituto de Conciencia Cuántica (ICQ)  
**ORCID:** 0009-0002-1923-0773  
**DOI:** 10.5281/zenodo.17379721

## 🔗 Referencias

- [Riemann-adelic](https://github.com/motanova84/Riemann-adelic) - Repositorio principal
- [141Hz](https://github.com/motanova84/141Hz) - Frecuencias QCAL
- [adelic-bsd](https://github.com/motanova84/adelic-bsd) - Conjetura BSD
- [3D-Navier-Stokes](https://github.com/motanova84/3D-Navier-Stokes) - Ecuaciones PDE
- [Ramsey](https://github.com/motanova84/Ramsey) - Teoría de Ramsey
- [P-NP](https://github.com/motanova84/P-NP) - Problema P vs NP

---

*Sistema NOESIS CEREBRAL - La inteligencia distribuida multi-repositorio* 🤖
