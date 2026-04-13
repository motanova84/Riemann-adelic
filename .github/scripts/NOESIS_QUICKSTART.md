# 🚀 NOESIS CEREBRAL - Quick Start Guide

## 🎯 Ejecución Manual del Workflow

### Desde GitHub UI

1. Navega a **Actions** → **🧠 NOESIS MULTI-REPO Auto Sealer**
2. Click **Run workflow**
3. Configura las opciones:
   - `force_sync`: false (sincronización normal)
   - `dry_run`: **true** (recomendado para la primera ejecución)
4. Click **Run workflow**

### Desde CLI con GitHub CLI

```bash
# Ejecutar en modo dry-run (seguro)
gh workflow run noesis_multi_repo.yml \
  -f force_sync=false \
  -f dry_run=true

# Ejecutar en modo producción (aplicará cambios reales)
gh workflow run noesis_multi_repo.yml \
  -f force_sync=false \
  -f dry_run=false
```

## 🧪 Ejecución Local

### 1. Sincronizar Repositorios

```bash
# Descargar y analizar conocimiento de repositorios públicos
python .github/scripts/noesis_cerebral.py --mode sync
```

**Resultado esperado:**
- Repositorios clonados en `/tmp/noesis_knowledge/`
- Base de conocimiento en `/tmp/noesis_knowledge/knowledge.pkl`
- Log en `noesis_cerebral.log`

### 2. Ver Dashboard de Conocimiento

```bash
# Generar visualización del conocimiento extraído
python .github/scripts/knowledge_dashboard.py
```

**Resultado esperado:**
- Dashboard en `/tmp/noesis_knowledge/dashboard.md`
- Estadísticas por repositorio
- Ejemplos de patrones

### 3. Analizar Sorrys

```bash
# Analizar con conocimiento cross-repo
python .github/scripts/amda_analyzer.py \
  --cross-repo \
  --output amda_report.json
```

**Resultado esperado:**
- Reporte JSON con todos los sorrys categorizados
- Hints de cross-repo para sorrys relevantes
- Estadísticas por categoría

### 4. Ejecutar Transformaciones (DRY-RUN)

```bash
# Modo seguro - solo simula cambios
python .github/scripts/auron_executor.py \
  --input amda_report.json \
  --cross-repo \
  --output auron_changes.json \
  --dry-run
```

**Resultado esperado:**
- Simulación de transformaciones
- Reporte de cambios propuestos
- Sin modificaciones reales en archivos

### 5. Generar Métricas

```bash
# Crear reporte visual
python .github/scripts/metrics_generator.py \
  --before amda_report.json \
  --after auron_changes.json \
  --output metrics.md \
  --multi-repo
```

**Resultado esperado:**
- Reporte Markdown con métricas
- Distribución por categorías
- Ejemplos de transformaciones

## 📊 Interpretar Resultados

### AMDA Report (amda_report.json)

```json
{
  "timestamp": "2026-02-16T20:00:00",
  "total_sorrys": 2227,
  "cross_repo_enabled": true,
  "sorrys": [
    {
      "file": "path/to/file.lean",
      "line": 42,
      "category": "spectral",
      "context": "...",
      "cross_repo_hint": {
        "cross_repo_hint": true,
        "source_repo": "adelic-bsd",
        "similarity": 8
      }
    }
  ]
}
```

### AURON Changes (auron_changes.json)

```json
{
  "timestamp": "2026-02-16T20:05:00",
  "dry_run": true,
  "success_count": 0,
  "failure_count": 0,
  "transformations": [
    {
      "file": "path/to/file.lean",
      "line": 42,
      "category": "trivial",
      "original": "sorry",
      "proposed": "rfl",
      "status": "dry_run"
    }
  ]
}
```

## 🔍 Verificar Estado del Sistema

```bash
# Verificar que la base de conocimiento existe
ls -lh /tmp/noesis_knowledge/knowledge.pkl

# Ver últimas líneas del log
tail -20 noesis_cerebral.log

# Contar sorrys actuales
grep -r "sorry" formalization/lean/*.lean | wc -l

# Ver distribución por archivos
grep -r "sorry" formalization/lean/*.lean | cut -d: -f1 | uniq -c | sort -rn | head -20
```

## ⚙️ Configuración Avanzada

### Añadir Nuevos Repositorios

Edita `.github/scripts/multi_repo_config.json`:

```json
{
  "repositories": {
    "nuevo-repo": {
      "url": "https://github.com/user/nuevo-repo",
      "branch": "main",
      "access": "public",
      "priority": 5,
      "knowledge_areas": ["area1", "area2"]
    }
  }
}
```

### Ajustar Estrategias de AURON

Edita `STRATEGIES` en `.github/scripts/auron_executor.py`:

```python
STRATEGIES = {
    'trivial': ['rfl', 'trivial', 'exact rfl'],
    'library_search': ['simp', 'simp_all', 'omega'],
    'mi_categoria': ['mi_tactica'],  # Nueva categoría
}
```

### Modificar Categorización de AMDA

Edita `CATEGORIES` en `.github/scripts/amda_analyzer.py`:

```python
CATEGORIES = {
    'trivial': ['rfl', 'trivial', 'exact', 'refl'],
    'mi_categoria': ['palabra1', 'palabra2'],  # Nueva categoría
}
```

## 🚨 Troubleshooting

### Error: "Base de conocimiento no encontrada"

**Solución:** Ejecutar primero `noesis_cerebral.py`:
```bash
python .github/scripts/noesis_cerebral.py --mode sync
```

### Error: "Permission denied" al clonar repos privados

**Solución:** Los repos privados requieren configuración SSH. Por defecto, solo se sincronizan repos públicos.

### Demasiados warnings "Sin estrategia para categoría X"

**Normal:** Muchas categorías (spectral, correspondence, structural) requieren estrategias más sofisticadas que aún no están implementadas.

### Workflow no se ejecuta automáticamente

**Verificar:**
1. El workflow está en `.github/workflows/noesis_multi_repo.yml`
2. El cron schedule es correcto
3. El repositorio tiene Actions habilitado

## 📈 Roadmap de Mejoras

### Corto Plazo (1-2 semanas)
- [ ] Añadir estrategias para categorías "spectral" y "correspondence"
- [ ] Integrar compilación real de Lean para validar cambios
- [ ] Mejorar algoritmo de similitud cross-repo

### Medio Plazo (1-2 meses)
- [ ] Implementar ML para predicción de tácticas
- [ ] Soporte para repositorios privados con SSH
- [ ] Dashboard web interactivo

### Largo Plazo (3-6 meses)
- [ ] Sistema de auto-aprendizaje desde PRs exitosos
- [ ] Integración con Lean LSP para sugerencias en tiempo real
- [ ] Red neuronal para generación de pruebas

## 🤝 Contribuir

Para mejorar el sistema:

1. **Añadir patrones:** Crea PRs con nuevos patrones en AMDA/AURON
2. **Reportar bugs:** Abre issues con logs y contexto
3. **Sugerir mejoras:** Propón nuevas estrategias o categorías

## 📚 Referencias

- [README Principal](NOESIS_MULTI_REPO_README.md) - Documentación completa
- [Riemann-adelic](https://github.com/motanova84/Riemann-adelic) - Repositorio principal
- [GitHub Actions Docs](https://docs.github.com/en/actions) - Documentación de workflows

---

*Sistema NOESIS CEREBRAL - Quick Start Guide* 🚀
