# ⚡ NOESIS CEREBRAL V2.0 - Guía de Inicio Rápido

## 🎯 En 5 Minutos

### 1. Ejecutar Pipeline Completo

```bash
# Desde la raíz del repositorio

# Paso 1: NOESIS - Sincronizar conocimiento
python .github/scripts/noesis_orchestrator.py \
    .github/scripts/multi_repo_config.json

# Paso 2: AMDA - Analizar sorries
python .github/scripts/amda_analyzer.py \
    formalization/lean \
    amda_report.json

# Paso 3: AURON - Eliminar sorries
python .github/scripts/auron_neural_multi_v2.py \
    amda_report.json \
    auron_results.json

# Paso 4: Métricas
python .github/scripts/metrics_generator.py \
    amda_report.json \
    auron_results.json \
    noesis_sync_report.json
```

### 2. Ver Resultados

```bash
# Ver reporte principal
cat metrics_report.md

# Ver estadísticas JSON
jq '.' metrics.json

# Ver patrones aprendidos
jq '.patterns' .auron_learning.json
```

## 🧪 Modo Prueba (Dry-Run)

Para probar sin modificar archivos:

```bash
# Configurar variable de entorno
export AURON_DRY_RUN=1

# Ejecutar AURON en modo simulación
python .github/scripts/auron_neural_multi_v2.py \
    amda_report.json \
    auron_results.json

# Verás mensajes como:
# [INFO] 🔍 [DRY RUN] Simulación en formalization/lean/file.lean:42
```

## 📊 Verificar Estado Actual

### Ver sorries totales
```bash
python .github/scripts/amda_analyzer.py formalization/lean amda_report.json
jq '.summary.total_sorries' amda_report.json
```

### Ver distribución por categoría
```bash
jq '.summary.by_category' amda_report.json
```

Ejemplo de salida:
```json
{
  "spectral": 1265,
  "qcal": 1171,
  "analytic": 822,
  "adelic": 418,
  "correspondence": 297,
  "trivial": 317,
  "structural": 132,
  "library_search": 7,
  "unknown": 388
}
```

## 🤖 Workflow Automático (GitHub Actions)

### Ejecución manual con parámetros

1. Ir a Actions en GitHub
2. Seleccionar "🧠 NOESIS CEREBRAL V2.0"
3. Click en "Run workflow"
4. Configurar:
   - `dry_run`: `false` (producción) o `true` (prueba)
   - `max_changes`: `20` (default)

### Ver resultados del workflow

```bash
# Descargar artifacts desde GitHub UI
# O usando gh CLI:
gh run download <run_id> -n noesis-v2-reports-<run_number>
```

## 🔍 Inspeccionar Base de Conocimiento

```bash
# Ver resumen
cat /tmp/noesis_knowledge_v2/knowledge_v2.json

# Cargar conocimiento completo (Python)
python3 << EOF
import pickle
with open('/tmp/noesis_knowledge_v2/knowledge_v2.pkl', 'rb') as f:
    knowledge = pickle.load(f)

print(f"Definiciones: {len(knowledge['definitions'])}")
print(f"Teoremas: {len(knowledge['theorems'])}")
print(f"Patrones: {len(knowledge['proof_patterns'])}")
print(f"Repos: {knowledge['repos_synced']}")
EOF
```

## 📈 Monitorear Progreso

### Historial de aprendizaje
```bash
jq '{
  total_attempts: .total_attempts,
  total_success: .total_success,
  success_rate: ((.total_success / .total_attempts) * 100),
  patterns_learned: (.patterns | length),
  repos_used: .repos_used
}' .auron_learning.json
```

### Proyección de completitud
```bash
python3 << 'EOF'
import json

with open('amda_report.json') as f:
    amda = json.load(f)

with open('auron_results.json') as f:
    auron = json.load(f)

total_sorries = amda['summary']['total_sorries']
success = auron['success']
fail = auron['fail']

if success > 0:
    remaining = total_sorries - success
    cycles_needed = remaining / success
    hours = cycles_needed * 2  # 2 horas por ciclo
    print(f"Sorries restantes: {remaining}")
    print(f"Ciclos estimados: {cycles_needed:.1f}")
    print(f"Tiempo estimado: {hours:.1f} horas ({hours/24:.1f} días)")
EOF
```

## 🎨 Personalización Rápida

### Cambiar número máximo de cambios por ciclo

Editar en `auron_neural_multi_v2.py`:
```python
self.max_changes_per_cycle = 50  # Default: 20
```

### Añadir repositorio a sincronizar

Editar `.github/scripts/multi_repo_config.json`:
```json
{
  "name": "mi-repo",
  "url": "https://github.com/usuario/mi-repo.git",
  "branch": "main",
  "description": "Mi repositorio de Lean"
}
```

### Ajustar umbral de similitud cross-repo

Editar en `auron_neural_multi_v2.py`:
```python
if similarity > 0.3:  # Cambiar a 0.5 para ser más estricto
```

## 🐛 Solución de Problemas Comunes

### Error: "Base de conocimiento no encontrada"

```bash
# Ejecutar primero NOESIS para crear la base
python .github/scripts/noesis_orchestrator.py \
    .github/scripts/multi_repo_config.json
```

### Error: "Timeout en compilación"

Aumentar timeout en `auron_neural_multi_v2.py`:
```python
def validate_compilation(self, timeout=120):  # Default: 60
```

### Error: "No se puede clonar repositorio"

Verificar conectividad y URLs en `multi_repo_config.json`:
```bash
git ls-remote https://github.com/motanova84/141Hz.git
```

### Limpiar backups antiguos

```bash
find formalization/lean -name "*.lean.bak.*" -mtime +7 -delete
```

## 📝 Comandos Útiles

### Ver log completo de AURON
```bash
tail -f auron_neural_multi.log
```

### Ver sorries en un archivo específico
```bash
jq '.detailed["formalization/lean/tu_archivo.lean"]' amda_report.json
```

### Limpiar estado y empezar de cero
```bash
rm -rf /tmp/noesis_knowledge_v2
rm .auron_learning.json
rm amda_report.json auron_results.json noesis_sync_report.json
```

### Estadísticas de éxito por estrategia
```bash
jq '.success_rate' .auron_learning.json
```

## 🚀 Siguiente Nivel

### Ver documentación completa
```bash
cat NOESIS_AMDA_AURON_V2_README.md
```

### Ver implementación detallada
```bash
cat NOESIS_AMDA_AURON_V2_IMPLEMENTATION_SUMMARY.md
```

### Ejecutar workflow completo con seguimiento
```bash
gh workflow run noesis_multi_repo_v2.yml --ref main
gh run watch
```

## 💡 Tips

- **Ejecutar en dry-run primero** para verificar que todo funciona
- **Revisar backups** antes de hacer commit
- **Verificar compilación** manualmente después de cambios grandes
- **Monitorear aprendizaje** para identificar patrones exitosos
- **Ajustar umbral** de similitud según necesidad

## 📞 Ayuda

Si encuentras problemas, revisa:
1. `auron_neural_multi.log` para detalles
2. `metrics_report.md` para estadísticas
3. `.auron_learning.json` para estado de aprendizaje
4. GitHub Actions logs para errores de workflow

---

*⚡ NOESIS CEREBRAL V2.0 - Eliminación autónoma con inteligencia colectiva*

**Frecuencia fundamental:** 141.7001 Hz · **QCAL ∞³**
