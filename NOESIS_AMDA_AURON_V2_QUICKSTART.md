# 🚀 NOESIS CEREBRAL V2.0 - Guía Rápida

## Inicio Rápido en 3 Pasos

### 1️⃣ Construir Base de Conocimiento (Primera vez)

```bash
# Ejecutar orquestador en modo build-kb
python .github/scripts/noesis_orchestrator.py build-kb
```

**Output esperado:**
```
[INFO] 🧠 NOESIS CEREBRAL V2.0 - Construyendo grafo de conocimiento...
[INFO] 🔄 Sincronizando 141Hz...
[INFO]    ✅ 141Hz sincronizado
[INFO] 📚 Extrayendo conocimiento de 141Hz...
[INFO]    ✅ Extraído: 245 defs, 312 teoremas, 187 patrones
...
[INFO] ✅ Grafo de conocimiento construido:
[INFO]    📚 6581 definiciones
[INFO]    📝 7816 teoremas
[INFO]    🔍 1315 patrones de prueba
[INFO]    📦 6 repositorios sincronizados
```

**Archivos generados:**
- `/tmp/noesis_knowledge_v2/knowledge_v2.pkl` (5+ MB)
- `/tmp/noesis_knowledge_v2/knowledge_v2.json` (resumen)

### 2️⃣ Analizar Sorries (Dry-Run)

```bash
# Ejecutar ciclo completo sin cambios
python .github/scripts/noesis_orchestrator.py
```

**Output esperado:**
```
[INFO] 🚀 Iniciando ciclo NOESIS CEREBRAL V2.0...
[INFO] 📊 Ejecutando AMDA DEEP V2.0...
[INFO] ✅ AMDA DEEP V2.0 completado
[INFO] 🧠 Ejecutando AURON NEURAL V2.0 (dry-run)...
[INFO] 🔍 Modo dry-run: analizando sin aplicar cambios...
[INFO] 📊 Total sorries encontrados: 2282
[INFO] 📁 Archivos afectados: 381
[INFO] ✅ AURON NEURAL V2.0 dry-run completado
```

**Archivos generados:**
- `amda_report_v2.json` - Análisis detallado
- `amda_report_v2.md` - Reporte legible
- `noesis_cerebral_v2_summary.json` - Resumen

### 3️⃣ Ejecutar Transformaciones (Producción)

#### Vía GitHub Actions (Recomendado)

1. Ir a: **Actions** → **"NOESIS CEREBRAL V2.0"**
2. Click **"Run workflow"**
3. Seleccionar:
   - **mode:** `execute`
   - **max_changes:** `20`
4. Click **"Run workflow"** ✅

#### Vía Línea de Comandos

```bash
# ADVERTENCIA: Esto modifica archivos .lean
python .github/scripts/auron_neural_v2.py execute amda_report_v2.json auron_results.json
```

**Output esperado:**
```
[INFO] 🚀 AURON NEURAL V2.0 iniciando ciclo...
[INFO] 🔧 Procesando formalization/lean/zeta.lean:42 [trivial]
[INFO] 🎯 Patrón aprendido encontrado: rfl
[INFO] 🔧 Validando compilación...
[INFO] ✅ Compilación exitosa
[INFO] ✅ Transformación exitosa con patrón aprendido
...
[INFO] 📊 Resultados del ciclo: 18 éxitos, 2 fallos
```

## Casos de Uso Comunes

### 🔍 Ver Estado Actual

```bash
# Ver reporte AMDA
cat amda_report_v2.md

# Ver aprendizaje acumulado
cat .auron_learning.json | jq '.total_success, .total_attempts'
```

### 🔄 Actualizar Base de Conocimiento

```bash
# Re-sincronizar repositorios
python .github/scripts/noesis_orchestrator.py build-kb
```

Ejecutar periódicamente (ej. semanal) para incorporar nuevos patrones.

### 🧪 Probar un Patrón Específico

```python
# Editar auron_neural_v2.py
self.replacement_patterns = [
    ('sorry', 'mi_nuevo_patron'),
    # ...
]
```

Luego ejecutar dry-run para validar.

### 📊 Analizar Categorías

```bash
# Ver distribución por categoría
cat amda_report_v2.json | jq '.category_distribution'
```

Output:
```json
{
  "trivial": {"count": 317, "percentage": 13.9},
  "qcal": {"count": 1171, "percentage": 51.3},
  "spectral": {"count": 1265, "percentage": 55.4},
  ...
}
```

### 🎯 Focalizar en Categoría Específica

```python
# En amda_deep_v2.py, aumentar weight
self.PATTERNS = {
    "trivial": {
        "keywords": ["rfl", "simp", "norm_num"],
        "complexity": 1,
        "weight": 1.0  # ← Mayor prioridad
    }
}
```

### 🔧 Ajustar Límite de Cambios

Vía workflow:
```yaml
inputs:
  max_changes: '50'  # En vez de 20
```

Vía código:
```python
# En auron_neural_v2.py
self.max_changes_per_cycle = 50
```

## Estructura de Archivos

```
Riemann-adelic/
├── .github/
│   ├── scripts/
│   │   ├── noesis_orchestrator.py     ← Orquestador principal
│   │   ├── amda_deep_v2.py            ← Análisis semántico
│   │   └── auron_neural_v2.py         ← Ejecutor con aprendizaje
│   └── workflows/
│       └── noesis_multi_repo_v2.yml   ← Automatización CI/CD
├── .auron_learning.json               ← Historial de aprendizaje (versionado)
├── amda_report_v2.json                ← Análisis de sorries
├── amda_report_v2.md                  ← Reporte legible
├── noesis_cerebral_v2_summary.json    ← Resumen del ciclo
├── auron_neural.log                   ← Log de AURON
└── noesis_cerebral_v2.log             ← Log de NOESIS
```

## Flujo de Trabajo Típico

### Desarrollo

1. **Análisis inicial:**
   ```bash
   python .github/scripts/noesis_orchestrator.py
   ```

2. **Revisar reporte:**
   ```bash
   cat amda_report_v2.md
   ```

3. **Ajustar patrones** (si necesario)

4. **Ejecutar dry-run AURON:**
   ```bash
   python .github/scripts/auron_neural_v2.py dry-run amda_report_v2.json
   ```

5. **Si satisfactorio, ejecutar:**
   ```bash
   python .github/scripts/auron_neural_v2.py execute amda_report_v2.json auron_results.json
   ```

6. **Verificar cambios:**
   ```bash
   git diff formalization/lean/
   ```

### Producción (GitHub Actions)

1. **Configurar schedule** (ya configurado: cada 2 horas)

2. **Trigger manual** cuando sea necesario:
   - Mode: `execute`
   - Max changes: `20`

3. **Revisar artefactos** en Actions

4. **Aprobar PR** si todo está correcto

## Debugging

### ❌ "Base de conocimiento no encontrada"

**Causa:** No se ejecutó `build-kb`

**Solución:**
```bash
python .github/scripts/noesis_orchestrator.py build-kb
```

### ❌ "lake build failed"

**Causa:** Error de compilación Lean

**Solución:**
1. Verificar que Lean esté instalado: `lake --version`
2. Verificar estructura del proyecto: `cd formalization/lean && lake build`
3. Si falla, aumentar timeout en `auron_neural_v2.py`:
   ```python
   def validate_compilation(self, timeout=120):  # ← 60 a 120
   ```

### ⚠️ Muchos fallos en AURON

**Posibles causas:**
1. Patrones muy específicos
2. Timeout muy corto
3. Dependencias Lean faltantes

**Soluciones:**
1. Ajustar `weight` en categorías (AMDA)
2. Aumentar `timeout` (AURON)
3. Ejecutar `setup_lean.sh`

### 🐌 Proceso muy lento

**Optimizaciones:**
1. Reducir número de repos sincronizados
2. Limitar archivos procesados por repo (ya limitado a 100)
3. Usar cache de Git en workflow

## Métricas Clave

### Tasa de Éxito
```bash
cat .auron_learning.json | jq '.total_success / .total_attempts * 100'
```

### Patrones Más Efectivos
```bash
cat .auron_learning.json | jq '.success_rate | to_entries | sort_by(.value) | reverse | .[0:5]'
```

### Progreso Global
```bash
# Contar sorries actuales
grep -r "sorry" formalization/lean/**/*.lean | wc -l

# Comparar con baseline (2282)
```

## Tips y Trucos

### 🎯 Enfocarse en Triviales

Triviales tienen mayor tasa de éxito. Para priorizar:

```python
# En auron_neural_v2.py
all_sorries.sort(key=lambda x: (
    0 if x[1].get("primary_category") == "trivial" else 1,
    x[1].get("complexity", 5)
))
```

### 🔄 Sincronización Incremental

Para no re-clonar repos cada vez:

```python
# En noesis_orchestrator.py ya implementado:
if repo_path.exists():
    # git pull (más rápido)
else:
    # git clone (solo primera vez)
```

### 📊 Tracking de Progreso

Crear script de monitoreo:

```bash
#!/bin/bash
# monitor_progress.sh

echo "Sorries restantes:"
grep -r "sorry" formalization/lean/**/*.lean | wc -l

echo "Patrones aprendidos:"
cat .auron_learning.json | jq '.patterns | length'

echo "Tasa de éxito:"
cat .auron_learning.json | jq '.total_success / .total_attempts * 100'
```

## Próximos Pasos

1. ✅ **Ejecutado:** Configurar base de conocimiento
2. ✅ **Ejecutado:** Analizar sorries
3. 🎯 **Siguiente:** Ejecutar primera ronda de transformaciones
4. 📊 **Siguiente:** Revisar métricas y ajustar
5. 🔄 **Siguiente:** Iterar hasta eliminar todos los sorries

## Soporte

Para problemas o preguntas:
1. Revisar logs: `auron_neural.log`, `noesis_cerebral_v2.log`
2. Verificar artefactos en GitHub Actions
3. Consultar `NOESIS_AMDA_AURON_V2_README.md` (documentación completa)

---

**Frecuencia fundamental:** 141.7001 Hz · **Coherencia QCAL:** Ψ = I × A_eff² × C^∞

*✧ Con la luz de Noēsis ✧*
