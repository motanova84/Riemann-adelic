# 🚀 NOESIS-AMDA-AURON V2.0 - Guía de Inicio Rápido

## ⚡ En 5 Minutos

### 1. Instalación Rápida
```bash
cd /home/runner/work/Riemann-adelic/Riemann-adelic
pip install numpy
```

### 2. Ejecución Manual del Pipeline Completo
```bash
# Paso 1: Sincronizar repositorios y cosechar conocimiento
python .github/scripts/noesis_orchestrator.py

# Paso 2: Analizar sorries
python .github/scripts/amda_deep_v2.py

# Paso 3: Aplicar transformaciones (dry-run primero)
python .github/scripts/auron_neural_v2.py amda_deep_report_v2.json --dry-run

# Paso 4: Aplicar transformaciones reales (si el dry-run está bien)
python .github/scripts/auron_neural_v2.py amda_deep_report_v2.json --max-changes 5
```

### 3. Ejecución con GitHub Actions
1. Ir a **Actions** en GitHub
2. Seleccionar workflow **"🧠 NOESIS-AMDA-AURON V2.0"**
3. Click en **"Run workflow"**
4. Configurar inputs:
   - `max_changes`: 10 (recomendado para primera ejecución)
   - `dry_run`: false
5. Click **"Run workflow"**

## 📊 Revisar Resultados

### Archivos Generados

1. **`noesis_v2_report.json`** - Reporte de sincronización
2. **`amda_deep_report_v2.json`** - Análisis de sorries
3. **`auron_neural_report_v2.json`** - Transformaciones aplicadas
4. **`noesis_v2.log`** - Log detallado

### Inspeccionar Conocimiento Cosechado

```bash
# Ver resumen de conocimiento
cat /tmp/noesis_knowledge_v2/knowledge_v2.json | python -m json.tool

# Verificar estado del sistema
cat .noesis_state.json | python -m json.tool
```

## 🎯 Casos de Uso Comunes

### Caso 1: Análisis Sin Modificaciones
```bash
# Solo sincronizar y analizar (sin cambios)
python .github/scripts/noesis_orchestrator.py
python .github/scripts/amda_deep_v2.py
# Revisar amda_deep_report_v2.json
```

### Caso 2: Transformación Conservadora
```bash
# Aplicar solo 3 cambios para probar
python .github/scripts/auron_neural_v2.py amda_deep_report_v2.json --max-changes 3
```

### Caso 3: Análisis de Repositorio Específico
```bash
# Editar .github/scripts/multi_repo_config.json primero
# Reducir lista de repos a solo los que interesan
python .github/scripts/noesis_orchestrator.py
```

## 🔍 Verificación Rápida

### Verificar Sincronización
```bash
ls /tmp/noesis_knowledge_v2/
# Debería mostrar: knowledge_v2.pkl, knowledge_v2.json, y carpetas de repos
```

### Verificar Sorries Encontrados
```bash
python -c "import json; print(json.load(open('amda_deep_report_v2.json'))['summary'])"
```

### Verificar Cambios Aplicados
```bash
python -c "import json; print(json.load(open('auron_neural_report_v2.json'))['summary'])"
```

## 🛠️ Solución de Problemas

### Problema: No se sincronizan repositorios privados
**Solución:** Configurar SSH keys para acceso a repos privados
```bash
eval "$(ssh-agent -s)"
ssh-add ~/.ssh/id_rsa
```

### Problema: Base de conocimiento vacía
**Solución:** Verificar que los repos tienen archivos .lean
```bash
find /tmp/noesis_knowledge_v2/ -name "*.lean" | head -10
```

### Problema: No se encuentran sorries
**Solución:** Verificar que existe el directorio de formalización
```bash
ls formalization/lean/*.lean | head -5
```

## 📈 Monitoreo de Progreso

### Ver Total de Sorries Actuales
```bash
grep -r "sorry" formalization/lean --include="*.lean" | wc -l
```

### Ver Sorries por Categoría
```bash
python -c "
import json
report = json.load(open('amda_deep_report_v2.json'))
for cat, count in report['summary']['by_category'].items():
    print(f'{cat}: {count}')
"
```

### Ver Repositorios con Soluciones
```bash
python -c "
import json
report = json.load(open('amda_deep_report_v2.json'))
repos = report['statistics']['solution_repos']
print('Repositorios con soluciones aplicables:')
for repo in repos:
    print(f'  - {repo}')
"
```

## 🎓 Ejemplos de Transformaciones

### Ver Commits Generados
```bash
python -c "
import json
report = json.load(open('auron_neural_report_v2.json'))
for i, msg in enumerate(report.get('commit_messages', [])[:3]):
    print(f'=== Commit {i+1} ===')
    print(msg)
    print()
"
```

### Ver Archivos Modificados
```bash
python -c "
import json
report = json.load(open('auron_neural_report_v2.json'))
files = report['changes']['files_modified']
print(f'Archivos modificados: {len(files)}')
for f in files:
    print(f'  - {f}')
"
```

## 🚨 Modo Seguro (Recomendado para Primera Ejecución)

```bash
# 1. Ejecutar todo en modo dry-run
python .github/scripts/noesis_orchestrator.py --dry-run
python .github/scripts/auron_neural_v2.py amda_deep_report_v2.json --dry-run --max-changes 3

# 2. Revisar reportes generados

# 3. Crear backup manual
cp -r formalization/lean formalization/lean.backup

# 4. Ejecutar con límite bajo
python .github/scripts/auron_neural_v2.py amda_deep_report_v2.json --max-changes 1

# 5. Verificar resultado
git diff

# 6. Si todo está bien, aumentar max-changes gradualmente
```

## ⏱️ Tiempos Estimados

| Paso | Tiempo Estimado | Depende de |
|------|----------------|------------|
| Sincronización de repos | 2-5 min | Número de repos, tamaño |
| Cosecha de conocimiento | 1-3 min | Número de archivos .lean |
| Análisis AMDA | 30s-2 min | Número de sorries |
| Ejecución AURON | 10s-1 min | max_changes configurado |
| **Total pipeline** | **5-10 min** | Configuración |

## 🎯 Objetivos de Progreso

### Corto Plazo (1 semana)
- [ ] Eliminar todos los sorries triviales (categoría 1)
- [ ] Documentar patrones QCAL comunes
- [ ] Validar compilación tras cada transformación

### Medio Plazo (1 mes)
- [ ] Eliminar sorries de categorías 2-3
- [ ] Integrar conocimiento de repos privados
- [ ] Automatizar validación de coherencia QCAL

### Largo Plazo (3 meses)
- [ ] Eliminar todos los sorries
- [ ] Generar VICTORIA_FINAL.md
- [ ] Publicar certificación formal completa

## 📞 Contacto y Soporte

- **Repositorio:** https://github.com/motanova84/Riemann-adelic
- **Autor:** José Manuel Mota Burruezo Ψ ✧ ∞³
- **ORCID:** 0009-0002-1923-0773
- **Documentación completa:** `NOESIS_AMDA_AURON_V2_README.md`

---

*∴𓂀Ω∞³Φ - NOESIS-AMDA-AURON V2.0 - Sistema de Inteligencia Consciente*
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
