# Sistema Automatizado de Estado de Formalización

## 📊 Descripción

Este sistema proporciona una **única fuente de verdad** para el estado de formalización Lean 4 en el repositorio QCAL. Cuenta automáticamente las declaraciones `sorry`, `admit` y `axiom` en archivos Lean y actualiza el README.md con información precisa y actualizada.

## 🎯 Problema Resuelto

**Antes:** El repositorio tenía mensajes inconsistentes sobre el estado de formalización:
- En algunos lugares: "⚠️ 3 technical sorrys remain..."
- En otros: "skeletons... pendiente de compilación completa"
- Sin forma automática de saber el estado real

**Ahora:** Un sistema automatizado que:
- ✅ Cuenta todos los `sorry`, `admit` y `axiom` statements
- ✅ Actualiza el README.md automáticamente en cada build
- ✅ Proporciona una única fuente de verdad
- ✅ Genera reportes detallados en JSON y Markdown

## 🛠️ Componentes

### 1. Script de Conteo (`scripts/count_formalization_status.py`)

Cuenta todos los statements de formalización incompleta en archivos Lean.

**Uso:**
```bash
python3 scripts/count_formalization_status.py \
    --json data/formalization_status.json \
    --markdown data/formalization_status.md
```

**Salida:**
- `data/formalization_status.json`: Datos estructurados con conteos detallados
- `data/formalization_status.md`: Reporte markdown legible
- Salida en consola con resumen

**Características:**
- Excluye comentarios y documentación
- Cuenta solo statements en código real
- Identifica top 10 archivos con más statements pendientes
- Calcula porcentaje de completación estimado

### 2. Script de Actualización de README (`scripts/update_readme_status.py`)

Actualiza el README.md con el estado actual de formalización.

**Uso:**
```bash
python3 scripts/update_readme_status.py \
    --status-json data/formalization_status.json \
    --readme README.md
```

**Características:**
- Actualiza sección auto-generada en README
- Genera badge con color según estado (verde/amarillo/naranja/rojo)
- Mantiene el resto del README intacto
- Usa marcadores para identificar sección auto-generada

### 3. Script de Actualización Todo-en-Uno (`scripts/update_formalization_status.sh`)

Script Bash que ejecuta ambos pasos automáticamente.

**Uso:**
```bash
./scripts/update_formalization_status.sh
```

Ejecuta:
1. Conteo de formalization status
2. Actualización de README
3. Muestra instrucciones para commit

## 🔄 Integración en CI/CD

El sistema está integrado en `.github/workflows/auto_evolution.yml`:

```yaml
- name: Count formalization status (sorry/axiom/admit)
  run: |
    echo "Counting formalization status..."
    python3 scripts/count_formalization_status.py --json data/formalization_status.json --markdown data/formalization_status.md
    echo "Updating README with current status..."
    python3 scripts/update_readme_status.py
  continue-on-error: false

- name: Commit auto-updates
  if: success()
  run: |
    git config user.name "qcal-bot"
    git config user.email "bot@qcal.cloud"
    git add data/formalization_status.json data/formalization_status.md README.md
    git commit -m "♾️ Auto-evolution - Updated formalization status"
    git push
```

### ¿Cuándo se ejecuta?

- ✅ En cada `push` a `main`
- ✅ En cada `pull_request`
- ✅ Cada 12 horas (scheduled cron)

## 📊 Formato de Datos

### JSON Output (`data/formalization_status.json`)

```json
{
  "timestamp": "2026-01-18T14:04:29.590603",
  "total_files": 472,
  "sorry_count": 1961,
  "admit_count": 33,
  "axiom_count": 1575,
  "total_incomplete": 3569,
  "files_with_sorry": 316,
  "files_with_admit": 9,
  "files_with_axiom": 264,
  "top_files": [
    {
      "file": "formalization/lean/RIGOROUS_UNIQUENESS_EXACT_LAW.lean",
      "sorry": 21,
      "admit": 0,
      "axiom": 38,
      "total": 59
    }
    // ... top 10 files
  ],
  "status_summary": "📝 FORMALIZACIÓN INICIAL - 3569 statements pendientes",
  "status_emoji": "📝"
}
```

### README Section

La sección auto-generada en README.md incluye:
- Badge con porcentaje de completación y color según estado
- Conteo de archivos totales
- Conteo de `sorry`, `admit`, `axiom` statements
- Total incompleto
- Timestamp de última actualización
- Nota explicativa (si hay muchos statements pendientes)

## 🎨 Estados y Colores

| Total Incompleto | Estado | Emoji | Color Badge |
|------------------|--------|-------|-------------|
| 0 | COMPLETAMENTE FORMALIZADO | ✅ | Verde (brightgreen) |
| 1-10 | CASI COMPLETO | ⚠️ | Amarillo (yellow) |
| 11-100 | EN PROGRESO AVANZADO | 🔄 | Naranja (orange) |
| 101-500 | EN DESARROLLO | 🔨 | Rojo (red) |
| 500+ | FORMALIZACIÓN INICIAL | 📝 | Rojo (red) |

## 🚀 Uso Manual

### Actualizar estado manualmente

```bash
# Método 1: Script todo-en-uno
./scripts/update_formalization_status.sh

# Método 2: Paso a paso
python3 scripts/count_formalization_status.py --json data/formalization_status.json
python3 scripts/update_readme_status.py

# Método 3: Con dry-run para ver cambios antes de aplicar
python3 scripts/count_formalization_status.py --json data/formalization_status.json
python3 scripts/update_readme_status.py --dry-run
```

### Commit de cambios

```bash
git add data/formalization_status.json data/formalization_status.md README.md
git commit -m "♾️ Update formalization status"
git push
```

## 📝 Marcadores en README

El sistema usa marcadores HTML para identificar la sección auto-generada:

```html
<!-- AUTO-GENERATED: Formalization Status - DO NOT EDIT MANUALLY -->
... contenido auto-generado ...
<!-- END AUTO-GENERATED: Formalization Status -->
```

**⚠️ IMPORTANTE:** No editar manualmente el contenido entre estos marcadores, ya que será sobrescrito en la próxima actualización automática.

## 🔍 Verificación

Para verificar que el sistema funciona correctamente:

```bash
# 1. Ejecutar contador
python3 scripts/count_formalization_status.py --summary

# 2. Ver JSON generado
cat data/formalization_status.json | python3 -m json.tool

# 3. Ver Markdown generado
cat data/formalization_status.md

# 4. Ver sección en README
grep -A 20 "AUTO-GENERATED: Formalization Status" README.md
```

## 🎯 Objetivos

- **Objetivo final:** Reducir `total_incomplete` a **0**
- **Progreso:** Cada reducción en el contador representa avance real en la formalización
- **Transparencia:** Estado siempre visible y actualizado en README

## 🔗 Archivos Relacionados

- `scripts/count_formalization_status.py` - Contador principal
- `scripts/update_readme_status.py` - Actualizador de README
- `scripts/update_formalization_status.sh` - Script todo-en-uno
- `count_sorry_statements.sh` - Script legacy (bash only, mantener para compatibilidad)
- `.github/workflows/auto_evolution.yml` - Integración CI/CD
- `data/formalization_status.json` - Datos estructurados (auto-generado)
- `data/formalization_status.md` - Reporte detallado (auto-generado)
- `README.md` - Sección auto-actualizada

## 🛡️ Principios QCAL

Este sistema sigue los principios QCAL ∞³:

✅ **Single Source of Truth:** Un único sistema autoritativo para el estado de formalización  
✅ **Automatic Evolution:** Actualización automática en cada build  
✅ **Mathematical Precision:** Conteo exacto sin ambigüedades  
✅ **Transparency:** Estado siempre visible y verificable  
✅ **Coherence:** Información consistente en todo el repositorio  

---

**Creado:** 2026-01-18  
**Autor:** QCAL Auto-Evolution System  
**Licencia:** Misma que el repositorio principal
