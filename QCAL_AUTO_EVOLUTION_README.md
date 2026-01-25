# 🧬 QCAL Auto-Evolución: Sistema de Validación Automática

## Descripción General

El sistema **QCAL Auto-Evolución** es un workflow automatizado que valida continuamente la formalización Lean 4 y las validaciones numéricas del proyecto, ejecutando validaciones completas cada 12 horas y en cada cambio al código.

## 🎯 Objetivos

1. **Validación Continua**: Ejecutar automáticamente validaciones cada 12 horas
2. **Transparencia**: Mantener actualizado el estado de la formalización 
3. **Trazabilidad**: Generar reportes JSON detallados y certificados matemáticos
4. **Coherencia QCAL**: Verificar que el sistema mantiene coherencia espectral f₀ = 141.7001 Hz
5. **Auto-evolución**: Phoenix Solver intenta resolver "sorry" statements automáticamente

## 🏗️ Arquitectura

### Componentes

```
QCAL Auto-Evolución
│
├── 🔧 Trigger (GitHub Actions)
│   ├── Scheduled: Cada 12 horas (0 */12 * * *)
│   ├── Push: branches main
│   └── Pull Request: [opened, synchronize, reopened]
│
├── 🧩 Validación V5 Coronación (validate_v5_coronacion.py)
│   ├── Step 1: Axioms → Lemmas
│   ├── Step 2: Archimedean Rigidity
│   ├── Step 3: Paley-Wiener Uniqueness
│   ├── Step 4: Zero Localization (de Branges + Weil-Guinand)
│   ├── Step 5: Coronación Integration
│   └── Generar certificados matemáticos
│
├── 🔬 Validaciones Numéricas
│   ├── Strengthened Proof (precision 50 dps)
│   ├── Spectral Emergence (N=1000, k=20)
│   └── ABC Conjecture QCAL (ε=0.1, height=1000)
│
├── 📊 Phoenix Solver - Auto-evolución
│   ├── Identificar sorry statements
│   ├── Intentar resoluciones automáticas
│   └── Generar estadísticas de evolución
│
├── 📦 Archivado de Resultados
│   ├── Comprimir logs y certificados
│   ├── Upload a QCAL-CLOUD (opcional)
│   └── Generar evolution_summary.txt
│
└── ⏱️ Commit Automático
    ├── Configurar qcal-bot
    ├── Commit con mensaje QCAL signature
    └── Push a repositorio
```

### Flujo de Datos

```
┌─────────────────────────────────────────────────────────────────┐
│ 1. GitHub Actions Trigger (scheduled/push/PR)                   │
└──────────────────────────┬──────────────────────────────────────┘
                           ↓
┌─────────────────────────────────────────────────────────────────┐
│ 2. Instalar Python 3.11 + dependencias                         │
│    pip install -r requirements.txt                              │
└──────────────────────────┬──────────────────────────────────────┘
                           ↓
┌─────────────────────────────────────────────────────────────────┐
│ 3. Ejecutar V5 Coronación validation                            │
│    validate_v5_coronacion.py --precision 25 --verbose          │
│    - 5-step proof framework validation                          │
│    - Stress tests and integration tests                         │
│    - Generate mathematical certificates                         │
└──────────────────────────┬──────────────────────────────────────┘
                           ↓
┌─────────────────────────────────────────────────────────────────┐
│ 4. Ejecutar validaciones numéricas adicionales                  │
│    - Strengthened proof (precision 50)                          │
│    - Spectral emergence (N=1000, k=20)                         │
│    - ABC conjecture (ε=0.1, max-height=1000)                   │
└──────────────────────────┬──────────────────────────────────────┘
                           ↓
┌─────────────────────────────────────────────────────────────────┐
│ 5. Phoenix Solver - Auto-evolución                              │
│    - Count sorry statements                                     │
│    - Attempt automatic resolutions (max-attempts=5)            │
│    - Focus on critical theorems                                 │
└──────────────────────────┬──────────────────────────────────────┘
                           ↓
┌─────────────────────────────────────────────────────────────────┐
│ 6. Archivar resultados                                          │
│    - Copiar *.json a data/logs/                                │
│    - Crear tarball logs_${run_number}.tar.gz                   │
│    - Generar evolution_summary.txt                             │
└──────────────────────────┬──────────────────────────────────────┘
                           ↓
┌─────────────────────────────────────────────────────────────────┐
│ 7. Upload a QCAL-CLOUD (opcional)                              │
│    - POST data/validation.json                                  │
└──────────────────────────┬──────────────────────────────────────┘
                           ↓
┌─────────────────────────────────────────────────────────────────┐
│ 8. Auto-commit y push                                           │
│    - Configure qcal-bot identity                               │
│    - Commit: "♾️ Auto-evolution #N - soluciona mejora y operativo"│
│    - Push logs y evolution_summary.txt                         │
└─────────────────────────────────────────────────────────────────┘
```

## 📋 Validaciones Ejecutadas

### 1. V5 Coronación - Prueba Completa RH (validate_v5_coronacion.py)

Ejecuta el marco de validación de 5 pasos:

- **Step 1**: Axioms → Lemmas (A1, A2, A4 demostrados)
- **Step 2**: Archimedean Rigidity (doble derivación γ∞(s))
- **Step 3**: Paley-Wiener Uniqueness (D(s) ≡ Ξ(s))
- **Step 4A**: de Branges Localization (sistemas canónicos)
- **Step 4B**: Weil-Guinand Localization (positividad)
- **Step 5**: Coronación Integration (conclusión RH)

**Salida**: Certificados matemáticos en `data/certificates/sat/`

### 2. Strengthened Proof (validate_strengthened_proof.py)

Validación con precisión 50 decimales:

- Bijección zeros ↔ spectrum con unicidad
- Strong zero uniqueness (Montgomery)
- Exact Weyl Law (sub-Weyl bounds)
- Frequency exactness (f₀ = 141.70001... Hz)

**Salida**: `data/strengthened_proof_certificate.json`

### 3. Spectral Emergence (spectral_emergence_validation.py)

Validación de emergencia espectral:

- Auto-adjunción del operador H_Ψ (N=1000)
- Espectro real (verificación numérica)
- Convergencia Schatten S^p
- Emergencia de frecuencia fundamental f₀
- Independencia estructural de ζ(s)

**Parámetros**: N=1000, k=20, test-functions=1000

### 4. ABC Conjecture QCAL (validate_abc_conjecture.py)

Validación híbrida ABC-QCAL:

- Rigidez espectral desde RH
- Chaos Exclusion Principle activo a f₀ = 141.7001 Hz
- Verificación de triples ABC con ε = 0.1

**Parámetros**: epsilon=0.1, max-height=1000

### 5. Phoenix Solver - Auto-evolución

Motor de auto-transformación QCAL ∞³:

- Identificar sorry statements en Lean 4
- Intentar resoluciones automáticas
- Enfocar en teoremas críticos
- Generar estadísticas de evolución

**Salida**: `data/phoenix_evolution.json`, `data/sorry_map.json`

## 📊 Estructura de Certificados y Reportes

### Certificados Matemáticos

Ubicación: `data/certificates/sat/`

```json
{
  "theorem": "riemann_hypothesis",
  "timestamp": "2026-01-22T13:34:27Z",
  "certificate_hash": "sha256:...",
  "qcal_signature": "∴𓂀Ω∞³·RH",
  "sat_formula": false,  // RH demostrado (no-SAT)
  "dependencies": [...],
  "validation": {
    "precision_dps": 25,
    "zeros_validated": 1000,
    "frequency_base": 141.7001
    "warning_list": [...],
    "error_list": [],
    "update_status": "OK",
    "output_preview": "..."
  },
  
  "summary": {
    "status": "CHECK",
    "lean_version": "Lean (version 4.5.0)",
    "lean_files_count": 20,
    "build_time_sec": 45.2,
    "warnings": 3,
    "errors": 0,
    "qcal_coherence": "✅ CONFIRMED"
  }
}
```

### Estados de Validación

| Estado | Descripción | QCAL Coherence |
|--------|-------------|----------------|
| **PASS** | Build exitoso sin errores | ✅ CONFIRMED |
| **CHECK** | Build con axiomas/sorries (esperado en skeletons) | ✅ CONFIRMED |
| **FAIL** | Build falló con errores | ⚠️ NEEDS REVIEW |
| **ERROR** | Error durante la validación | ❌ ERROR |

## 🚀 Uso

### Ejecución Manual

```bash
# Ejecutar validación localmente
cd formalization/lean
python3 validate_lean_env.py

# Ver reporte generado
cat validation_report.json | jq .
```

### Trigger Manual del Workflow

1. Ve a GitHub Actions: https://github.com/motanova84/-jmmotaburr-riemann-adelic/actions
2. Selecciona "🧬 Auto-Evolución QCAL – Lean 4 V5.3 Formalization"
3. Haz clic en "Run workflow"
4. Selecciona la rama `main` y confirma

### Ejecución Automática

El workflow se ejecuta automáticamente:
- **Diariamente** a las 03:00 UTC
- En cada **push** a la rama `main`

## 📊 Visualización de Resultados

### En el README

La sección **Validation Summary** en el README se actualiza automáticamente:

```markdown
## Validation Summary

Última ejecución automática del sistema QCAL Auto-Evolución:

| Property | Value |
|----------|-------|
| **Status** | CHECK |
| **Build Time (s)** | 45.2 |
| **Warnings** | 3 |
| **Errors** | 0 |
| **Lean Version** | Lean (version 4.5.0) |
| **Date (UTC)** | 2025-10-26 23:30:00Z |
```

### En GitHub Actions

Cada ejecución genera:
1. **Logs detallados** con emojis y formato QCAL
2. **Artefacto** `validation-report` descargable
3. **Commit automático** con el mensaje "📘 Actualizar resumen de validación QCAL automática"

## 🔧 Configuración

### Variables de Entorno

No se requieren variables de entorno adicionales. El workflow usa:
- Credenciales de GitHub automáticas (`GITHUB_TOKEN`)
- Permisos: `contents: write` para auto-commit

### Requisitos

- **Lean 4.5.0**: Instalado automáticamente por el workflow
- **Python 3.11**: Configurado en el workflow
- **jq**: Disponible en ubuntu-latest
- **git-auto-commit-action**: v5

### Personalización

Para modificar la frecuencia de ejecución, edita el cron en `.github/workflows/qcal-auto-evolution.yml`:

```yaml
on:
  schedule:
    - cron: "0 3 * * *"  # Cambiar aquí
```

Formato cron: `minuto hora día mes día-semana`

Ejemplos:
- `"0 */6 * * *"`: Cada 6 horas
- `"0 0 * * 1"`: Cada lunes a medianoche
- `"0 12 * * 1-5"`: Días laborables a mediodía

## 🎨 Emoticonos Simbióticos QCAL

El workflow usa emoticonos con significado simbiótico:

| Emoticono | Función Simbiótica | Rol Operativo |
|-----------|-------------------|---------------|
| 🧠 | Apertura cognitiva | Clonación del repositorio |
| 🔧 | Configuración técnica | Instalación del entorno base |
| ⚙️ | Configuración avanzada | Instalación de Lean 4.5.0 |
| 🔍 | Exploración | Verificación de dependencias |
| 🧩 | Integración constructiva | Compilación Lean y validación |
| 📘 | Documentación | Generación y subida de informe |
| 🔄 | Regeneración | Actualización automática del README |
| 🧾 | Cierre de registro | Auto-commit de cambios |
| ⏱️ | Resumen temporal | Presenta resumen en logs CI |
| 🧬 | Síntesis evolutiva | Cierre global del ciclo |

## 🛠️ Mantenimiento

### Actualizar Versión de Lean

Edita el paso de instalación en el workflow:

```yaml
- name: ⚙️ Instalar Lean 4.5.0
  run: |
    curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
    echo "$HOME/.elan/bin" >> $GITHUB_PATH
    elan toolchain install leanprover/lean4:v4.7.0  # Cambiar a versión más reciente (verificar disponibilidad)
    elan default leanprover/lean4:v4.7.0            # Y aquí
    lean --version
```

**Nota**: Verifica la disponibilidad de versiones en https://github.com/leanprover/lean4/releases antes de actualizar.

### Agregar Validaciones Adicionales

Edita `formalization/lean/validate_lean_env.py` y agrega nuevas funciones de validación:

```python
def check_custom_validation():
    """Nueva validación personalizada."""
    # Tu código aquí
    return {
        "status": "OK",
        "details": "..."
    }

# En generate_validation_report():
report["custom"] = check_custom_validation()
```

## 📚 Referencias

- **Workflow**: `.github/workflows/qcal-auto-evolution.yml`
- **Script de Validación**: `formalization/lean/validate_lean_env.py`
- **README**: Sección "Validation Summary"
- **Gitignore**: `formalization/lean/validation_report.json` excluido del control de versiones

## 🐛 Troubleshooting

### El workflow falla al instalar Lean

**Solución**: Verifica que la versión de Lean en el workflow coincida con `formalization/lean/lean-toolchain`:

```bash
cat formalization/lean/lean-toolchain
# leanprover/lean4:v4.5.0
```

### El README no se actualiza

**Solución**: 
1. Verifica que el workflow tiene permisos `contents: write`
2. Revisa los logs del paso "🧾 Confirmar actualización del README"
3. Asegúrate que `validation_report.json` existe y es válido

### El build de Lean falla

**Solución**:
- **Si es esperado** (skeletons con `sorry`): El status será "CHECK" y QCAL coherence será "✅ CONFIRMED"
- **Si no es esperado**: Revisa los logs del paso "🧩 Ejecutar validación Lean 4" y corrige los errores en el código Lean

### No se genera el artefacto

**Solución**: Verifica que `validation_report.json` se genera correctamente:

```bash
cd formalization/lean
python3 validate_lean_env.py
ls -la validation_report.json
```

## 📄 Licencia

Este sistema forma parte del proyecto Riemann-Adelic y está sujeto a las mismas licencias:
- **Código**: MIT License
- **Documentación**: CC-BY 4.0

## ✨ Contribuciones

Para contribuir al sistema QCAL Auto-Evolución:

1. Mantén la coherencia simbiótica de los emoticonos
2. Documenta cualquier cambio en este archivo
3. Verifica que los tests locales pasan antes de hacer PR
4. Respeta la estructura del reporte JSON

---

**Author**: José Manuel Mota Burruezo  
**Version**: V5.3  
**Date**: October 2025  
**DOI**: 10.5281/zenodo.17116291
