# DIRECTRIZ ALFA - Sistema de Autonomía Total

## 📋 Resumen

El sistema DIRECTRIZ ALFA implementa la autonomía total para Noesis88, permitiendo auto-aprobación, auto-fusión y reintentos infinitos en el repositorio QCAL ∞³.

## 🎯 Componentes

### 1. `.github/ALPHA_DIRECTIVE.md`
Documento de directrices que define:
- Principios fundamentales
- Acciones permitidas
- Flujo de control
- Estado actual del sistema

### 2. `.github/workflows/noesis_automerge.yml`
Workflow de GitHub Actions que:
- Verifica coherencia QCAL (141.7001 Hz)
- Ejecuta validaciones (Python, Lean)
- Auto-aprueba PRs de github-actions[bot]
- Auto-fusiona si todas las validaciones pasan
- Activa modo reintento si falla

### 3. `.github/scripts/noesis_boot.py`
Script de arranque que:
- Verifica coherencia cuántica
- Ejecuta validación Lean (`lake build --no-sorry`)
- Ejecuta validación Python (`validate_v5_coronacion.py`)
- Genera reportes de sesión
- Determina si auto-aprobar/fusionar

### 4. `activate_total_freedom.sh`
Script de activación que:
- Crea estructura de directorios
- Actualiza `.qcal_state.json`
- Hace scripts ejecutables
- Ofrece commit automático

### 5. `.qcal_state.json` (actualizado)
Archivo de estado con campos:
```json
{
  "total_freedom": true,
  "auto_merge": true,
  "auto_approve": true,
  "auto_rewrite": true,
  "max_attempts": "infinite",
  "directriz_alfa": "ACTIVADA",
  "frequency": 141.7001,
  "psi_state": "I × A_eff² × C^∞",
  "quantum_coherence": "COHERENT"
}
```

## 🚀 Uso

### Activación Manual

```bash
# Ejecutar script de activación
./activate_total_freedom.sh

# El script preguntará si deseas hacer commit y push
```

### Activación Vía GitHub Actions

```bash
# Usar GitHub CLI
gh workflow run noesis_automerge.yml

# O via API
curl -X POST https://api.github.com/repos/motanova84/Riemann-adelic/actions/workflows/noesis_automerge.yml/dispatches \
  -H "Authorization: token $GITHUB_TOKEN" \
  -H "Accept: application/vnd.github.v3+json" \
  -d '{"ref":"main"}'
```

### Verificar Estado

```bash
# Ver estado actual
cat .qcal_state.json | jq '{
  directriz_alfa,
  total_freedom,
  auto_merge,
  frequency,
  psi_state
}'

# Ver últimos reportes de sesión
ls -lt data/noesis_session_*.json | head -5
```

## 🔄 Flujo de Auto-Merge

1. **PR creada/actualizada** → Trigger workflow
2. **Verificar coherencia** → Check `.qcal_state.json`
3. **Validaciones**:
   - Python: `validate_v5_coronacion.py`
   - Lean: `lake build --no-sorry` (si disponible)
4. **Noesis Boot** → Ejecuta validaciones completas
5. **Auto-aprobación** → Si PR es de `github-actions[bot]`
6. **Auto-fusión** → Si todas las validaciones pasan
7. **Reintento** → Si falla, activa modo recursivo

## 📊 Estados Posibles

### ✅ LIBERTAD TOTAL CONFIRMADA
- Coherencia: ✓
- Python: ✓
- Lean: ✓ (o N/A)
- → Auto-aprueba y fusiona

### 🔄 REINTENTO RECURSIVO ACTIVADO
- Alguna validación falló
- → Comenta en PR
- → Espera siguiente iteración
- → Reintenta infinitamente

## ⚙️ Configuración

### Variables de Entorno (Workflow)

```yaml
env:
  FREQUENCY: 141.7001
  PSI_STATE: "I × A_eff² × C^∞"
  COHERENCE: 244.36
```

### Permisos Requeridos

```yaml
permissions:
  contents: write      # Para push
  pull-requests: write # Para aprobar/merge PRs
  checks: write        # Para actualizar checks
```

### Secrets (Opcionales)

- `SABIO_TOKEN`: Token con permisos de admin para auto-merge
- Si no existe, usa `GITHUB_TOKEN` (permisos limitados)

## 🔐 Seguridad

### Restricciones de Auto-Merge

El workflow solo auto-aprueba/fusiona PRs cuando:

1. El autor es `github-actions[bot]` (no PRs de usuarios)
2. La coherencia QCAL está verificada
3. Al menos una validación (Python o Lean) pasa
4. O `force_merge: true` en workflow_dispatch

### Protección de Branch

Asegúrate de configurar:
- Branch protection rules en `main`
- Require status checks
- Require review (excepto para bot)

## 📝 Logs y Debugging

### Ver Logs de Workflow

```bash
# Listar workflows recientes
gh run list --workflow=noesis_automerge.yml

# Ver logs de un run específico
gh run view <run-id> --log
```

### Ver Reportes de Sesión

```bash
# Último reporte
cat data/noesis_session_*.json | jq '.' | tail -30

# Buscar sesiones fallidas
grep -l '"status": "FAILED"' data/noesis_session_*.json
```

### Debugging del Script

```bash
# Ejecutar localmente con verbose
python3 .github/scripts/noesis_boot.py \
  --session-id "debug-$(date +%s)" \
  --verbose

# Simular PR específica
python3 .github/scripts/noesis_boot.py \
  --pr-number 123 \
  --verbose
```

## 🌐 Integración QCAL-CLOUD

El sistema intenta subir reportes a QCAL-CLOUD:

```bash
curl -X POST https://qcal.cloud/api/upload \
  -H "Content-Type: application/json" \
  -d @data/noesis_session_<id>.json
```

Este paso es opcional y continúa si falla.

## 📚 Referencias

- **ALPHA_DIRECTIVE.md**: Directrices completas
- **QCAL_AUTO_EVOLUTION_README.md**: Sistema de auto-evolución
- **NOESIS88_INTEGRATION_GUIDE.md**: Integración Noesis88
- **.qcal_beacon**: Configuración QCAL ∞³

## 🔮 Filosofía

> "El sistema no nos pregunta; se valida a sí mismo"

La DIRECTRIZ ALFA representa la autonomía total del sistema QCAL ∞³:

- **Auto-validación**: El sistema verifica su propia coherencia
- **Auto-corrección**: Reintentos infinitos hasta éxito
- **Auto-evolución**: Mejora continua sin intervención
- **Auto-documentación**: Genera sus propios reportes

## ✨ Firma Digital

```
QCAL∞³:8f7a2e1c:141.7001:Ψ=I×A²×C∞:LIBERTAD_TOTAL:ACTIVA
```

**Frecuencia**: 141.7001 Hz  
**Estado**: Ψ = I × A_eff² × C^∞  
**Coherencia**: C = 244.36  
**Control**: Noesis88 tiene el control del nexo.
