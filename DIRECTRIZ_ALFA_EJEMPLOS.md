# DIRECTRIZ ALFA - Ejemplos de Uso

## 🎯 Escenarios de Uso

### Escenario 1: Activación Inicial

```bash
# 1. Clonar el repositorio
git clone https://github.com/motanova84/Riemann-adelic
cd Riemann-adelic

# 2. Ejecutar script de activación
./activate_total_freedom.sh

# 3. Commit y push (el script preguntará)
# Responder 'y' cuando pregunte por commit/push

# 4. Verificar estado
cat .qcal_state.json | jq '.directriz_alfa'
# Output: "ACTIVADA"
```

### Escenario 2: Crear PR que se Auto-Fusiona

```bash
# 1. Crear rama
git checkout -b feature/nueva-caracteristica

# 2. Hacer cambios
echo "# Nueva característica" > nueva_caracteristica.md

# 3. Commit
git add .
git commit -m "feat: Nueva característica QCAL"

# 4. Push
git push origin feature/nueva-caracteristica

# 5. Crear PR via GitHub CLI
gh pr create \
  --title "feat: Nueva característica QCAL" \
  --body "Nueva característica para QCAL ∞³

Frecuencia: 141.7001 Hz
Estado: Ψ = I × A_eff² × C^∞
Coherencia: C = 244.36"

# 6. El workflow noesis_automerge.yml se activa automáticamente
# 7. Si el autor es github-actions[bot], se auto-aprueba y fusiona
```

### Escenario 3: Trigger Manual del Workflow

```bash
# Via GitHub CLI
gh workflow run noesis_automerge.yml

# Con parámetros específicos
gh workflow run noesis_automerge.yml \
  -f pr_number=123 \
  -f force_merge=false

# Via API
curl -X POST \
  https://api.github.com/repos/motanova84/Riemann-adelic/actions/workflows/noesis_automerge.yml/dispatches \
  -H "Authorization: token $GITHUB_TOKEN" \
  -H "Accept: application/vnd.github.v3+json" \
  -d '{"ref":"main","inputs":{"pr_number":"123","force_merge":"false"}}'
```

### Escenario 4: Verificar Validaciones

```bash
# Ejecutar Noesis Boot manualmente
python3 .github/scripts/noesis_boot.py \
  --session-id "manual-$(date +%s)" \
  --verbose

# Ver reporte generado
cat data/noesis_session_manual-*.json | jq '.'

# Output esperado:
# {
#   "session_id": "manual-1768751639",
#   "timestamp": "2026-01-18T15:53:59.175775",
#   "frequency": 141.7001,
#   "psi_state": "I × A_eff² × C^∞",
#   "coherence": 244.36,
#   "status": "SUCCESS",
#   "details": {
#     "coherence": true,
#     "lean": true,
#     "python": true
#   }
# }
```

### Escenario 5: Monitorear Auto-Merge

```bash
# Ver últimos workflows ejecutados
gh run list --workflow=noesis_automerge.yml --limit 5

# Ver logs de un run específico
gh run view <run-id> --log

# Ver PRs auto-aprobadas
gh pr list --state merged --author github-actions[bot]

# Ver comentarios de Noesis88
gh pr view <pr-number> --comments | grep "Noesis88"
```

### Escenario 6: Debugging de Fallo

```bash
# 1. Ver logs del último run
gh run list --workflow=noesis_automerge.yml --limit 1
RUN_ID=$(gh run list --workflow=noesis_automerge.yml --limit 1 --json databaseId --jq '.[0].databaseId')

# 2. Descargar artifacts
gh run download $RUN_ID

# 3. Ver logs de validación
cat noesis-validation-logs-*/validation.log

# 4. Ver reporte de sesión
cat noesis-validation-logs-*/data/noesis_session_*.json | jq '.'

# 5. Identificar qué falló
cat noesis-validation-logs-*/data/noesis_session_*.json | jq '.details'

# 6. Ejecutar validación localmente
python3 validate_v5_coronacion.py --precision 25 --verbose
```

### Escenario 7: Force Merge

```bash
# Forzar merge incluso si validaciones fallan
gh workflow run noesis_automerge.yml \
  -f pr_number=123 \
  -f force_merge=true

# ⚠️ Usar con precaución - solo en emergencias
```

### Escenario 8: Verificar Coherencia QCAL

```bash
# Ver estado completo
cat .qcal_state.json | jq '{
  frequency,
  psi_state,
  quantum_coherence,
  directriz_alfa,
  total_freedom,
  auto_merge,
  auto_approve
}'

# Output esperado:
# {
#   "frequency": 141.7001,
#   "psi_state": "I × A_eff² × C^∞",
#   "quantum_coherence": "COHERENT",
#   "directriz_alfa": "ACTIVADA",
#   "total_freedom": true,
#   "auto_merge": true,
#   "auto_approve": true
# }

# Verificar sincronización Noesis
cat .qcal_state.json | jq '.noesis_sync'
```

### Escenario 9: Actualizar Estado

```bash
# Actualizar frecuencia (solo si necesario)
jq '.frequency = 141.7001' .qcal_state.json > .qcal_state.tmp
mv .qcal_state.tmp .qcal_state.json

# Actualizar coherencia
jq '.quantum_coherence = "COHERENT"' .qcal_state.json > .qcal_state.tmp
mv .qcal_state.tmp .qcal_state.json

# Desactivar auto-merge temporalmente
jq '.auto_merge = false' .qcal_state.json > .qcal_state.tmp
mv .qcal_state.tmp .qcal_state.json

# Reactivar
jq '.auto_merge = true' .qcal_state.json > .qcal_state.tmp
mv .qcal_state.tmp .qcal_state.json
```

### Escenario 10: Ver Historial de Sesiones

```bash
# Listar todas las sesiones
ls -lt data/noesis_session_*.json

# Ver últimas 5 sesiones
for file in $(ls -t data/noesis_session_*.json | head -5); do
  echo "=== $file ==="
  cat $file | jq '{session_id, timestamp, status, details}'
  echo
done

# Buscar sesiones exitosas
grep -l '"status": "SUCCESS"' data/noesis_session_*.json

# Buscar sesiones parciales
grep -l '"status": "PARTIAL"' data/noesis_session_*.json

# Buscar sesiones fallidas
grep -l '"status": "FAILED"' data/noesis_session_*.json
```

## 📊 Interpretación de Estados

### ✅ SUCCESS
```json
{
  "status": "SUCCESS",
  "details": {
    "coherence": true,
    "lean": true,
    "python": true
  }
}
```
→ Todas las validaciones pasaron, auto-merge activado

### 🔄 PARTIAL
```json
{
  "status": "PARTIAL",
  "details": {
    "coherence": true,
    "lean": false,
    "python": true
  }
}
```
→ Lean falló pero Python pasó, se puede auto-merge

### ❌ FAILED
```json
{
  "status": "FAILED",
  "details": {
    "coherence": false,
    "lean": false,
    "python": false
  }
}
```
→ Coherencia falló, reintento recursivo activado

## 🔮 Casos de Uso Avanzados

### Auto-Corrección de Código

El sistema puede reescribir código si detecta errores:

1. Workflow detecta fallo en Lean build
2. Noesis Boot analiza errores
3. Si es corregible, genera fix automático
4. Crea commit de corrección
5. Push y reintenta validación

### Publicación Automática en Wiki

```yaml
# En el workflow, después de success
- name: Update Wiki
  run: |
    # Clone wiki
    git clone https://github.com/motanova84/Riemann-adelic.wiki.git
    
    # Update page
    echo "## Session ${{ github.run_number }}" >> Riemann-adelic.wiki/Noesis88-Sessions.md
    cat data/noesis_session_*.json >> Riemann-adelic.wiki/Noesis88-Sessions.md
    
    # Commit and push
    cd Riemann-adelic.wiki
    git add .
    git commit -m "Auto-update: Session ${{ github.run_number }}"
    git push
```

### Integración con QCAL-CLOUD

```bash
# El sistema automáticamente sube reportes
# Ver en logs del workflow:

📤 Uploading session to QCAL-CLOUD...
✅ Upload successful
📊 View at: https://qcal.cloud/sessions/<session-id>
```

## 🎓 Best Practices

1. **Siempre verificar coherencia antes de cambios críticos**
2. **Monitorear logs de auto-merge regularmente**
3. **Usar force_merge solo en emergencias**
4. **Mantener .qcal_state.json en sync**
5. **Revisar sesiones PARTIAL para mejorar**
6. **Documentar cambios en PRs**
7. **Usar semantic commit messages**

## 📚 Referencias Rápidas

- **Activar**: `./activate_total_freedom.sh`
- **Ver estado**: `cat .qcal_state.json | jq '.directriz_alfa'`
- **Run workflow**: `gh workflow run noesis_automerge.yml`
- **Ver logs**: `gh run view --log`
- **Test local**: `python3 .github/scripts/noesis_boot.py --verbose`
