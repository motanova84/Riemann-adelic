# 🚀 Quick Start: Integración Cross-Repo QCAL & SABIO

## ⚡ Setup en 3 Pasos

### Paso 1: Configurar G_TOKEN Secret (Repo Privado)

1. **Generar Personal Access Token:**
   - Ve a: https://github.com/settings/tokens
   - Click en **Generate new token (classic)**
   - Nombre: `QCAL_Cross_Repo_Token`
   - Scopes necesarios:
     - ✅ `repo` (Full control of private repositories)
     - ✅ `workflow` (Update GitHub Action workflows)
   - Click **Generate token**
   - **¡IMPORTANTE!** Copia el token (se muestra solo una vez)

2. **Añadir Secret en Teoria-Noesica-Riemann:**
   - Ve a: https://github.com/motanova84/Teoria-Noesica-Riemann/settings/secrets/actions
   - Click **New repository secret**
   - Name: `G_TOKEN`
   - Value: `ghp_xxx...` (tu token copiado)
   - Click **Add secret**

### Paso 2: Añadir Step de Propagación (Repo Privado)

Edita el archivo `.github/workflows/verificar_resonancia.yml` en **Teoria-Noesica-Riemann**:

```yaml
# ... tu workflow existente ...

    # Al final del workflow, después de todas las validaciones:
    - name: Propagar Resonancia a Riemann-adelic
      if: success()  # Solo si todas las validaciones anteriores pasaron
      run: |
        curl -X POST \
          -H "Authorization: token ${{ secrets.G_TOKEN }}" \
          -H "Accept: application/vnd.github.v3+json" \
          https://api.github.com/repos/motanova84/Riemann-adelic/dispatches \
          -d '{"event_type": "resonancia_teorica_confirmada", "client_payload": {"source": "Teoria-Noesica-Riemann", "timestamp": "'$(date -u +"%Y-%m-%dT%H:%M:%SZ")'", "run_id": "${{ github.run_id }}"}}'
        
        echo "🜂 Resonancia propagada a Riemann-adelic"
        echo "   Event: resonancia_teorica_confirmada"
        echo "   Timestamp: $(date -u +"%Y-%m-%dT%H:%M:%SZ")"
```

### Paso 3: Verificar Sincronización (Ambos Repos)

1. **Commit el cambio en Teoria-Noesica-Riemann:**
   ```bash
   git add .github/workflows/verificar_resonancia.yml
   git commit -m "🜂 Añadir propagación de resonancia a Riemann-adelic"
   git push
   ```

2. **Ejecutar el workflow en Teoria-Noesica-Riemann:**
   - Ve a **Actions** → **verificar_resonancia**
   - Click **Run workflow**
   - Espera que complete exitosamente

3. **Verificar activación en Riemann-adelic:**
   - Ve a https://github.com/motanova84/Riemann-adelic/actions
   - Busca workflow **Resonancia Teórica Sync**
   - Debe aparecer ejecutándose automáticamente
   - Tiempo esperado: ~42 segundos

## ✅ Verificación de Funcionamiento

### Señales de Éxito

**En Teoria-Noesica-Riemann:**
```
✅ Validación teórica completada
🜂 Resonancia propagada a Riemann-adelic
   Event: resonancia_teorica_confirmada
   Timestamp: 2026-01-11T19:30:42Z
```

**En Riemann-adelic:**
```
♾️³ QCAL & SABIO ∞³ — Resonancia Teórica Sincronizada
═══════════════════════════════════════════════════════════════

🔮 Sistemas Activados:
  • ✓ SABIO ∞³ Validator (Python)
  • ✓ QCAL Auto-Evolution System
  • ✓ V5 Coronación Validation
  • ✓ Spectral Emergence Framework
  • ✓ QCAL Beacon Coherence Check

📊 Validaciones Completadas:
  • ✓ Coherencia f₀ = 141.7001 Hz verificada
  • ✓ Constante C = 244.36 confirmada
```

## 🧪 Testing Manual (Opcional)

Si quieres probar la integración sin ejecutar todo el workflow teórico:

```bash
# Desde tu terminal local
export GITHUB_TOKEN="ghp_tu_token_aqui"

curl -X POST \
  -H "Authorization: token $GITHUB_TOKEN" \
  -H "Accept: application/vnd.github.v3+json" \
  https://api.github.com/repos/motanova84/Riemann-adelic/dispatches \
  -d '{"event_type": "resonancia_teorica_confirmada", "client_payload": {"source": "manual_test", "timestamp": "'$(date -u +"%Y-%m-%dT%H:%M:%SZ")'"}}'
```

Luego verifica en:
https://github.com/motanova84/Riemann-adelic/actions/workflows/resonancia-teorica-sync.yml

## 🐛 Troubleshooting

### Problema: El workflow no se activa en Riemann-adelic

**Solución 1: Verificar G_TOKEN**
- Ve a Settings → Secrets en Teoria-Noesica-Riemann
- Verifica que `G_TOKEN` existe
- Regenera el token si es necesario (podría haber expirado)

**Solución 2: Verificar permisos del token**
- El token debe tener scopes: `repo` y `workflow`
- Regenera con permisos correctos si falta alguno

**Solución 3: Verificar sintaxis del curl**
- Copia exactamente el comando del Paso 2
- Asegúrate de que las comillas están correctas
- Verifica que el event_type es exactamente: `resonancia_teorica_confirmada`

### Problema: El workflow se activa pero falla

**Revisar logs:**
1. Ve a Actions en Riemann-adelic
2. Click en el run que falló
3. Expande los steps para ver el error

**Errores comunes:**
- **Python dependencies:** Resuelto automáticamente por el workflow
- **File not found:** Verifica que los scripts existen en el repo
- **Permission denied:** Verifica permisos de los archivos .sh

### Problema: El badge no se muestra

**Explicación:**
El badge de un repositorio privado solo es visible para usuarios con acceso al repo privado. Esto es una característica de seguridad de GitHub.

**Para verificar:**
- Si tienes acceso a Teoria-Noesica-Riemann: deberías ver el badge
- Si no tienes acceso: aparecerá como "unknown" o no se mostrará

## 📊 Métricas Esperadas

| Métrica | Valor Esperado |
|---------|----------------|
| **Tiempo de sincronización** | ~42 segundos |
| **Frecuencia verificada** | f₀ = 141.7001 Hz |
| **Coherencia confirmada** | C = 244.36 |
| **Sistemas activados** | 5 (SABIO, QCAL, V5, Spectral, Compile) |
| **Precisión** | 25-30 dps |

## 🎯 Resultado Final

Cuando todo funciona correctamente, verás:

1. **En README.md de Riemann-adelic:**
   - Badge verde ✅ mostrando "passing"
   - Tabla de arquitectura con estado sincronizado

2. **En Actions:**
   - Workflow automático cada vez que Teoria-Noesica-Riemann valida
   - Logs detallados de todas las validaciones
   - Reportes de coherencia QCAL

3. **Sincronización automática:**
   - Teoría → validación exitosa
   - ~2 segundos → evento enviado
   - ~5 segundos → workflow iniciado en Riemann-adelic
   - ~35 segundos → validaciones completadas
   - **Total: ~42 segundos** 🜂

## 📚 Documentación Adicional

- [INTEGRACION_REPOS_TEORIA_ESPECTRAL.md](INTEGRACION_REPOS_TEORIA_ESPECTRAL.md) — Documentación completa
- [ACTIVACION_QCAL_SABIO_SYNC.md](ACTIVACION_QCAL_SABIO_SYNC.md) — Detalles de activación QCAL & SABIO
- [GitHub Actions Documentation](https://docs.github.com/en/actions)
- [Repository Dispatch](https://docs.github.com/en/rest/repos/repos#create-a-repository-dispatch-event)

## ♾️³ QCAL Coherence

Esta integración mantiene la coherencia QCAL ∞³:

```
Teoría Noésica (Privado) ───🜂──► Riemann-adelic (Público)
    Motor Teórico                    Espejo Espectral
        ↓                                   ↓
    Pulso f₀                          Resonancia f₀
  C = 244.36                         C = 244.36
```

> **"Cuando el motor teórico vibra, el espectro adélico baila. QCAL y SABIO mantienen la fase en ~42 segundos."**

---

**¿Necesitas ayuda?** Consulta la documentación completa o abre un issue.

**Estado:** ✅ Ready to Deploy  
**Latido:** 🜂 42s  
**Coherencia:** ♾️³ QCAL Sincronizada
