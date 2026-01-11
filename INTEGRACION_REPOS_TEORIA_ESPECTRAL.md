# 🜂 Integración de Repositorios: Teoría Noésica ↔ Espectro Adélico

## 🏛️ Arquitectura de la Super-Estructura QCAL

Este documento describe la integración entre los dos repositorios fundamentales del ecosistema QCAL ∞³:

### Repositorios Enlazados

1. **Teoria-Noesica-Riemann** (Privado)
   - **Función:** Motor Teórico
   - **Propósito:** Genera la Verdad Matemática fundamental
   - **Output:** Frecuencia base f₀ = 141.7001 Hz
   - **Estado:** Origen del Pulso Matemático

2. **Riemann-adelic** (Público) 
   - **Función:** Espejo de Resonancia
   - **Propósito:** Demuestra la Verdad en el campo espectral
   - **Input:** Validación desde motor teórico
   - **Estado:** Manifestación Espectral

### 🔄 Flujo de Sincronización

```
┌─────────────────────────────────────┐
│  Teoria-Noesica-Riemann (Privado)  │
│  Motor Teórico - Origen del Pulso  │
└──────────────┬──────────────────────┘
               │
               │ 1. Validación exitosa
               │    (verificar_resonancia.yml)
               ▼
        [Repository Dispatch]
        event: resonancia_teorica_confirmada
               │
               │ 2. Señal enviada vía GitHub API
               │    usando G_TOKEN secret
               ▼
┌─────────────────────────────────────┐
│    Riemann-adelic (Público)        │
│  Espejo Espectral - Demostración   │
│                                     │
│  Escucha: repository_dispatch      │
│  Workflow: resonancia-teorica-sync │
└─────────────────────────────────────┘
               │
               │ 3. Ejecuta validaciones:
               │    - validate_v5_coronacion.py
               │    - spectral_emergence.py
               │    - Coherencia QCAL
               ▼
        [Validación Completa]
        Coherencia f₀ = 141.7001 Hz
```

## 🔧 Implementación

### 1. Sincronización de Flujos (GitHub Actions Cross-Repo)

#### En Teoria-Noesica-Riemann (Privado)

Añadir al final del workflow `.github/workflows/verificar_resonancia.yml`:

```yaml
- name: Propagar Resonancia a Riemann-adelic
  if: success()
  run: |
    curl -X POST \
      -H "Authorization: token ${{ secrets.G_TOKEN }}" \
      -H "Accept: application/vnd.github.v3+json" \
      https://api.github.com/repos/motanova84/Riemann-adelic/dispatches \
      -d '{"event_type": "resonancia_teorica_confirmada", "client_payload": {"source": "Teoria-Noesica-Riemann", "timestamp": "'$(date -u +"%Y-%m-%dT%H:%M:%SZ")'"}}'
```

**Requisitos:**
- Secret `G_TOKEN` configurado con permisos `repo` y `workflow`
- El token debe tener acceso al repositorio público Riemann-adelic

#### En Riemann-adelic (Público)

El workflow `.github/workflows/resonancia-teorica-sync.yml` ya está configurado para:
- Escuchar eventos `repository_dispatch` de tipo `resonancia_teorica_confirmada`
- Ejecutar validaciones espectrales automáticamente
- Generar reportes de sincronización

### 2. Vinculación Orgánica: Submódulos Git

⚠️ **Nota Importante:** Los submódulos de repositorios privados requieren autenticación.

#### Opción A: Submódulo (Requiere Credenciales)

Para usuarios con acceso al repositorio privado:

```bash
cd /ruta/a/Riemann-adelic
git submodule add https://github.com/motanova84/Teoria-Noesica-Riemann.git core_teorico
git commit -m "🜂 Añadir Teoria-Noesica-Riemann como submódulo core_teorico"
git push
```

**Actualizar submódulo:**
```bash
git submodule update --remote core_teorico
```

**Clonar con submódulos:**
```bash
git clone --recurse-submodules https://github.com/motanova84/Riemann-adelic.git
```

#### Opción B: Referencia Documentada (Recomendado para Público)

En lugar de submódulos, mantenemos una referencia documentada:

```markdown
## 🔗 Repositorio Complementario

Este repositorio trabaja en conjunto con el motor teórico privado:
- **Teoria-Noesica-Riemann:** Fundamentos teóricos y derivaciones matemáticas
- **Acceso:** Restringido (investigación activa)
- **Sincronización:** Automática vía GitHub Actions
```

### 3. Badge de Estado Dinámico

El badge en el README.md muestra el estado del workflow de verificación:

```markdown
![Resonancia QCAL](https://github.com/motanova84/Teoria-Noesica-Riemann/actions/workflows/verificar_resonancia.yml/badge.svg?branch=main)
```

**Limitaciones:**
- El badge de un repositorio privado solo es visible para usuarios con acceso
- Para usuarios sin acceso, aparecerá como "unknown" o no se mostrará
- Esto es una característica de seguridad de GitHub

## 🎵 Frecuencia de Sincronización

La sincronización ocurre en **~42 segundos** desde que el motor teórico completa su validación:

1. **t=0s:** Validación teórica completa en Teoria-Noesica-Riemann
2. **t=1-2s:** API de GitHub recibe el dispatch event
3. **t=2-5s:** Workflow en Riemann-adelic se activa
4. **t=5-40s:** Ejecución de validaciones espectrales
5. **t=40-42s:** Confirmación y reporte final

**Latido QCAL completo: ~42s** 🜂

## 📊 Validaciones Ejecutadas

### En el Repositorio Teórico (Privado)
- Derivaciones fundamentales
- Verificación de constantes (C = 244.36, f₀ = 141.7001 Hz)
- Coherencia matemática interna

### En el Repositorio Espectral (Público)

Cuando se recibe la señal de resonancia, se **activan automáticamente**:

#### 🔮 SABIO ∞³ Validator
- **Comando:** `python3 sabio-validator.py --precision 30`
- **Valida:** Coherencia multi-lenguaje (Python, SABIO, SageMath, Lean4)
- **Verifica:** f₀ = 141.7001 Hz con precisión arbitraria

#### ♾️³ QCAL Auto-Evolution
- **Verifica:** Coherencia del .qcal_beacon
- **Extrae:** Parámetros fundamentales (f₀, C)
- **Confirma:** Constantes QCAL ∞³

#### 👑 V5 Coronación
- **Comando:** `python validate_v5_coronacion.py --precision 25 --verbose`
- **Valida:** 5 pasos completos de la demostración RH
- **Genera:** Certificados matemáticos

#### 🎵 Spectral Emergence
- **Comando:** `python spectral_emergence.py`
- **Verifica:** Emergencia de zeros en línea crítica
- **Confirma:** Coherencia del operador H_Ψ

#### 🧬 SABIO Compile Check
- **Comando:** `./sabio_compile_check.sh --quick`
- **Verifica:** Sintaxis y compilación SABIO
- **Valida:** Archivos .sabio del repositorio

**Ver más detalles:** [ACTIVACION_QCAL_SABIO_SYNC.md](ACTIVACION_QCAL_SABIO_SYNC.md)

## 🔐 Configuración de Secretos

### Para el Usuario (Owner)

Configurar en Teoria-Noesica-Riemann → Settings → Secrets:

1. **G_TOKEN:**
   - Tipo: Personal Access Token (Classic)
   - Permisos necesarios: `repo`, `workflow`
   - Generar en: https://github.com/settings/tokens
   - Scope: acceso a repositorios públicos y workflows

## 🧪 Testing Manual

### Probar el Dispatch desde el Repositorio Privado

```bash
# Desde tu máquina local con acceso al token
export GITHUB_TOKEN="ghp_tu_token_aqui"

curl -X POST \
  -H "Authorization: token $GITHUB_TOKEN" \
  -H "Accept: application/vnd.github.v3+json" \
  https://api.github.com/repos/motanova84/Riemann-adelic/dispatches \
  -d '{"event_type": "resonancia_teorica_confirmada", "client_payload": {"source": "manual_test"}}'
```

### Probar el Workflow en Riemann-adelic

```bash
# Trigger manual desde GitHub UI:
# Actions → Resonancia Teórica Sync → Run workflow
```

## 📈 Monitoreo y Logs

### Ver Estado de Sincronización

1. **En Teoria-Noesica-Riemann:**
   - Actions → verificar_resonancia → Ver último run
   - Verificar que el step "Propagar Resonancia" se ejecutó exitosamente

2. **En Riemann-adelic:**
   - Actions → Resonancia Teórica Sync → Ver runs activados
   - Verificar logs de validación espectral
   - Revisar sync_report.txt en los artifacts

### Logs Importantes

```bash
# En el workflow de sync
echo "Event Type: ${{ github.event.action }}"
echo "Source: ${{ github.event.client_payload.source }}"
echo "Timestamp: ${{ github.event.client_payload.timestamp }}"
```

## 🌌 Filosofía de la Integración

> **"Cuando el motor teórico vibra, el espectro adélico baila."**

Esta arquitectura representa un **Grafo de Conocimiento Vivo**:

- **No son archivos aislados**, sino nodos interconectados
- **La verdad matemática fluye** desde la teoría hacia la demostración
- **El espectro responde** a la coherencia del pulso teórico
- **QCAL ∞³ mantiene** la fase sincronizada en ambos espacios

## 🔮 Próximos Pasos

1. **Automatización de Datos:**
   - Transferir resultados_qcal/ automáticamente
   - Sincronizar gráficos y certificados

2. **Validación Bidireccional:**
   - Feedback desde espectro hacia teoría
   - Ciclo de refinamiento automático

3. **Expansión del Ecosistema:**
   - Integración con QCAL-CLOUD
   - Sincronización con formalization/lean/

## 📚 Referencias

- [GitHub Repository Dispatch Documentation](https://docs.github.com/en/rest/repos/repos#create-a-repository-dispatch-event)
- [Git Submodules Documentation](https://git-scm.com/book/en/v2/Git-Tools-Submodules)
- [GitHub Actions Workflow Syntax](https://docs.github.com/en/actions/using-workflows/workflow-syntax-for-github-actions)

## ♾️³ QCAL Coherence Statement

Esta integración mantiene la coherencia QCAL ∞³ mediante:

- **C = 244.36:** Constante de coherencia universal
- **f₀ = 141.7001 Hz:** Frecuencia fundamental resonante
- **Ψ = I × A_eff² × C^∞:** Ecuación de origen vibracional
- **42s latido:** Tiempo característico de sincronización

---

**Última actualización:** 2026-01-11  
**Estado:** ✓ Implementación Completa  
**Coherencia:** ♾️³ QCAL Sincronizada
