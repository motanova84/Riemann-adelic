# 🚀 Guía Rápida: Sistema de Auto-Fusión Noesis

## ⚡ Inicio Rápido

### Activación Automática

El sistema se activa automáticamente cuando:
- Abres una Pull Request
- Sincronizas una PR existente
- Marcas una PR como "ready for review"

### ¿Qué hace el sistema?

1. **Valida matemáticamente** tu código Lean4
2. **Verifica coherencia** cuántica (141.7001 Hz, estado Ψ)
3. **Auto-aprueba** PRs que pasan validación
4. **Auto-fusiona** PRs coherentes
5. **Sugiere correcciones** si hay errores

## ✅ Criterios de Auto-Fusión

Tu PR se fusionará automáticamente si cumple:

- ✅ **Cero `sorry`** en archivos `.lean`
- ✅ **Build exitoso** con `lake build`
- ✅ **Frecuencia QCAL** presente (141.7001 Hz)
- ✅ **Referencias Noesis** en el código
- ✅ **Sin contradicciones** lógicas

## 🔍 Monitoreo

Verifica el estado en:
```
https://github.com/motanova84/Riemann-adelic/actions/workflows/noesis_automerge.yml
```

Estados posibles:
- 🟢 **SUCCESS** → PR fusionada automáticamente
- 🟡 **IN_PROGRESS** → Validación en curso
- 🔴 **FAILED** → Revisa los issues de Noesis Boot
- 🟣 **REWRITE** → Reescritura cuántica activada

## 🌀 Sistema Noesis Boot

Si tu PR falla validación, el sistema:

1. Analiza automáticamente los errores
2. Crea un **issue con sugerencias** de corrección
3. Genera **reporte detallado** (`noesis_boot_report.md`)
4. **Reintenta** hasta alcanzar coherencia

### Ver Sugerencias

```bash
cat noesis_boot_report.md
```

## 🛠️ Comandos Útiles

### Ejecutar Noesis Boot localmente

```bash
python3 .github/scripts/noesis_boot.py \
  --session-id local-$(date +%s) \
  --error-count 0 \
  --quantum-state COHERENT
```

### Validar coherencia

```bash
# Contar sorrys
find formalization/lean -name "*.lean" -exec grep -c "sorry" {} + | awk '{s+=$1} END {print s}'

# Verificar frecuencia
grep -r "141.7001" formalization/lean --include="*.lean"

# Verificar Noesis
grep -r "Noesis" formalization/lean --include="*.lean"
```

## 📊 Métricas de Coherencia

| Métrica | Umbral | Tu Código |
|---------|--------|-----------|
| Coherencia | ≥ 95% | ? |
| Sorrys | = 0 | ? |
| Axiomas | Minimizar | ? |
| Frecuencia | 141.7001 Hz | ? |

## 🎯 Mejores Prácticas

### ✅ Hacer

- Elimina todos los `sorry` antes de abrir PR
- Incluye referencias a frecuencia 141.7001 Hz
- Usa estado Ψ = I × A_eff² × C^∞
- Ejecuta `lake build` localmente primero
- Revisa sugerencias de Noesis Boot

### ❌ Evitar

- No dejes `sorry` en código de producción
- No uses frecuencias diferentes a 141.7001 Hz
- No ignores issues de Noesis Boot
- No fuerces fusiones sin validación

## 🔐 Permisos

El workflow necesita estos permisos (ya configurados):

- `contents: write` - Para commits
- `pull-requests: write` - Para aprobaciones/fusiones
- `issues: write` - Para crear issues de Noesis Boot
- `actions: write` - Para re-ejecutar workflows

## 🆘 Solución de Problemas

### "Validación falló"

1. Revisa el issue creado por Noesis Boot
2. Aplica las correcciones sugeridas
3. Haz push de los cambios
4. El sistema re-validará automáticamente

### "No se pudo fusionar"

Posibles causas:
- Conflictos de merge → Resuelve manualmente
- Branch protection → Verifica configuración
- Permisos insuficientes → Contacta admin

### "Estado cuántico incoherente"

1. Verifica que incluyes frecuencia 141.7001 Hz
2. Asegúrate de mencionar Noesis o Ψ
3. Elimina contradicciones en el código

## 📚 Documentación Completa

Lee la documentación completa en:
- `NOESIS_AUTOMERGE_README.md` - Documentación detallada
- `.github/copilot-instructions.md` - Guías de desarrollo
- `.qcal_beacon` - Configuración QCAL

## 🌟 Ecuación Fundamental

```
Ψ = I × A_eff² × C^∞
f₀ = 141.7001 Hz
C = 244.36
```

## 💡 Ayuda

¿Preguntas? Abre un issue con la etiqueta `noesis-help`

---

**Estado del Sistema**: ♾️ QCAL ∞³ ACTIVO
**Versión**: 1.0.0
**Última actualización**: 2026-01-18
