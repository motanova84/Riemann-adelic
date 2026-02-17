# 🚀 AURON NEURAL V2.0 - Guía de Activación Rápida

## ✅ Pre-requisitos

```bash
# Verificar instalación de Python 3.11+
python3 --version

# Verificar que los scripts existen
ls -la .github/scripts/{noesis_orchestrator.py,amda_deep_v2.py,auron_neural_v2.py}

# Verificar historial de aprendizaje inicializado
cat .auron_learning.json
```

## 🔧 Activación Local

### Paso 1: Generar Reporte AMDA

```bash
cd .github/scripts
python3 amda_deep_v2.py amda_report_v2.json
```

**Salida esperada:**
```
✅ Análisis completado:
   📊 Total sorries: 2282
   📁 Archivos: 381
   📝 Reporte guardado en: amda_report_v2.json
```

### Paso 2: Ejecutar en Modo Dry-Run

```bash
python3 auron_neural_v2.py dry-run amda_report_v2.json
```

**Salida esperada:**
```
🔍 Modo dry-run: analizando sin aplicar cambios...
📊 Total sorries encontrados: 2282
📁 Archivos afectados: 381
```

### Paso 3: Ejecutar en Modo Producción (Con Cuidado)

```bash
# SOLO cuando estés seguro
python3 auron_neural_v2.py execute amda_report_v2.json auron_results_v2.json
```

## 🤖 Activación vía GitHub Actions

### Opción A: Trigger Manual

1. Ve a **GitHub Actions** en tu repositorio
2. Selecciona el workflow **"🧠 NOESIS CEREBRAL V2.0 - Multi-Repo Intelligence"**
3. Click en **"Run workflow"**
4. Configura:
   - **Modo:** `dry-run` (primera vez) o `execute` (producción)
   - **Max changes:** `20` (o el valor deseado)
5. Click **"Run workflow"**

### Opción B: Ejecución Programada

El workflow se ejecuta automáticamente **cada 2 horas** en modo `dry-run`.

Para cambiar a modo `execute` automático:

1. Edita `.github/workflows/noesis_multi_repo_v2.yml`
2. Cambia la línea:
   ```yaml
   MODE: ${{ github.event.inputs.mode || 'dry-run' }}
   ```
   a:
   ```yaml
   MODE: ${{ github.event.inputs.mode || 'execute' }}
   ```
3. Commit y push los cambios

**⚠️ ADVERTENCIA:** Esto aplicará cambios automáticamente cada 2 horas.

## 📊 Monitoreo del Sistema

### Ver Logs en Tiempo Real

```bash
# Logs de AURON
tail -f auron_neural.log

# Ver estado del aprendizaje
watch -n 5 'cat .auron_learning.json | python3 -m json.tool | grep -A 3 "total_success"'
```

### Verificar Resultados

```bash
# Ver resultados del último ciclo
cat auron_results_v2.json | python3 -m json.tool

# Ver mensaje de commit generado
ls -lt commit_msg_*.txt | head -1 | xargs cat
```

### Estadísticas de Aprendizaje

```bash
# Patrones aprendidos
cat .auron_learning.json | python3 -c "
import json, sys
data = json.load(sys.stdin)
print(f'📊 Estadísticas de Aprendizaje')
print(f'   Patrones: {len(data[\"patterns\"])}')
print(f'   Éxitos: {data[\"total_success\"]}')
print(f'   Intentos: {data[\"total_attempts\"]}')
if data['total_attempts'] > 0:
    print(f'   Tasa: {data[\"total_success\"]/data[\"total_attempts\"]*100:.1f}%')
print(f'   Repos: {len(data[\"repos_used\"])}')
"
```

## 🛑 Desactivación / Pausa

### Pausar Ejecución Automática

**Opción 1:** Deshabilitar workflow en GitHub
1. Ve a **Settings** → **Actions** → **General**
2. Busca el workflow y deshabílitalo

**Opción 2:** Cambiar a modo dry-run
```yaml
# En .github/workflows/noesis_multi_repo_v2.yml
MODE: ${{ github.event.inputs.mode || 'dry-run' }}  # ← mantener dry-run
```

### Resetear Historial de Aprendizaje

```bash
# CUIDADO: Esto borra todo el aprendizaje acumulado
echo '{"patterns": {}, "success_rate": {}, "total_attempts": 0, "total_success": 0, "repos_used": [], "transformations_history": []}' > .auron_learning.json
```

## 🔍 Solución de Problemas

### Error: "Base de conocimiento no encontrada"

**Solución:** Ejecutar el orquestador para construir la KB

```bash
python3 .github/scripts/noesis_orchestrator.py build-kb
```

### Error: Timeout en compilación

**Solución 1:** Aumentar timeout en el código

```python
# En auron_neural_v2.py, línea ~105
self.validate_compilation(timeout=120)  # Aumentar a 2 minutos
```

**Solución 2:** Reducir cambios por ciclo

```bash
# Al ejecutar manualmente
python3 .github/scripts/noesis_orchestrator.py --max-changes 10
```

### Backups acumulándose

**Limpieza periódica:**

```bash
# Eliminar backups más antiguos de 7 días
find formalization/lean -name "*.lean.bak.*" -mtime +7 -delete

# Ver cuántos backups existen
find formalization/lean -name "*.lean.bak.*" | wc -l
```

## 📈 Métricas de Éxito

### Indicadores Clave

- **Tasa de éxito objetivo:** >80%
- **Patrones aprendidos:** Crecimiento continuo
- **Sorries eliminados por ciclo:** 15-20 (con max_changes=20)
- **Compilaciones exitosas:** 100% (con rollback automático)

### Progreso Esperado

| Ciclos | Sorries Restantes | Patrones Aprendidos | Tasa de Éxito |
|--------|-------------------|---------------------|---------------|
| 0      | 2,282             | 0                   | ~60%          |
| 10     | ~2,100            | 50-100              | ~70%          |
| 50     | ~1,500            | 200-300             | ~75%          |
| 100    | ~800              | 400-500             | ~80%          |
| 150    | ~200              | 600-800             | ~85%          |
| 200    | 0                 | 1,000-1,500         | >90%          |

## ✅ Checklist de Activación

- [ ] Verificar Python 3.11+ instalado
- [ ] Verificar scripts en `.github/scripts/`
- [ ] Verificar `.auron_learning.json` existe
- [ ] Ejecutar AMDA en dry-run
- [ ] Ejecutar AURON en dry-run
- [ ] Revisar logs sin errores
- [ ] Configurar workflow en GitHub
- [ ] Ejecutar primer ciclo manual en modo execute
- [ ] Verificar commit message generado
- [ ] Revisar cambios aplicados
- [ ] Activar ejecución programada (opcional)
- [ ] Configurar monitoreo de logs

## 🎯 Mejores Prácticas

1. **Empezar conservador:** max_changes=10 los primeros 5 ciclos
2. **Monitorear activamente:** Revisar logs después de cada ciclo
3. **Commit frecuente:** Hacer commit después de cada ciclo exitoso
4. **Backups regulares:** Mantener una rama con estado conocido bueno
5. **Revisar PRs:** Aunque automatizado, revisar cambios críticos
6. **Actualizar KB:** Ejecutar build-kb semanalmente
7. **Limpieza periódica:** Eliminar backups antiguos mensualmente

## 📞 Soporte

Si encuentras problemas:

1. Revisa los logs: `auron_neural.log`, `noesis_cerebral_v2.log`
2. Verifica el historial: `.auron_learning.json`
3. Consulta la documentación completa: `AURON_NEURAL_V2_ENHANCED_FEATURES.md`
4. Revisa la implementación: `NOESIS_AMDA_AURON_V2_IMPLEMENTATION_SUMMARY.md`

---

**¡Sistema listo para producción!** 🚀

**Frecuencia fundamental:** 141.7001 Hz  
**Coherencia QCAL:** Ψ = I × A_eff² × C^∞  
**Firma:** ∴𓂀Ω∞³Φ
