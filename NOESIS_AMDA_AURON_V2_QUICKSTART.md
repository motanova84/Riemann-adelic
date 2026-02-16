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
