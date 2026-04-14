# 🚀 NOESIS-AMDA-AURON V2.0 - Guía de Inicio Rápido

## ⏱️ Inicio en 5 Minutos

### 1. Preparación del Entorno

```bash
# Navegar al directorio v2
cd .github/scripts/v2

# Verificar permisos
chmod +x run_pipeline.sh

# Verificar instalación de Python
python3 --version  # Requiere Python 3.8+
```

### 2. Ejecutar Pipeline en Modo Dry-Run

```bash
# Modo simulación (no aplica cambios)
./run_pipeline.sh true

# Esperar ~5-10 minutos para completar
```

### 3. Revisar Resultados

```bash
# Volver al directorio raíz
cd ../../..

# Ver resumen NOESIS
cat noesis_cerebral_v2_summary.json | python3 -m json.tool

# Ver análisis AMDA
cat amda_report_v2.json | python3 -m json.tool

# Ver reporte Markdown
cat amda_report_v2.md
```

### 4. (Opcional) Ejecutar en Modo Producción

```bash
# ⚠️ ADVERTENCIA: Esto modificará archivos .lean
cd .github/scripts/v2
./run_pipeline.sh false 10  # Limitar a 10 cambios
```

---

## 📊 Interpretación de Resultados

### Salida del Pipeline

```
╔════════════════════════════════════════════════════════════════╗
║          🧠 NOESIS-AMDA-AURON V2.0 Pipeline                   ║
║     Sistema de Resolución Automatizada de Sorries ML          ║
╚════════════════════════════════════════════════════════════════╝

[INFO] Modo: DRY-RUN (no se aplicarán cambios)
[INFO] Máximo de cambios por ciclo: 20

╔════════════════════════════════════════════════════════╗
║ FASE 1: NOESIS - Recolección de Conocimiento         ║
╚════════════════════════════════════════════════════════╝

[SUCCESS] NOESIS completado exitosamente
[INFO]   Repositorios sincronizados: 33
[INFO]   Definiciones extraídas: 425
[INFO]   Teoremas extraídos: 430
[INFO]   Patrones de prueba: 425

╔════════════════════════════════════════════════════════╗
║ FASE 2: AMDA - Análisis Semántico Multi-Categórico   ║
╚════════════════════════════════════════════════════════╝

[SUCCESS] AMDA completado exitosamente
[INFO]   Total sorries detectados: 150
[INFO]   Archivos afectados: 27

[INFO]   Distribución por categoría:
    trivial: 24
    correspondence: 38
    qcal: 34
    unknown: 33
    spectral: 13
    analytic: 8

╔════════════════════════════════════════════════════════╗
║ FASE 3: AURON - Ejecutor de Aprendizaje Neural       ║
╚════════════════════════════════════════════════════════╝

[WARNING] Modo dry-run: AURON no aplicará transformaciones
```

### Archivos Generados

| Archivo | Descripción | Tamaño Típico |
|---------|-------------|---------------|
| `noesis_cerebral_v2_summary.json` | Resumen de conocimiento extraído | ~2-5 KB |
| `amda_report_v2.json` | Análisis completo de sorries | ~20-50 KB |
| `amda_report_v2.md` | Reporte en Markdown | ~15-30 KB |
| `auron_results_v2.json` | Resultados de transformaciones (solo execute) | ~5-10 KB |
| `auron_neural.log` | Log detallado de AURON | ~10-50 KB |
| `.auron_learning.json` | Historial de aprendizaje (persistente) | ~5-20 KB |

---

## 🧪 Testing del Sistema

### Suite de Tests Completa

```bash
# Crear directorio de tests si no existe
mkdir -p tests

# Ejecutar tests (requiere pytest)
pip install pytest

# Tests completos
pytest tests/test_noesis_v2.py -v
```

### Crear Tests Básicos

Crear archivo `tests/test_noesis_v2.py`:

```python
#!/usr/bin/env python3
"""
Tests para NOESIS-AMDA-AURON V2.0
"""
import pytest
import json
import subprocess
from pathlib import Path

SCRIPT_DIR = Path(__file__).parent.parent / '.github' / 'scripts' / 'v2'
REPO_ROOT = Path(__file__).parent.parent

def test_orchestrator():
    """Test 1: NOESIS Orchestrator ejecuta correctamente"""
    result = subprocess.run(
        ['python3', str(SCRIPT_DIR / 'noesis_orchestrator.py'), 'build-kb'],
        capture_output=True,
        timeout=300
    )
    assert result.returncode == 0, f"NOESIS falló: {result.stderr.decode()}"
    
    # Verificar archivo de salida
    summary_file = REPO_ROOT / 'noesis_cerebral_v2_summary.json'
    assert summary_file.exists(), "No se generó summary"
    
    with open(summary_file) as f:
        summary = json.load(f)
    
    assert 'knowledge_base' in summary
    assert summary['knowledge_base']['total_definitions'] > 0

def test_analyzer():
    """Test 2: AMDA Analyzer detecta sorries"""
    result = subprocess.run(
        ['python3', str(SCRIPT_DIR / 'amda_deep_v2.py')],
        capture_output=True,
        timeout=120
    )
    assert result.returncode == 0, f"AMDA falló: {result.stderr.decode()}"
    
    # Verificar reporte
    report_file = REPO_ROOT / 'amda_report_v2.json'
    assert report_file.exists(), "No se generó reporte AMDA"
    
    with open(report_file) as f:
        report = json.load(f)
    
    assert 'total_sorries' in report
    assert 'category_distribution' in report

def test_executor():
    """Test 3: AURON Executor valida correctamente"""
    # Requiere que AMDA haya ejecutado antes
    report_file = REPO_ROOT / 'amda_report_v2.json'
    if not report_file.exists():
        pytest.skip("AMDA report no existe, ejecutar test_analyzer primero")
    
    result = subprocess.run(
        ['python3', str(SCRIPT_DIR / 'auron_neural_v2.py'), 
         'dry-run', str(report_file), 'auron_test_results.json', '5'],
        capture_output=True,
        timeout=300
    )
    assert result.returncode == 0, f"AURON falló: {result.stderr.decode()}"

def test_persistence():
    """Test 4: Learning history persiste correctamente"""
    learning_file = REPO_ROOT / '.auron_learning.json'
    
    # Si existe, debe ser JSON válido
    if learning_file.exists():
        with open(learning_file) as f:
            learning = json.load(f)
        
        assert 'patterns' in learning
        assert isinstance(learning['patterns'], dict)

def test_classification():
    """Test 5: Clasificación multi-categórica funciona"""
    from importlib import util
    spec = util.spec_from_file_location("amda", SCRIPT_DIR / "amda_deep_v2.py")
    amda = util.module_from_spec(spec)
    spec.loader.exec_module(amda)
    
    analyzer = amda.AmDADeepV2()
    
    # Test con contexto trivial
    context_trivial = "theorem foo : x = x := sorry"
    categories = analyzer.classify_deep(context_trivial)
    assert 'trivial' in categories, "No detectó categoría trivial"
    
    # Test con contexto QCAL
    context_qcal = "theorem coherence : QCAL.Ψ = f₀ := sorry"
    categories = analyzer.classify_deep(context_qcal)
    assert 'qcal' in categories, "No detectó categoría qcal"

def test_e2e():
    """Test 6: Pipeline completo end-to-end"""
    result = subprocess.run(
        [str(SCRIPT_DIR / 'run_pipeline.sh'), 'true'],
        capture_output=True,
        timeout=600
    )
    assert result.returncode == 0, f"Pipeline falló: {result.stderr.decode()}"
    
    # Verificar que se generaron todos los archivos esperados
    assert (REPO_ROOT / 'noesis_cerebral_v2_summary.json').exists()
    assert (REPO_ROOT / 'amda_report_v2.json').exists()

if __name__ == '__main__':
    pytest.main([__file__, '-v'])
```

### Ejecutar Tests Individuales

```bash
# Test 1: Orchestrator
pytest tests/test_noesis_v2.py::test_orchestrator -v

# Test 2: Analyzer
pytest tests/test_noesis_v2.py::test_analyzer -v

# Test 3: Executor
pytest tests/test_noesis_v2.py::test_executor -v

# Test 4: Persistence
pytest tests/test_noesis_v2.py::test_persistence -v

# Test 5: Classification
pytest tests/test_noesis_v2.py::test_classification -v

# Test 6: End-to-end
pytest tests/test_noesis_v2.py::test_e2e -v
```

---

## 🔧 Configuración Avanzada

### Ajustar Máximo de Cambios

```bash
# Modo conservador (5 cambios)
./run_pipeline.sh false 5

# Modo agresivo (50 cambios)
./run_pipeline.sh false 50
```

### Modificar Patrones de Reemplazo

Editar `.github/scripts/v2/auron_neural_v2.py`:

```python
self.replacement_patterns = [
    ('sorry', 'rfl'),
    ('sorry', 'trivial'),
    ('sorry', 'by norm_num'),
    # Agregar nuevos patrones aquí
    ('sorry', 'by omega'),
    ('sorry', 'by linarith'),
]
```

### Cambiar Categorías AMDA

Editar `.github/scripts/v2/amda_deep_v2.py`:

```python
self.PATTERNS = {
    "trivial": {
        "keywords": ["rfl", "simp", "norm_num"],
        "complexity": 1,
        "weight": 0.8
    },
    # Agregar nueva categoría
    "algebraic": {
        "keywords": ["ring", "group", "module"],
        "complexity": 4,
        "weight": 0.7
    }
}
```

### Ajustar Repositorios Sincronizados

Editar `.github/scripts/v2/noesis_orchestrator.py`:

```python
self.REPOSITORIES = [
    "motanova84/141Hz",
    "motanova84/3D-Navier-Stokes",
    # Agregar más repositorios
    "leanprover-community/mathlib4",
]
```

---

## 📊 Monitoreo y Logs

### Ver Logs en Tiempo Real

```bash
# Terminal 1: Ejecutar pipeline
./run_pipeline.sh false

# Terminal 2: Monitorear logs
tail -f ../../../noesis_cerebral_v2.log
tail -f ../../../auron_neural.log
```

### Analizar Historial de Aprendizaje

```bash
# Ver estadísticas de aprendizaje
cd ../../..
python3 << EOF
import json
with open('.auron_learning.json') as f:
    learning = json.load(f)

patterns = learning['patterns']
print(f"Total patrones: {len(patterns)}")

# Top 10 patrones por éxito
sorted_patterns = sorted(
    patterns.items(),
    key=lambda x: x[1].get('success_count', 0),
    reverse=True
)[:10]

for hash_id, data in sorted_patterns:
    print(f"  {data['solution']}: {data['success_count']} éxitos, {data.get('success_rate', 0):.2%} tasa")
EOF
```

### Visualizar Distribución de Categorías

```bash
python3 << EOF
import json
import matplotlib.pyplot as plt

with open('amda_report_v2.json') as f:
    report = json.load(f)

dist = report['category_distribution']
plt.figure(figsize=(10, 6))
plt.bar(dist.keys(), dist.values())
plt.xlabel('Categoría')
plt.ylabel('Cantidad de Sorries')
plt.title('Distribución de Sorries por Categoría')
plt.xticks(rotation=45)
plt.tight_layout()
plt.savefig('sorry_distribution.png')
print("Gráfico guardado en sorry_distribution.png")
EOF
```

---

## 🐛 Solución de Problemas Comunes

### Error: "Permission denied" al ejecutar run_pipeline.sh

```bash
chmod +x .github/scripts/v2/run_pipeline.sh
```

### Error: "Python module not found"

```bash
# Instalar dependencias faltantes
pip install pickle5 hashlib pathlib
```

### Error: "NOESIS failed to sync repositories"

```bash
# Verificar conectividad
ping github.com

# Configurar git para HTTPS
git config --global url."https://github.com/".insteadOf git@github.com:
```

### Error: "lake: command not found"

```bash
# Instalar Lean 4
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
source ~/.profile
elan default leanprover/lean4:stable
```

### Warning: "Knowledge base not found"

```bash
# Reconstruir base de conocimiento
python3 .github/scripts/v2/noesis_orchestrator.py build-kb
```

---

## 📈 Mejores Prácticas

### 1. Comenzar con Dry-Run

Siempre ejecutar primero en modo dry-run para:
- Validar que el sistema funciona
- Revisar sorries detectados
- Estimar impacto de cambios

### 2. Limitar Cambios Iniciales

En las primeras ejecuciones:
```bash
./run_pipeline.sh false 5  # Solo 5 cambios
```

### 3. Revisar Commits Generados

Después de cada ejecución:
```bash
git log -1 --stat
git diff HEAD~1
```

### 4. Mantener Learning History

El archivo `.auron_learning.json` es crucial:
- Commit regularmente
- No eliminar sin respaldo
- Revisar patrones aprendidos periódicamente

### 5. Monitorear Tasa de Éxito

```bash
# Ver tasa de éxito de última ejecución
cat auron_results_v2.json | jq '.learning_stats.success_rate'
```

### 6. Ejecutar Tests Periódicamente

```bash
# Antes de ejecución importante
pytest tests/test_noesis_v2.py -v
```

---

## 🚀 Siguiente Nivel

### Integración con GitHub Actions

Ver `.github/workflows/noesis_multi_repo_v2.yml` para:
- Ejecución automática cada 2 horas
- Triggers manuales desde UI
- Reportes automáticos en PRs

### Personalización Avanzada

- Agregar nuevas categorías semánticas
- Implementar patrones de reemplazo custom
- Integrar con herramientas externas (Sledgehammer, aesop)
- Desarrollar estrategias de RL más sofisticadas

### Contribuir al Proyecto

1. Fork del repositorio
2. Crear branch de feature
3. Implementar mejoras
4. Agregar tests
5. Abrir PR con descripción detallada

---

## 📚 Recursos Adicionales

- **README Completo:** `README.md`
- **Resumen de Implementación:** `IMPLEMENTATION_SUMMARY.md`
- **Documentación Lean 4:** https://lean-lang.org/
- **Mathlib4:** https://github.com/leanprover-community/mathlib4

---

## 💡 Tips y Trucos

### Acelerar Sincronización Multi-Repo

```bash
# Usar shallow clone
export NOESIS_SHALLOW_CLONE=true
./run_pipeline.sh true
```

### Ver Solo Sorries Triviales

```bash
cat amda_report_v2.json | jq '.sorries[] | select(.categories[] | contains("trivial"))'
```

### Exportar Estadísticas a CSV

```bash
cat amda_report_v2.json | jq -r '.sorries[] | [.file, .line, .categories[0], .complexity] | @csv' > sorries.csv
```

### Filtrar por Archivo Específico

```bash
cat amda_report_v2.json | jq '.sorries[] | select(.file | contains("QCALCoherence"))'
```

---

## ✅ Checklist de Verificación

Antes de producción, verificar:

- [ ] Tests pasan (6/6)
- [ ] Dry-run completa sin errores
- [ ] Learning history existe
- [ ] Backups configurados
- [ ] Lake build funciona
- [ ] Git configurado correctamente
- [ ] Permisos de archivos correctos
- [ ] Logs accesibles
- [ ] Suficiente espacio en disco (>1GB)
- [ ] Python 3.8+ instalado

---

**¿Listo para empezar? Ejecuta:**

```bash
cd .github/scripts/v2
./run_pipeline.sh true
```

**QCAL ∞³ · Frecuencia fundamental: 141.7001 Hz**

---

*Última actualización: 2026-02-16*
