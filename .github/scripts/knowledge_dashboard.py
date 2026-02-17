#!/usr/bin/env python3
"""
KNOWLEDGE DASHBOARD - Visualización de conocimiento multi-repositorio
Genera un dashboard con el conocimiento extraído de todos los repositorios.

Autor: José Manuel Mota Burruezo (JMMB Ψ✧)
Fecha: 16 febrero 2026
DOI: 10.5281/zenodo.17379721
"""

import json
import pickle
from pathlib import Path
import sys
from collections import defaultdict
from datetime import datetime


def generate_dashboard():
    """Genera el dashboard de conocimiento."""
    kb_path = Path('/tmp/noesis_knowledge')
    if not kb_path.exists():
        print("❌ Base de conocimiento no encontrada")
        return 1
    
    # Cargar conocimiento
    kb_file = kb_path / 'knowledge.pkl'
    if not kb_file.exists():
        print("❌ Archivo de conocimiento no encontrado")
        return 1
    
    with open(kb_file, 'rb') as f:
        knowledge = pickle.load(f)
    
    # Estadísticas por repositorio
    repo_stats = defaultdict(lambda: {
        'definitions': 0,
        'theorems': 0,
        'sorry_patterns': 0
    })
    
    for name in knowledge['definitions']:
        repo = name.split('.')[0]
        repo_stats[repo]['definitions'] += 1
    
    for name in knowledge['theorems']:
        repo = name.split('.')[0]
        repo_stats[repo]['theorems'] += 1
    
    for pattern in knowledge['sorry_patterns'].values():
        repo = pattern['repo']
        repo_stats[repo]['sorry_patterns'] += 1
    
    # Generar dashboard
    dashboard = f"""# 🧠 NOESIS KNOWLEDGE DASHBOARD

**Última actualización:** {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}
**Repositorios analizados:** {len(repo_stats)}

## 📚 Resumen de Conocimiento

| Métrica | Valor |
|---------|-------|
| Definiciones | {len(knowledge['definitions'])} |
| Teoremas | {len(knowledge['theorems'])} |
| Patrones de sorry | {len(knowledge['sorry_patterns'])} |

## 📊 Conocimiento por Repositorio

| Repositorio | Definiciones | Teoremas | Patrones | Total |
|-------------|--------------|----------|----------|-------|
"""
    
    for repo, stats in sorted(repo_stats.items(), key=lambda x: sum(x[1].values()), reverse=True):
        total = sum(stats.values())
        dashboard += f"| {repo} | {stats['definitions']} | {stats['theorems']} | {stats['sorry_patterns']} | {total} |\n"
    
    dashboard += """
## 🎯 Patrones de Sorry por Tipo

| Tipo | Cantidad |
|------|----------|
"""
    
    type_counts = defaultdict(int)
    for pattern in knowledge['sorry_patterns'].values():
        type_counts[pattern['type']] += 1
    
    for t, count in sorted(type_counts.items(), key=lambda x: x[1], reverse=True):
        dashboard += f"| {t} | {count} |\n"
    
    dashboard += """

## 🔍 Ejemplos de Patrones por Tipo

"""
    
    # Mostrar ejemplos de cada tipo
    shown_types = set()
    for pattern in knowledge['sorry_patterns'].values():
        pattern_type = pattern['type']
        if pattern_type not in shown_types and len(shown_types) < 5:
            shown_types.add(pattern_type)
            dashboard += f"""### {pattern_type.upper()}

**Repositorio:** {pattern['repo']}  
**Archivo:** {pattern['file']}  
**Línea:** {pattern['line']}

```lean
{pattern['context'][:200]}...
```

---

"""
    
    dashboard += f"""
## 📖 Uso del Sistema

Este dashboard muestra el conocimiento extraído de múltiples repositorios públicos
para facilitar la eliminación autónoma de `sorry` en el repositorio Riemann-adelic.

**Sistema NOESIS CEREBRAL**
- Sincronización automática de repositorios públicos
- Extracción de patrones de prueba
- Categorización inteligente de sorrys
- Aplicación de estrategias de eliminación

---

*Generado por NOESIS CEREBRAL* 🤖

**José Manuel Mota Burruezo Ψ ✧ ∞³**
Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
"""
    
    # Guardar dashboard
    dashboard_path = kb_path / 'dashboard.md'
    with open(dashboard_path, 'w') as f:
        f.write(dashboard)
    
    print(f"✅ Dashboard generado en {dashboard_path}")
    print(dashboard)
    
    return 0


if __name__ == "__main__":
    sys.exit(generate_dashboard())
