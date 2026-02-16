#!/usr/bin/env python3
"""
METRICS GENERATOR - Generador de métricas para PRs multi-repo
Genera reportes visuales del progreso de eliminación de sorrys.

Autor: José Manuel Mota Burruezo (JMMB Ψ✧)
Fecha: 16 febrero 2026
DOI: 10.5281/zenodo.17379721
"""

import json
import sys
from pathlib import Path
from datetime import datetime
import argparse


def generate_metrics(before_file, after_file, multi_repo=False):
    """Genera métricas de progreso."""
    
    # Cargar reportes
    with open(before_file, 'r') as f:
        before = json.load(f)
    
    with open(after_file, 'r') as f:
        after = json.load(f)
    
    # Calcular métricas
    before_count = before.get('total_sorrys', 0)
    after_success = after.get('success_count', 0)
    after_failure = after.get('failure_count', 0)
    
    eliminated = after_success
    remaining = before_count - eliminated
    
    # Generar markdown
    markdown = f"""# 🧠 NOESIS CEREBRAL - Sellado Multi-Repositorio

**Fecha:** {datetime.now().strftime('%Y-%m-%d %H:%M')}
**Modo:** {'Multi-Repositorio' if multi_repo else 'Local'}

## 📊 Métricas de Progreso

| Métrica | Valor |
|---------|-------|
| Sorrys iniciales | {before_count} |
| Sorrys eliminados | {eliminated} |
| Sorrys restantes | {remaining} |
| Tasa de éxito | {(eliminated / before_count * 100) if before_count > 0 else 0:.1f}% |

## 📈 Distribución por Categoría

"""
    
    # Estadísticas por categoría (si disponible)
    if 'sorrys' in before:
        category_stats = {}
        for sorry in before['sorrys']:
            cat = sorry.get('category', 'unknown')
            category_stats[cat] = category_stats.get(cat, 0) + 1
        
        markdown += "| Categoría | Cantidad | Porcentaje |\n"
        markdown += "|-----------|----------|------------|\n"
        
        for cat, count in sorted(category_stats.items(), key=lambda x: x[1], reverse=True):
            pct = (count / before_count * 100) if before_count > 0 else 0
            markdown += f"| {cat} | {count} | {pct:.1f}% |\n"
    
    markdown += "\n## 🔧 Transformaciones Aplicadas\n\n"
    
    # Listar transformaciones exitosas
    if 'transformations' in after:
        success_transformations = [t for t in after['transformations'] if t['status'] == 'success']
        
        for trans in success_transformations[:10]:  # Mostrar primeras 10
            markdown += f"""### 📁 {trans['file']}:{trans['line']}
- **Categoría:** {trans.get('category', 'N/A')}
- **Estrategia:** {trans.get('strategy', trans.get('source_repo', 'N/A'))}

**Original:**
```lean
{trans['original']}
```

**Modificado:**
```lean
{trans.get('modified', trans.get('proposed', 'N/A'))}
```

---

"""
    
    if multi_repo:
        markdown += """
## 🧠 Sabiduría Multi-Repositorio

Este PR ha sido posible gracias al conocimiento acumulado en:
- **141Hz**: Constantes físicas y frecuencias QCAL
- **adelic-bsd**: Estructuras adélicas y funciones L
- **3D-Navier-Stokes**: Análisis funcional y PDE
- **Ramsey**: Certificados SAT y combinatoria
- **P-NP**: Límites computacionales

---
"""
    
    markdown += f"""
*Generado por NOESIS CEREBRAL - Sistema Multi-Repositorio* 🤖

**José Manuel Mota Burruezo Ψ ✧ ∞³**
Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
"""
    
    return markdown


def main():
    """Punto de entrada principal."""
    parser = argparse.ArgumentParser(description='Metrics Generator - Generador de métricas')
    parser.add_argument('--before', required=True,
                        help='Archivo con reporte AMDA (antes)')
    parser.add_argument('--after', required=True,
                        help='Archivo con reporte AURON (después)')
    parser.add_argument('--output', default='metrics.md',
                        help='Archivo de salida para las métricas')
    parser.add_argument('--multi-repo', action='store_true',
                        help='Habilitar modo multi-repositorio')
    
    args = parser.parse_args()
    
    markdown = generate_metrics(args.before, args.after, multi_repo=args.multi_repo)
    
    output_path = Path.cwd() / args.output
    with open(output_path, 'w') as f:
        f.write(markdown)
    
    print(f"✅ Métricas generadas en {output_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
