#!/usr/bin/env python3
"""
METRICS GENERATOR - Generador de métricas para PRs multi-repo
Genera reportes visuales del progreso de eliminación de sorrys.

Autor: José Manuel Mota Burruezo (JMMB Ψ✧)
Fecha: 16 febrero 2026
DOI: 10.5281/zenodo.17379721
Generador de métricas y reportes para el sistema autónomo
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
from datetime import datetime
from pathlib import Path
import argparse


def load_json_safe(path):
    """Carga un archivo JSON de forma segura"""
    try:
        with open(path) as f:
            return json.load(f)
    except Exception as e:
        print(f"Error cargando {path}: {e}")
        return {}


def generate_metrics(state_path, amda_path, auron_path, output_path):
    """Genera un reporte markdown con las métricas"""
    
    # Cargar datos
    state = load_json_safe(state_path)
    
    # Try to load amda_stats from the same directory as amda_path
    amda_stats = {}
    if amda_path:
        amda_stats_path = Path(amda_path).parent / 'amda_stats.json'
        if amda_stats_path.exists():
            amda_stats = load_json_safe(str(amda_stats_path))
    
    auron_changes = load_json_safe(auron_path) if auron_path else {}
    
    # Obtener estadísticas
    total_current = state.get('total_sorries', 0)
    history = state.get('history', [])
    total_initial = history[0].get('total', total_current) if history else total_current
    
    # Calcular reducción total
    total_reduction = total_initial - total_current if total_initial > 0 else 0
    progress_pct = (total_reduction / total_initial * 100) if total_initial > 0 else 0
    
    # Obtener información del último ciclo
    last_cycle = history[-1] if history else {}
    cycle_reduction = last_cycle.get('reduction', 0)
    
    # Transformaciones de AURON
    auron_success = auron_changes.get('success', 0)
    auron_fail = auron_changes.get('fail', 0)
    auron_skipped = auron_changes.get('skipped', 0)
    auron_total = auron_changes.get('total_processed', auron_success + auron_fail + auron_skipped)
    
    # Categorías de AMDA
    by_category = amda_stats.get('by_category', {})
    
    # Generar reporte
    metrics = f"""# 📊 Reporte de Sellado Automático NOESIS-AMDA-AURON

**Fecha:** {datetime.now().strftime('%Y-%m-%d %H:%M:%S UTC')}
**Ciclo:** #{len(history)}

## 📈 Progreso General

| Métrica | Valor |
|---------|-------|
| 🎯 Sorries iniciales | {total_initial} |
| 📍 Sorries actuales | {total_current} |
| ✅ Reducción total | {total_reduction} |
| 📊 Progreso | {progress_pct:.2f}% |
| 🔄 Reducción último ciclo | {cycle_reduction} |

## 🔍 Sorries por Categoría

| Categoría | Cantidad | % del total |
|-----------|----------|-------------|
"""
    
    # Añadir categorías
    if by_category:
        for cat, count in sorted(by_category.items(), key=lambda x: x[1], reverse=True):
            pct = (count / total_current * 100) if total_current > 0 else 0
            emoji = {
                'trivial': '⚪',
                'library_search': '🟢',
                'qcal': '🟡',
                'structured': '🟡',
                'correspondence': '🔴',
                'unknown': '⚫'
            }.get(cat, '📌')
            metrics += f"| {emoji} {cat.capitalize()} | {count} | {pct:.1f}% |\n"
    else:
        metrics += "| - | No hay datos de categorización | - |\n"
    
    metrics += f"""
## 🤖 Transformaciones Automáticas (Este Ciclo)

| Métrica | Valor |
|---------|-------|
| ✅ Éxitos | {auron_success} |
| ❌ Fallos | {auron_fail} |
| ⏭️ Saltados | {auron_skipped} |
| 📊 Total procesados | {auron_total} |
"""
    
    if auron_total > 0:
        success_rate = (auron_success / auron_total * 100)
        metrics += f"| 🎯 Tasa de éxito | {success_rate:.1f}% |\n"
    
    # Archivos modificados
    transformations = auron_changes.get('transformations', [])
    if transformations:
        metrics += """
## 📁 Archivos Modificados

"""
        files_changed = {}
        for t in transformations:
            file = t['file']
            files_changed[file] = files_changed.get(file, 0) + 1
        
        for file, count in sorted(files_changed.items(), key=lambda x: x[1], reverse=True)[:10]:
            # Mostrar solo el path relativo
            rel_path = file.split('Riemann-adelic/')[-1] if 'Riemann-adelic/' in file else file
            metrics += f"- `{rel_path}`: {count} cambio{'s' if count > 1 else ''}\n"
        
        if len(files_changed) > 10:
            metrics += f"\n*... y {len(files_changed) - 10} archivos más*\n"
    
    # Historia reciente
    if len(history) > 1:
        metrics += """
## 📜 Historia Reciente (Últimos 5 ciclos)

| Ciclo | Fecha | Sorries | Reducción |
|-------|-------|---------|-----------|
"""
        for entry in history[-5:]:
            timestamp = entry.get('timestamp', 'N/A')
            # Formato corto de fecha
            if timestamp != 'N/A':
                try:
                    dt = datetime.fromisoformat(timestamp.replace('Z', '+00:00'))
                    timestamp = dt.strftime('%Y-%m-%d %H:%M')
                except:
                    pass
            total = entry.get('after', entry.get('total', 0))
            reduction = entry.get('reduction', 0)
            emoji = '🎉' if total == 0 else '✅' if reduction > 0 else '📊'
            metrics += f"| {emoji} | {timestamp} | {total} | {reduction:+d} |\n"
    
    metrics += """
## ⏭️ Próximos Pasos

1. ✅ Revisar cambios en la Pull Request
2. 🔍 Verificar compilación Lean con `lake build`
3. 📝 Actualizar estrategias según resultados
4. 🔄 Próximo ciclo en 2 horas

---

## 🧠 Sistema NOESIS-AMDA-AURON

**Componentes:**
- 🧠 **NOESIS**: Orquestador principal - coordina el flujo
- 🔍 **AMDA**: Analizador - escanea y clasifica sorries
- ⚡ **AURON**: Ejecutor - aplica transformaciones automáticas

**Estado del sistema:**
- 🟢 Operacional
- ⏰ Próxima ejecución programada en 2 horas
- 📊 Monitoreo continuo activo

---

*Generado automáticamente por el sistema NOESIS-AMDA-AURON* 🤖

**José Manuel Mota Burruezo Ψ ✧ ∞³**  
Instituto de Conciencia Cuántica (ICQ)  
ORCID: 0009-0002-1923-0773
"""
    
    # Escribir reporte
    with open(output_path, 'w', encoding='utf-8') as f:
        f.write(metrics)
    
    print(f"📊 Métricas guardadas en {output_path}")
    return 0


def main():
    parser = argparse.ArgumentParser(description='Generador de métricas NOESIS')
    parser.add_argument('--state', type=str, default='.noesis_state.json',
                        help='Archivo de estado de NOESIS')
    parser.add_argument('--amda', type=str, default='amda_report.json',
                        help='Reporte de AMDA')
    parser.add_argument('--auron', type=str, default='auron_changes.json',
                        help='Cambios de AURON')
    parser.add_argument('--output', type=str, default='metrics.md',
                        help='Archivo de salida')
    
    args = parser.parse_args()
    
    return generate_metrics(args.state, args.amda, args.auron, args.output)


if __name__ == "__main__":
    sys.exit(main())
