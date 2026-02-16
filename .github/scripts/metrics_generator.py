#!/usr/bin/env python3
"""
Generador de métricas y reportes para el sistema autónomo
"""

import json
import sys
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
