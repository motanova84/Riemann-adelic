#!/usr/bin/env python3
"""
METRICS GENERATOR V2.0
Genera métricas y reportes para el sistema NOESIS CEREBRAL V2.0
"""

import json
import sys
from pathlib import Path
from datetime import datetime

class MetricsGenerator:
    """Generador de métricas y estadísticas"""
    
    def __init__(self, amda_report, auron_results, noesis_report):
        self.amda_report = self.load_json(amda_report)
        self.auron_results = self.load_json(auron_results)
        self.noesis_report = self.load_json(noesis_report)
        
    def load_json(self, filepath):
        """Carga un archivo JSON"""
        if not filepath.exists():
            return {}
        with open(filepath) as f:
            return json.load(f)
    
    def generate_markdown_report(self):
        """Genera reporte en formato Markdown"""
        timestamp = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
        
        # Estadísticas AMDA
        total_sorries = self.amda_report.get("summary", {}).get("total_sorries", 0)
        by_category = self.amda_report.get("summary", {}).get("by_category", {})
        
        # Estadísticas AURON
        success = self.auron_results.get("success", 0)
        fail = self.auron_results.get("fail", 0)
        learning_stats = self.auron_results.get("learning_stats", {})
        
        # Estadísticas NOESIS
        kb = self.noesis_report.get("knowledge_base", {})
        
        md = f"""# 🧠 NOESIS CEREBRAL V2.0 - Reporte de Métricas

**Generado:** {timestamp}
**Sistema:** NOESIS-AMDA-AURON V2.0

---

## 📊 Resumen Ejecutivo

| Métrica | Valor |
|---------|-------|
| Sorries totales | {total_sorries} |
| Sorries eliminados | {success} |
| Sorries restantes | {total_sorries - success} |
| Tasa de éxito | {success/(success+fail)*100:.1f}% | 
| Repositorios sincronizados | {len(kb.get('repos_synced', []))} |
| Conocimiento total | {kb.get('total_items', 0)} items |

---

## 🎯 Análisis AMDA Deep V2.0

### Distribución por Categoría

"""
        # Tabla de categorías
        for category, count in sorted(by_category.items(), key=lambda x: x[1], reverse=True):
            percentage = (count / total_sorries * 100) if total_sorries > 0 else 0
            md += f"- **{category}**: {count} ({percentage:.1f}%)\n"
        
        md += f"""
---

## 🤖 Resultados AURON Neural Multi V2.0

### Transformaciones Realizadas

| Tipo | Cantidad |
|------|----------|
| Éxitos | {success} |
| Fallos | {fail} |
| Tasa de éxito | {success/(success+fail)*100:.1f}% |

### Aprendizaje del Sistema

| Métrica | Valor |
|---------|-------|
| Patrones aprendidos | {learning_stats.get('total_patterns', 0)} |
| Nuevos patrones | {learning_stats.get('patterns_learned', 0)} |
| Tasa de aprendizaje | {learning_stats.get('success_rate', 0)*100:.1f}% |
| Repos utilizados | {len(learning_stats.get('repos_used', []))} |

### Repositorios Fuente

"""
        for repo in learning_stats.get('repos_used', []):
            md += f"- {repo}\n"
        
        md += f"""
---

## 📚 Base de Conocimiento NOESIS

### Sincronización de Repositorios

**Ubicación:** `{kb.get('location', '/tmp/noesis_knowledge_v2')}`

| Tipo | Cantidad |
|------|----------|
| Definiciones | {kb.get('definitions', 0)} |
| Teoremas | {kb.get('theorems', 0)} |
| Patrones de prueba | {kb.get('proof_patterns', 0)} |
| **Total** | {kb.get('total_items', 0)} |

### Repositorios Sincronizados

"""
        for repo in kb.get('repos_synced', []):
            md += f"- {repo}\n"
        
        md += f"""
---

## 📈 Proyecciones

"""
        if success > 0:
            remaining = total_sorries - success
            cycles_needed = remaining / success if success > 0 else 0
            hours_estimated = cycles_needed * 2  # 2 horas por ciclo
            
            md += f"""
- **Sorries restantes:** {remaining}
- **Ciclos estimados:** {cycles_needed:.1f}
- **Tiempo estimado:** {hours_estimated:.1f} horas
- **Fecha estimada de completitud:** {datetime.now().timestamp() + hours_estimated * 3600}
"""
        
        md += """
---

## 🔧 Siguiente Ciclo

**Prioridades:**
1. Continuar con categorías `trivial` y `library_search`
2. Aprender de repositorios con alta similitud
3. Expandir patrones de éxito

**Mejoras sugeridas:**
- Incrementar timeout de compilación si es necesario
- Ajustar umbral de similitud cross-repo
- Revisar patrones fallidos para aprendizaje

---

*Generado automáticamente por NOESIS CEREBRAL V2.0*

**Frecuencia fundamental:** 141.7001 Hz · **Coherencia QCAL:** C = 244.36
"""
        
        return md
    
    def generate_json_metrics(self):
        """Genera métricas en formato JSON"""
        metrics = {
            "timestamp": datetime.now().isoformat(),
            "version": "V2.0",
            "amda": {
                "total_sorries": self.amda_report.get("summary", {}).get("total_sorries", 0),
                "by_category": self.amda_report.get("summary", {}).get("by_category", {})
            },
            "auron": {
                "success": self.auron_results.get("success", 0),
                "fail": self.auron_results.get("fail", 0),
                "learning": self.auron_results.get("learning_stats", {})
            },
            "noesis": {
                "knowledge_base": self.noesis_report.get("knowledge_base", {})
            }
        }
        
        return metrics
    
    def save_reports(self, output_dir="."):
        """Guarda los reportes"""
        output_dir = Path(output_dir)
        output_dir.mkdir(parents=True, exist_ok=True)
        
        # Reporte Markdown
        md_report = self.generate_markdown_report()
        md_file = output_dir / 'metrics_report.md'
        with open(md_file, 'w', encoding='utf-8') as f:
            f.write(md_report)
        
        print(f"✅ Reporte Markdown: {md_file}")
        
        # Métricas JSON
        json_metrics = self.generate_json_metrics()
        json_file = output_dir / 'metrics.json'
        with open(json_file, 'w') as f:
            json.dump(json_metrics, f, indent=2)
        
        print(f"✅ Métricas JSON: {json_file}")
        
        return md_file, json_file

def main():
    """Función principal"""
    if len(sys.argv) < 4:
        print("Uso: metrics_generator.py <amda_report.json> <auron_results.json> <noesis_report.json>")
        sys.exit(1)
    
    amda_report = Path(sys.argv[1])
    auron_results = Path(sys.argv[2])
    noesis_report = Path(sys.argv[3])
    
    generator = MetricsGenerator(amda_report, auron_results, noesis_report)
    md_file, json_file = generator.save_reports()
    
    print(f"\n✅ Métricas generadas exitosamente")

if __name__ == "__main__":
    main()
