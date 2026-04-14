#!/usr/bin/env python3
"""
🍽️ NOESIS DIGESTIVE SYSTEM - EXCRECIÓN
Elimina desechos y prepara el organismo para el próximo ciclo
"""

import json
import subprocess
from pathlib import Path
from datetime import datetime

class DigestiveExcretion:
    def __init__(self):
        self.repo_root = Path(__file__).parent.parent.parent
        
    def clean_backups(self):
        """Elimina archivos de backup antiguos"""
        backups = list(self.repo_root.rglob('*.lean.bak*'))
        removed = 0
        for backup in backups:
            try:
                backup.unlink()
                removed += 1
            except Exception as e:
                print(f"⚠️ No se pudo eliminar {backup}: {e}")
        return removed
    
    def archive_waste(self):
        """Archiva los desechos para análisis futuro"""
        log_file = self.repo_root / '.digestive_log.json'
        waste_file = self.repo_root / 'digestive_waste_archive.json'
        
        if log_file.exists():
            try:
                with open(log_file) as f:
                    log = json.load(f)
                
                # Mover desechos al archivo
                waste = [d for d in log.get('digestions', []) if not d.get('success')]
                
                if waste_file.exists():
                    with open(waste_file) as f:
                        archive = json.load(f)
                else:
                    archive = {'waste': [], 'archived_at': []}
                
                if waste:
                    archive['waste'].extend(waste)
                    archive['archived_at'].append(datetime.now().isoformat())
                    archive['total_waste'] = len(archive['waste'])
                    
                    with open(waste_file, 'w') as f:
                        json.dump(archive, f, indent=2)
                
                # Limpiar desechos del log actual (mantener solo éxitos)
                log['digestions'] = [d for d in log['digestions'] if d.get('success')]
                log['waste'] = 0
                
                with open(log_file, 'w') as f:
                    json.dump(log, f, indent=2)
                
                return len(waste)
            except Exception as e:
                print(f"⚠️ Error archivando desechos: {e}")
                return 0
        return 0
    
    def clean_old_reports(self):
        """Limpia reportes antiguos (mantiene últimos 10)"""
        reports = list(self.repo_root.glob('digestive_*.md'))
        # Mantener solo los últimos 10 reportes
        if len(reports) > 10:
            reports.sort(key=lambda x: x.stat().st_mtime)
            removed = 0
            for report in reports[:-10]:
                try:
                    report.unlink()
                    removed += 1
                except Exception as e:
                    print(f"⚠️ No se pudo eliminar {report}: {e}")
            return removed
        return 0
    
    def clean_temp_meal_files(self):
        """Limpia archivos temporales de comida"""
        temp_files = [
            self.repo_root / 'digestive_meal.json',
        ]
        removed = 0
        for temp_file in temp_files:
            if temp_file.exists():
                try:
                    temp_file.unlink()
                    removed += 1
                except Exception as e:
                    print(f"⚠️ No se pudo eliminar {temp_file}: {e}")
        return removed
    
    def analyze_waste(self):
        """Analiza los desechos para futuras mejoras"""
        waste_file = self.repo_root / 'digestive_waste_archive.json'
        if waste_file.exists():
            with open(waste_file) as f:
                archive = json.load(f)
            
            waste = archive.get('waste', [])
            
            # Analizar patrones de fracaso
            failure_patterns = {}
            for w in waste:
                file_name = Path(w['file']).name
                failure_patterns[file_name] = failure_patterns.get(file_name, 0) + 1
            
            return {
                'total_waste': len(waste),
                'top_failure_files': sorted(failure_patterns.items(), key=lambda x: x[1], reverse=True)[:5]
            }
        return {'total_waste': 0, 'top_failure_files': []}
    
    def generate_excretion_report(self, backups_removed, waste_archived, old_reports_removed, temp_removed, waste_analysis):
        """Genera reporte de excreción"""
        report = f"""# 🍽️ NOESIS DIGESTIVE SYSTEM - EXCRECIÓN

**Fecha:** {datetime.now().isoformat()}
**Frecuencia base:** 141.7001 Hz

## 🗑️ Limpieza Realizada

| Actividad | Cantidad |
|-----------|----------|
| 🧹 Backups eliminados | {backups_removed} |
| 📦 Desechos archivados | {waste_archived} |
| 📄 Reportes antiguos eliminados | {old_reports_removed} |
| 🔄 Archivos temporales eliminados | {temp_removed} |

## 📊 Análisis de Desechos

- **Total de desechos archivados:** {waste_analysis['total_waste']}
- **Archivos con más fracasos:**

"""
        for file, count in waste_analysis['top_failure_files']:
            report += f"  - `{file}`: {count} fracasos\n"
        
        report += f"""

## 🧬 Estado Post-Limpieza

- ✅ El organismo está limpio
- ✅ Listo para el próximo ciclo digestivo
- ✅ Coherencia optimizada
- ✅ Espacio liberado

## 💡 Lecciones Aprendidas

El análisis de desechos revela:
- Los archivos con más fracasos pueden requerir estrategias especializadas
- Algunos sorries son más difíciles de digerir que otros
- El organismo aprende tanto de éxitos como de fracasos

## ⏭️ Próximo ciclo

El sistema digestivo descansa. La próxima digestión comenzará cuando el hambre lo requiera.

**Ciclo completo ejecutado:**
1. ✅ Hambre detectada
2. ✅ Alimento ingerido
3. ✅ Comida digerida
4. ✅ Nutrientes asimilados
5. ✅ Desechos excretados

**Estado del organismo:** 💪 Más fuerte y sabio

---
*Generado por el Sistema Digestivo de NOESIS*
"""
        report_path = self.repo_root / 'digestive_excretion_report.md'
        with open(report_path, 'w') as f:
            f.write(report)
        
        print(report)
        return report
    
    def run(self):
        """Ejecuta el proceso de excreción"""
        print("🍽️ Eliminando desechos...")
        
        backups = self.clean_backups()
        waste = self.archive_waste()
        old = self.clean_old_reports()
        temp = self.clean_temp_meal_files()
        waste_analysis = self.analyze_waste()
        
        report = self.generate_excretion_report(backups, waste, old, temp, waste_analysis)
        
        print(f"\n✅ Excreción completa: {backups} backups, {waste} desechos archivados, {old} reportes antiguos, {temp} temporales")
        return report

if __name__ == "__main__":
    excretion = DigestiveExcretion()
    excretion.run()
