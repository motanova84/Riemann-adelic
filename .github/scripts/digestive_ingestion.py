#!/usr/bin/env python3
"""
🍽️ NOESIS DIGESTIVE SYSTEM - INGESTA
Toma los sorries como alimento
"""

import json
import subprocess
import random
from pathlib import Path
from datetime import datetime

class DigestiveIngestion:
    def __init__(self):
        self.repo_root = Path(__file__).parent.parent.parent
        self.meal_size = 50  # Máximo de sorries por comida
        self.meal = []
        
    def find_sorries(self):
        """Encuentra todos los sorries disponibles"""
        try:
            result = subprocess.run(
                ["grep", "-n", "sorry", "--include=*.lean", "-r", "formalization/lean/"],
                cwd=self.repo_root,
                capture_output=True, 
                text=True
            )
            
            sorries = []
            for line in result.stdout.splitlines():
                if ':' in line:
                    parts = line.split(':', 2)
                    if len(parts) >= 3:
                        file_path = parts[0]
                        line_num = parts[1]
                        content = parts[2] if len(parts) > 2 else ""
                        
                        try:
                            sorries.append({
                                'file': file_path,
                                'line': int(line_num),
                                'content': content.strip(),
                                'digested': False
                            })
                        except ValueError:
                            continue
            return sorries
        except Exception as e:
            print(f"Error encontrando sorries: {e}")
            return []
    
    def select_meal(self):
        """Selecciona una porción de sorries para digerir"""
        all_sorries = self.find_sorries()
        
        if not all_sorries:
            print("⚠️ No se encontraron sorries para digerir")
            return []
        
        # Priorizar sorries por categoría (más simples primero)
        # Esto es como elegir los alimentos más fáciles de digerir
        def priority(sorry):
            content = sorry['content'].lower()
            if 'rfl' in content or 'trivial' in content:
                return 0  # Fácil de digerir
            elif 'simp' in content:
                return 1
            elif 'library_search' in content:
                return 2
            else:
                return 3  # Difícil de digerir
        
        all_sorries.sort(key=priority)
        
        # Tomar una porción
        self.meal = all_sorries[:self.meal_size]
        
        # Guardar la comida para la siguiente fase
        meal_file = self.repo_root / 'digestive_meal.json'
        with open(meal_file, 'w') as f:
            json.dump(self.meal, f, indent=2)
        
        return self.meal
    
    def prepare_meal_report(self):
        """Prepara reporte de la comida"""
        report = f"""# 🍽️ NOESIS DIGESTIVE SYSTEM - INGESTA

**Fecha:** {datetime.now().isoformat()}
**Tamaño de la comida:** {len(self.meal)} sorries

## 📋 Menú del Día

"""
        for i, sorry in enumerate(self.meal[:20], 1):  # Mostrar solo los primeros 20
            content_preview = sorry['content'][:80]
            if len(sorry['content']) > 80:
                content_preview += "..."
            report += f"{i}. `{sorry['file']}:{sorry['line']}` - {content_preview}\n"
        
        if len(self.meal) > 20:
            report += f"\n... y {len(self.meal) - 20} sorries más ...\n"
        
        # Clasificar nutrientes
        categories = {
            'carbohidrato_simple': 0,
            'proteína_compleja': 0,
            'vitamina': 0,
            'fibra': 0
        }
        
        for sorry in self.meal:
            content = sorry['content'].lower()
            if 'rfl' in content or 'trivial' in content:
                categories['carbohidrato_simple'] += 1
            elif 'theorem' in content:
                categories['proteína_compleja'] += 1
            elif 'simp' in content or 'library_search' in content:
                categories['vitamina'] += 1
            else:
                categories['fibra'] += 1
        
        report += f"""

## 🍲 Valor Nutricional

- **Calorías:** {len(self.meal) * 10} unidades de coherencia
- **Proteínas (teoremas):** {categories['proteína_compleja']} unidades
- **Carbohidratos simples (rfl/trivial):** {categories['carbohidrato_simple']} unidades
- **Vitaminas (simp/library_search):** {categories['vitamina']} unidades
- **Fibra (otros):** {categories['fibra']} unidades

## ⏳ Preparación

{'✅ La comida está lista para ser digerida' if self.meal else '⚠️ No hay nada que comer'}

## 📊 Distribución por Archivo

"""
        # Agrupar por archivo
        by_file = {}
        for sorry in self.meal:
            file = sorry['file']
            by_file[file] = by_file.get(file, 0) + 1
        
        for file, count in sorted(by_file.items(), key=lambda x: x[1], reverse=True)[:10]:
            report += f"- `{file}`: {count} sorries\n"
        
        report += f"""

---
*Generado por el Sistema Digestivo de NOESIS*
"""
        report_path = self.repo_root / 'digestive_meal.md'
        with open(report_path, 'w') as f:
            f.write(report)
        
        print(report)
        return report

if __name__ == "__main__":
    ingestion = DigestiveIngestion()
    meal = ingestion.select_meal()
    ingestion.prepare_meal_report()
    print(f"\n🍽️ Comida preparada: {len(meal)} sorries")
