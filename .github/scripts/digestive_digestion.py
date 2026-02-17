#!/usr/bin/env python3
"""
🍽️ NOESIS DIGESTIVE SYSTEM - DIGESTIÓN
Procesa los sorries y extrae nutrientes (SIMULACIÓN SEGURA)
"""

import json
import subprocess
import hashlib
from pathlib import Path
from datetime import datetime
import random

class DigestiveDigestion:
    def __init__(self):
        self.repo_root = Path(__file__).parent.parent.parent
        self.nutrients_extracted = 0
        self.waste_produced = 0
        self.simulation_mode = True  # SIEMPRE en modo simulación para seguridad
        
    def classify_nutrient(self, sorry_content):
        """Clasifica el tipo de nutriente"""
        content = sorry_content.lower()
        if 'rfl' in content or 'trivial' in content:
            return 'carbohidrato_simple'
        elif 'theorem' in content:
            return 'proteína_compleja'
        elif 'calc' in content or 'norm_num' in content:
            return 'grasa_estructural'
        elif 'have' in content or 'simp' in content:
            return 'vitamina'
        else:
            return 'fibra'
    
    def simulate_digestion_strategies(self, content):
        """Simula diferentes estrategias de digestión"""
        strategies = [
            ('sorry', 'by exact?', 0.3),
            ('sorry', 'by apply?', 0.25),
            ('sorry', 'library_search', 0.2),
            ('sorry', 'solve_by_elim', 0.15),
            ('sorry', 'rfl', 0.4),
            ('sorry', 'trivial', 0.35),
            ('sorry', 'by simp', 0.3),
            ('sorry', 'by norm_num', 0.25),
            ('sorry', 'by ring', 0.2),
            ('sorry', 'by field_simp', 0.15),
        ]
        
        # Simular qué estrategia funcionaría mejor
        best_strategy = None
        best_score = 0
        
        for old, new, base_score in strategies:
            # Calcular score basado en el contenido
            score = base_score
            
            # Bonus si hay pistas en el comentario
            if 'algebraic' in content.lower() and 'ring' in new:
                score += 0.3
            if 'simplif' in content.lower() and 'simp' in new:
                score += 0.3
            if 'trivial' in content.lower() and 'trivial' in new:
                score += 0.4
            if 'arithmetic' in content.lower() and 'norm_num' in new:
                score += 0.3
                
            if score > best_score:
                best_score = score
                best_strategy = new
        
        # Simular éxito/fracaso basado en el score
        success = best_score > 0.5 and random.random() < best_score
        
        return success, best_strategy, best_score
    
    def digest_sorry(self, file_path, line, content):
        """Simula digestión de un sorry individual"""
        # SIMULACIÓN: NO modifica archivos reales
        success, strategy, confidence = self.simulate_digestion_strategies(content)
        
        if success:
            nutrient_type = self.classify_nutrient(content)
            self.nutrients_extracted += 1
            self.log_digestion(file_path, line, strategy, nutrient_type, success, confidence)
            return True, nutrient_type, strategy, confidence
        else:
            self.waste_produced += 1
            self.log_digestion(file_path, line, None, None, success, confidence)
            return False, None, None, confidence
    
    def log_digestion(self, file_path, line, solution, nutrient_type, success, confidence):
        """Registra el proceso digestivo"""
        log_file = self.repo_root / '.digestive_log.json'
        
        if log_file.exists():
            with open(log_file) as f:
                log = json.load(f)
        else:
            log = {
                'digestions': [], 
                'nutrients': {}, 
                'waste': 0,
                'last_meal': datetime.now().isoformat()
            }
        
        entry = {
            'timestamp': datetime.now().isoformat(),
            'file': str(file_path),
            'line': line,
            'solution': solution,
            'nutrient_type': nutrient_type,
            'success': success,
            'confidence': confidence,
            'simulation': self.simulation_mode
        }
        
        log['digestions'].append(entry)
        log['last_meal'] = datetime.now().isoformat()
        
        if success:
            log['nutrients'][nutrient_type] = log['nutrients'].get(nutrient_type, 0) + 1
        else:
            log['waste'] = log.get('waste', 0) + 1
        
        with open(log_file, 'w') as f:
            json.dump(log, f, indent=2)
    
    def digest_meal(self, meal):
        """Digiere una comida completa"""
        results = []
        print("🍽️ Iniciando digestión (MODO SIMULACIÓN)...")
        
        for i, sorry in enumerate(meal, 1):
            success, nutrient, strategy, confidence = self.digest_sorry(
                sorry['file'], 
                sorry['line'], 
                sorry['content']
            )
            results.append({
                'sorry': sorry,
                'success': success,
                'nutrient': nutrient,
                'strategy': strategy,
                'confidence': confidence
            })
            
            if i % 10 == 0:
                print(f"   Procesados {i}/{len(meal)} sorries...")
        
        print(f"✅ Digestión completada: {self.nutrients_extracted} éxitos, {self.waste_produced} desechos")
        return results
    
    def generate_digestion_report(self, results):
        """Genera reporte de digestión"""
        successes = sum(1 for r in results if r['success'])
        
        report = f"""# 🍽️ NOESIS DIGESTIVE SYSTEM - DIGESTIÓN

**Fecha:** {datetime.now().isoformat()}
**Comida procesada:** {len(results)} sorries
**Modo:** {'🔬 SIMULACIÓN SEGURA' if self.simulation_mode else '⚠️ REAL'}

## 📊 Resultados Digestivos

| Métrica | Valor |
|---------|-------|
| ✅ Digeridos exitosamente | {successes} ({successes/len(results)*100:.1f}%) |
| ❌ Desechados | {len(results) - successes} ({(len(results)-successes)/len(results)*100:.1f}%) |
| 🥗 Nutrientes extraídos | {self.nutrients_extracted} |
| 🗑️ Desperdicio producido | {self.waste_produced} |

## 🥗 Nutrientes Obtenidos

"""
        log_file = self.repo_root / '.digestive_log.json'
        if log_file.exists():
            with open(log_file) as f:
                log = json.load(f)
            nutrients = log.get('nutrients', {})
            for nutrient, count in sorted(nutrients.items(), key=lambda x: x[1], reverse=True):
                emoji = {'carbohidrato_simple': '🍞', 'proteína_compleja': '🥩', 
                        'vitamina': '🍊', 'fibra': '🥬', 'grasa_estructural': '🥑'}.get(nutrient, '🍽️')
                report += f"- {emoji} {nutrient}: {count}\n"
        
        report += f"""

## 🎯 Estrategias Más Exitosas

"""
        # Analizar mejores estrategias
        strategy_stats = {}
        for r in results:
            if r['success'] and r['strategy']:
                strategy = r['strategy']
                if strategy not in strategy_stats:
                    strategy_stats[strategy] = {'count': 0, 'confidence': []}
                strategy_stats[strategy]['count'] += 1
                strategy_stats[strategy]['confidence'].append(r['confidence'])
        
        for strategy, stats in sorted(strategy_stats.items(), key=lambda x: x[1]['count'], reverse=True):
            avg_conf = sum(stats['confidence']) / len(stats['confidence']) if stats['confidence'] else 0
            report += f"- `{strategy}`: {stats['count']} éxitos (confianza promedio: {avg_conf:.1%})\n"
        
        report += f"""

## 🧬 Estado del Organismo

- **Energía metabólica:** {self.nutrients_extracted * 10} unidades
- **Coherencia post-digestión:** {'En aumento ↗️' if successes > len(results)/2 else 'Estable →'}
- **Frecuencia base:** 141.7001 Hz
- **Modo de operación:** {'Simulación segura (no modifica archivos)' if self.simulation_mode else 'Modificación real'}

## 📈 Ejemplos de Digestión Exitosa

"""
        # Mostrar algunos ejemplos exitosos
        successful = [r for r in results if r['success']][:5]
        for r in successful:
            report += f"- `{r['sorry']['file']}:{r['sorry']['line']}` → `{r['strategy']}` (confianza: {r['confidence']:.1%})\n"
        
        report += f"""

## ⏭️ Próximo paso

La comida ha sido procesada. Ahora el organismo debe ASIMILAR los nutrientes.

⚠️ **NOTA IMPORTANTE:** Esta digestión fue ejecutada en MODO SIMULACIÓN.
Los archivos Lean NO han sido modificados. Para aplicar cambios reales,
se requiere revisión manual y pruebas de compilación.

---
*Generado por el Sistema Digestivo de NOESIS*
"""
        report_path = self.repo_root / 'digestive_digestion_report.md'
        with open(report_path, 'w') as f:
            f.write(report)
        
        print(report)
        return report

if __name__ == "__main__":
    digestion = DigestiveDigestion()
    
    # Cargar la comida preparada
    meal_file = Path(__file__).parent.parent.parent / 'digestive_meal.json'
    if meal_file.exists():
        with open(meal_file) as f:
            meal = json.load(f)
        results = digestion.digest_meal(meal)
        digestion.generate_digestion_report(results)
        print(f"\n🍽️ Digestión completada: {sum(1 for r in results if r['success'])} éxitos de {len(results)}")
    else:
        print("⚠️ No se encontró comida preparada. Ejecuta primero digestive_ingestion.py")
