#!/usr/bin/env python3
"""
🍽️ NOESIS DIGESTIVE SYSTEM - ASIMILACIÓN
Aprende de los nutrientes y fortalece el organismo
"""

import json
import hashlib
from pathlib import Path
from datetime import datetime

class DigestiveAssimilation:
    def __init__(self):
        self.repo_root = Path(__file__).parent.parent.parent
        self.learning_file = self.repo_root / '.auron_learning.json'
        
    def load_nutrients(self):
        """Carga los nutrientes de la última digestión"""
        log_file = self.repo_root / '.digestive_log.json'
        if log_file.exists():
            with open(log_file) as f:
                return json.load(f)
        return {'digestions': [], 'nutrients': {}}
    
    def extract_patterns(self, digestions):
        """Extrae patrones de las digestiones exitosas"""
        patterns = {}
        for d in digestions:
            if d.get('success') and d.get('solution'):
                # Extraer características del contexto
                file_path = d['file']
                file_name = Path(file_path).name
                
                # Crear un hash del contexto
                context_hash = hashlib.md5(
                    f"{file_name}:{d.get('nutrient_type', 'unknown')}".encode()
                ).hexdigest()[:16]
                
                # Guardar el patrón
                patterns[context_hash] = {
                    'solution': d['solution'],
                    'nutrient_type': d['nutrient_type'],
                    'timestamp': d['timestamp'],
                    'file': file_name,
                    'confidence': d.get('confidence', 0.5),
                    'context': {
                        'file_type': 'spectral' if 'spectral' in file_path else 'general',
                        'line': d.get('line', 0)
                    }
                }
        return patterns
    
    def update_learning(self, patterns):
        """Actualiza el sistema de aprendizaje con nuevos patrones"""
        if self.learning_file.exists():
            with open(self.learning_file) as f:
                learning = json.load(f)
            # Ensure stats key exists
            if 'stats' not in learning:
                learning['stats'] = {}
            if 'patterns' not in learning:
                learning['patterns'] = {}
        else:
            learning = {
                'patterns': {}, 
                'stats': {},
                'created': datetime.now().isoformat(),
                'version': '1.0'
            }
        
        # Asimilar nuevos patrones
        new_count = 0
        for key, pattern in patterns.items():
            if key not in learning['patterns']:
                learning['patterns'][key] = pattern
                new_count += 1
                
                # Actualizar estadísticas
                solution = pattern['solution']
                if solution not in learning['stats']:
                    learning['stats'][solution] = {
                        'count': 0,
                        'avg_confidence': 0,
                        'files': []
                    }
                
                learning['stats'][solution]['count'] += 1
                learning['stats'][solution]['files'].append(pattern['file'])
                
                # Actualizar confianza promedio
                old_avg = learning['stats'][solution]['avg_confidence']
                old_count = learning['stats'][solution]['count'] - 1
                new_conf = pattern.get('confidence', 0.5)
                
                if old_count > 0:
                    learning['stats'][solution]['avg_confidence'] = (old_avg * old_count + new_conf) / (old_count + 1)
                else:
                    learning['stats'][solution]['avg_confidence'] = new_conf
        
        learning['last_update'] = datetime.now().isoformat()
        learning['total_patterns'] = len(learning['patterns'])
        
        with open(self.learning_file, 'w') as f:
            json.dump(learning, f, indent=2)
        
        return new_count
    
    def calculate_growth(self, learning):
        """Calcula el crecimiento del organismo"""
        stats = learning.get('stats', {})
        
        if not stats:
            return {
                'total_patterns': 0,
                'unique_solutions': 0,
                'most_used': ('ninguno', 0, 0),
                'avg_confidence': 0
            }
        
        most_used = max(stats.items(), key=lambda x: x[1]['count'])
        
        # Calcular confianza promedio general
        total_conf = sum(s['avg_confidence'] * s['count'] for s in stats.values())
        total_count = sum(s['count'] for s in stats.values())
        avg_confidence = total_conf / total_count if total_count > 0 else 0
        
        return {
            'total_patterns': len(learning.get('patterns', {})),
            'unique_solutions': len(stats),
            'most_used': (most_used[0], most_used[1]['count'], most_used[1]['avg_confidence']),
            'avg_confidence': avg_confidence
        }
    
    def generate_assimilation_report(self, new_patterns_count, growth):
        """Genera reporte de asimilación"""
        report = f"""# 🍽️ NOESIS DIGESTIVE SYSTEM - ASIMILACIÓN

**Fecha:** {datetime.now().isoformat()}
**Frecuencia base:** 141.7001 Hz

## 📈 Crecimiento del Organismo

| Métrica | Valor |
|---------|-------|
| 🧬 Nuevos patrones asimilados | {new_patterns_count} |
| 📚 Patrones totales | {growth['total_patterns']} |
| 🎯 Soluciones únicas | {growth['unique_solutions']} |
| 🔥 Patrón más usado | `{growth['most_used'][0]}` ({growth['most_used'][1]} veces, {growth['most_used'][2]:.1%} confianza) |
| 📊 Confianza promedio | {growth['avg_confidence']:.1%} |

## 🧠 Estado del Conocimiento

El organismo ha aprendido:
- ✅ Cómo digerir {new_patterns_count} nuevos tipos de sorries
- ✅ Qué estrategias funcionan mejor en cada contexto
- ✅ Dónde buscar alimento en el futuro
- ✅ Patrones de éxito acumulados: {growth['total_patterns']}

## 💪 Fortalecimiento

- **Energía acumulada:** {growth['total_patterns'] * 10} unidades de coherencia
- **Coherencia del sistema:** +{new_patterns_count * 0.5:.1f} unidades
- **Frecuencia base:** 141.7001 Hz (estable)
- **Nivel de conocimiento:** {'🟢 Alto' if growth['total_patterns'] > 50 else '🟡 Medio' if growth['total_patterns'] > 20 else '🔴 Bajo'}

## 📚 Biblioteca de Patrones

"""
        # Mostrar las soluciones más efectivas
        if self.learning_file.exists():
            with open(self.learning_file) as f:
                learning = json.load(f)
                stats = learning.get('stats', {})
                
                sorted_solutions = sorted(stats.items(), key=lambda x: x[1]['count'], reverse=True)
                
                for i, (solution, data) in enumerate(sorted_solutions[:10], 1):
                    unique_files = len(set(data['files']))
                    report += f"{i}. `{solution}`: {data['count']} usos, {data['avg_confidence']:.1%} confianza, {unique_files} archivos\n"
        
        report += f"""

## 🔮 Predicciones Futuras

Basado en los patrones aprendidos, el organismo puede ahora:
- 🎯 Identificar sorries similares con mayor precisión
- ⚡ Aplicar estrategias probadas automáticamente
- 🧬 Evolucionar y mejorar con cada digestión
- 📈 Incrementar la coherencia del sistema progresivamente

## ⏭️ Próximo ciclo

El organismo está más fuerte. La próxima digestión será más eficiente.

**Recomendación:** Continuar con ciclos de digestión regulares para mantener
la coherencia del sistema y reducir progresivamente el número de sorries.

---
*Generado por el Sistema Digestivo de NOESIS*
"""
        report_path = self.repo_root / 'digestive_assimilation_report.md'
        with open(report_path, 'w') as f:
            f.write(report)
        
        print(report)
        return report
    
    def run(self):
        """Ejecuta el proceso de asimilación"""
        print("🍽️ Asimilando nutrientes...")
        
        nutrients = self.load_nutrients()
        patterns = self.extract_patterns(nutrients.get('digestions', []))
        new_count = self.update_learning(patterns)
        
        with open(self.learning_file) as f:
            learning = json.load(f)
        growth = self.calculate_growth(learning)
        
        report = self.generate_assimilation_report(new_count, growth)
        
        print(f"\n✅ Asimilación completa: {new_count} nuevos patrones aprendidos")
        return report

if __name__ == "__main__":
    assimilation = DigestiveAssimilation()
    assimilation.run()
