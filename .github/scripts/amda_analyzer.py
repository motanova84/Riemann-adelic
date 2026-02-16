#!/usr/bin/env python3
"""
AMDA ANALYZER - Analizador Multi-Dimensional Autónomo
Analiza archivos Lean para categorizar sorrys y determinar estrategias de eliminación.

Autor: José Manuel Mota Burruezo (JMMB Ψ✧)
Fecha: 16 febrero 2026
DOI: 10.5281/zenodo.17379721
"""

import json
import re
import sys
import pickle
from pathlib import Path
from datetime import datetime
import argparse
from collections import defaultdict


class AMDAAnalyzer:
    """Analizador de sorrys con soporte multi-repositorio."""
    
    CATEGORIES = {
        'trivial': ['rfl', 'trivial', 'exact', 'refl'],
        'library_search': ['exact?', 'apply?', 'simp?', 'omega'],
        'spectral': ['H_ψ', 'spectrum', 'eigenvalue', 'λ', 'spectral'],
        'correspondence': ['adelic', 'trace', 'bijection', 'correspondence'],
        'structural': ['funext', 'ext', 'intro', 'cases'],
        'qcal': ['QCAL', 'C =', 'f₀', '141.7', 'coherence']
    }
    
    def __init__(self, repo_root, cross_repo=False):
        self.repo_root = Path(repo_root)
        self.cross_repo = cross_repo
        self.knowledge_base = Path('/tmp/noesis_knowledge')
        self.formalization_dir = self.repo_root / 'formalization' / 'lean'
        self.sorry_data = []
        
    def log(self, message, level="INFO"):
        """Log mensaje a consola."""
        print(f"[{level}] {message}")
    
    def categorize_sorry(self, context):
        """Categoriza un sorry basado en su contexto."""
        scores = defaultdict(int)
        
        for category, keywords in self.CATEGORIES.items():
            for keyword in keywords:
                if keyword.lower() in context.lower():
                    scores[category] += 1
        
        if scores:
            return max(scores, key=scores.get)
        return 'unknown'
    
    def analyze_file(self, filepath):
        """Analiza un archivo Lean para encontrar sorrys."""
AMDA - Analizador Matemático Deductivo Autónomo
Escanea archivos Lean, clasifica 'sorry' y determina estrategias óptimas
"""

import re
import json
import subprocess
from pathlib import Path
import sys
from collections import defaultdict
import argparse


class AMDAAnalyzer:
    def __init__(self):
        self.repo_root = Path(__file__).parent.parent.parent
        self.lean_dir = self.repo_root / 'formalization' / 'lean'
        self.results = defaultdict(list)
        
    # Patrones de clasificación
    PATTERNS = {
        "correspondence": re.compile(
            r'sorry.*?(?:H_ψ|H_Ψ|spectrum|eigenvalue|zeta|ζ|ceros).*?(?:correspond|equiv|bij|↔)',
            re.IGNORECASE | re.DOTALL
        ),
        "trivial": re.compile(
            r'sorry.*?(?:rfl|trivial|refl|simp|by\s+simp|by\s+norm_num)',
            re.IGNORECASE | re.DOTALL
        ),
        "library_search": re.compile(
            r'sorry.*?(?:exact\?|apply\?|library_search|solve_by_elim)',
            re.IGNORECASE | re.DOTALL
        ),
        "qcal": re.compile(
            r'sorry.*?(?:QCAL|Noetic|coherence|coherencia|Ψ)',
            re.IGNORECASE | re.DOTALL
        ),
        "structured": re.compile(
            r'sorry.*?(?:theorem|lemma|have|show|calc).{50,}',
            re.IGNORECASE | re.DOTALL
        )
    }
    
    def scan_file(self, filepath):
        """Escanea un archivo Lean en busca de sorry"""
        try:
            with open(filepath, 'r', encoding='utf-8') as f:
                content = f.read()
                lines = content.split('\n')
        except Exception as e:
            self.log(f"Error leyendo {filepath}: {e}", level="ERROR")
            return []
        
        sorrys = []
        for i, line in enumerate(lines):
            if 'sorry' in line and not line.strip().startswith('--'):
                # Obtener contexto
            print(f"Error leyendo {filepath}: {e}")
            return
            
        for i, line in enumerate(lines):
            if 'sorry' in line:
                # Obtener contexto (5 líneas antes y después)
                start = max(0, i-5)
                end = min(len(lines), i+6)
                context = '\n'.join(lines[start:end])
                
                # Categorizar
                category = self.categorize_sorry(context)
                
                # Buscar conocimiento cross-repo si está habilitado
                cross_repo_hint = {}
                if self.cross_repo:
                    cross_repo_hint = self.analyze_with_cross_repo_knowledge(context, category)
                
                sorry_info = {
                    'file': str(filepath.relative_to(self.repo_root)),
                    'line': i + 1,
                    'category': category,
                    'context': context,
                    'cross_repo_hint': cross_repo_hint
                }
                sorrys.append(sorry_info)
        
        return sorrys
    
    def analyze_with_cross_repo_knowledge(self, sorry_context, category):
        """Utiliza NOESIS CEREBRAL para enriquecer el análisis."""
        kb_file = self.knowledge_base / 'knowledge.pkl'
        if not kb_file.exists():
            return {'cross_repo_hint': False}
        
        try:
            with open(kb_file, 'rb') as f:
                knowledge = pickle.load(f)
        except Exception as e:
            self.log(f"Error cargando knowledge base: {e}", level="WARN")
            return {'cross_repo_hint': False}
        
        # Buscar patrones similares
        similar_patterns = []
        for pattern_id, pattern in knowledge.get('sorry_patterns', {}).items():
            if pattern.get('type') == category and pattern['repo'] != 'Riemann-adelic':
                # Calcular similitud simple (mejorable)
                sorry_words = set(w.lower() for w in sorry_context.split() if len(w) > 3)
                pattern_words = set(w.lower() for w in pattern['context'].split() if len(w) > 3)
                common = sorry_words & pattern_words
                similarity = len(common)
                
                if similarity > 5:
                    similar_patterns.append({
                        'repo': pattern['repo'],
                        'file': pattern['file'],
                        'line': pattern['line'],
                        'context': pattern['context'],
                        'similarity': similarity
                    })
        
        # Ordenar por similitud
        similar_patterns.sort(key=lambda x: x['similarity'], reverse=True)
        
        if similar_patterns:
            best = similar_patterns[0]
            return {
                'cross_repo_hint': True,
                'source_repo': best['repo'],
                'source_file': best['file'],
                'source_line': best['line'],
                'suggested_pattern': best['context'],
                'similarity': best['similarity']
            }
        
        return {'cross_repo_hint': False}
    
    def analyze_all(self):
        """Analiza todos los archivos Lean en formalization/lean."""
        self.log("🔍 AMDA ANALYZER - Iniciando análisis...")
        
        lean_files = list(self.formalization_dir.rglob('*.lean'))
        self.log(f"📚 Encontrados {len(lean_files)} archivos Lean")
        
        total_sorrys = 0
        for lean_file in lean_files:
            sorrys = self.analyze_file(lean_file)
            total_sorrys += len(sorrys)
            self.sorry_data.extend(sorrys)
        
        self.log(f"📊 Total de sorrys encontrados: {total_sorrys}")
        
        # Estadísticas por categoría
        category_counts = defaultdict(int)
        for sorry in self.sorry_data:
            category_counts[sorry['category']] += 1
        
        self.log("📈 Distribución por categorías:")
        for category, count in sorted(category_counts.items(), key=lambda x: x[1], reverse=True):
            percentage = (count / total_sorrys * 100) if total_sorrys > 0 else 0
            self.log(f"   - {category}: {count} ({percentage:.1f}%)")
        
        # Estadísticas de cross-repo hints
        if self.cross_repo:
            cross_repo_count = sum(1 for s in self.sorry_data if s['cross_repo_hint'].get('cross_repo_hint'))
            self.log(f"🔗 Sorrys con conocimiento cross-repo: {cross_repo_count}")
        
        return self.sorry_data
    
    def save_report(self, output_file):
        """Guarda el reporte de análisis."""
        report = {
            'timestamp': datetime.now().isoformat(),
            'total_sorrys': len(self.sorry_data),
            'cross_repo_enabled': self.cross_repo,
            'sorrys': self.sorry_data
        }
        
        output_path = self.repo_root / output_file
        with open(output_path, 'w') as f:
            json.dump(report, f, indent=2)
        
        self.log(f"✅ Reporte guardado en {output_path}")
        return output_path


def main():
    """Punto de entrada principal."""
    parser = argparse.ArgumentParser(description='AMDA Analyzer - Análisis de sorrys con soporte multi-repo')
    parser.add_argument('--cross-repo', action='store_true',
                        help='Habilitar análisis con conocimiento cross-repo')
    parser.add_argument('--output', default='amda_report.json',
                # Clasificar el sorry
                category = self.classify_sorry(context)
                
                self.results[str(filepath.relative_to(self.repo_root))].append({
                    "line": i+1,
                    "code": line.strip(),
                    "context": context,
                    "category": category,
                    "priority": self.get_priority(category),
                    "strategy": self.get_strategy(category, context)
                })
    
    def classify_sorry(self, context):
        """Clasifica un sorry según su contexto"""
        for category, pattern in self.PATTERNS.items():
            if pattern.search(context):
                return category
        return "unknown"
    
    def get_priority(self, category):
        """Asigna prioridad basada en la categoría"""
        priorities = {
            "correspondence": "🔴 ALTA",
            "structured": "🟡 MEDIA",
            "library_search": "🟢 BAJA",
            "trivial": "⚪ INMEDIATA",
            "qcal": "🟡 MEDIA",
            "unknown": "⚪ REVISAR"
        }
        return priorities.get(category, "⚪ REVISAR")
    
    def get_strategy(self, category, context):
        """Determina la estrategia óptima para eliminar el sorry"""
        strategies = {
            "correspondence": """
                -- Estrategia: Correspondencia espectral
                -- Requiere: teoremas de conexión H_Ψ ↔ ζ(s)
                -- Pasos:
                --   1. Aplicar fórmula de traza: `trace_formula`
                --   2. Usar biyección de Guinand-Weil: `guinand_weil_bijection`
                --   3. Concluir con caracterización espectral: `spectral_characterization`
            """,
            "trivial": """
                -- Estrategia: Reemplazo directo
                -- Posibles sustituciones:
                --   `sorry` → `rfl`
                --   `sorry` → `trivial`
                --   `sorry` → `by norm_num`
                --   `sorry` → `by simp`
            """,
            "library_search": """
                -- Estrategia: Búsqueda en mathlib
                -- Comandos a probar:
                --   `exact?`
                --   `apply?`
                --   `library_search`
                --   `solve_by_elim`
            """,
            "qcal": """
                -- Estrategia: Lemas de coherencia QCAL
                -- Usar: `QCAL.Noesis.spectral_reflexivity`
                --       `QCAL.Noetic.coherence_tensor`
                --       `QCAL.Frequency.resonance`
            """
        }
        return strategies.get(category, "-- Estrategia: Análisis manual requerido")
    
    def run(self, output_path=None):
        """Ejecuta el análisis completo"""
        if not self.lean_dir.exists():
            print(f"Error: Directorio Lean no encontrado: {self.lean_dir}")
            return 1
            
        lean_files = list(self.lean_dir.rglob('*.lean'))
        print(f"🔍 AMDA escaneando {len(lean_files)} archivos Lean...")
        
        for file in lean_files:
            self.scan_file(file)
        
        # Guardar resultados
        if output_path is None:
            output_path = self.repo_root / 'amda_report.json'
        else:
            output_path = Path(output_path)
            
        with open(output_path, 'w') as f:
            json.dump(self.results, f, indent=2)
        
        # Estadísticas
        total = sum(len(v) for v in self.results.values())
        by_category = defaultdict(int)
        for file, sorries in self.results.items():
            for s in sorries:
                by_category[s['category']] += 1
        
        print(f"📊 AMDA Report:")
        print(f"   Total sorries: {total}")
        print(f"   Por categoría: {dict(by_category)}")
        print(f"   Reporte guardado en: {output_path}")
        
        # Guardar también estadísticas en un archivo separado
        stats_path = output_path.parent / 'amda_stats.json'
        stats = {
            "total": total,
            "by_category": dict(by_category),
            "by_file": {k: len(v) for k, v in self.results.items()},
            "timestamp": str(Path(__file__).stat().st_mtime)
        }
        with open(stats_path, 'w') as f:
            json.dump(stats, f, indent=2)
        
        return 0


def main():
    parser = argparse.ArgumentParser(description='AMDA - Analizador de sorries')
    parser.add_argument('--output', type=str, default='amda_report.json',
                        help='Archivo de salida para el reporte')
    
    args = parser.parse_args()
    
    repo_root = Path.cwd()
    analyzer = AMDAAnalyzer(repo_root, cross_repo=args.cross_repo)
    analyzer.analyze_all()
    analyzer.save_report(args.output)
    
    return 0
    analyzer = AMDAAnalyzer()
    return analyzer.run(args.output)


if __name__ == "__main__":
    sys.exit(main())
