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
                        help='Archivo de salida para el reporte')
    
    args = parser.parse_args()
    
    repo_root = Path.cwd()
    analyzer = AMDAAnalyzer(repo_root, cross_repo=args.cross_repo)
    analyzer.analyze_all()
    analyzer.save_report(args.output)
    
    return 0


if __name__ == "__main__":
    sys.exit(main())
