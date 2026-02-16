#!/usr/bin/env python3
"""
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
            print(f"Error leyendo {filepath}: {e}")
            return
            
        for i, line in enumerate(lines):
            if 'sorry' in line:
                # Obtener contexto (5 líneas antes y después)
                start = max(0, i-5)
                end = min(len(lines), i+6)
                context = '\n'.join(lines[start:end])
                
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
    
    analyzer = AMDAAnalyzer()
    return analyzer.run(args.output)


if __name__ == "__main__":
    sys.exit(main())
