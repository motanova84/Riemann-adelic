#!/usr/bin/env python3
"""
AMDA DEEP V2.0 - Advanced Multi-Dimensional Analysis
Categoriza 'sorry' statements en 8 categorías para eliminación inteligente
Parte del sistema NOESIS CEREBRAL V2.0
"""

import json
import re
import sys
from pathlib import Path
from collections import defaultdict
from datetime import datetime

class AMDAAnalyzer:
    """Analizador profundo de sorry statements con categorización multi-dimensional"""
    
    # Patrones actualizados con 8 categorías (PR #1716)
    PATTERNS = {
        "trivial": re.compile(
            r'sorry.*?(?:rfl|trivial|refl|simp|by\s+simp|by\s+norm_num)',
            re.IGNORECASE | re.DOTALL
        ),
        "spectral": re.compile(
            r'sorry.*?(?:H_ψ|H_Ψ|spectrum|eigenvalue|operator|Fredholm|determinant)',
            re.IGNORECASE | re.DOTALL
        ),
        "correspondence": re.compile(
            r'sorry.*?(?:correspond|equiv|bij|bijection|zeta|ζ|ceros|γ).*?(?:H_ψ|spectrum)',
            re.IGNORECASE | re.DOTALL
        ),
        "structural": re.compile(
            r'sorry.*?(?:funext|ext|congr|rw|rewrite|simp)',
            re.IGNORECASE | re.DOTALL
        ),
        "qcal": re.compile(
            r'sorry.*?(?:QCAL|Noetic|coherence|Ψ|f₀|141\.7|888|πCODE)',
            re.IGNORECASE | re.DOTALL
        ),
        "library_search": re.compile(
            r'sorry.*?(?:library_search|exact\?|apply\?|solve_by_elim|simp\?)',
            re.IGNORECASE | re.DOTALL
        ),
        "adelic": re.compile(
            r'sorry.*?(?:ad[ée]lic|S-finite|𝔸|ℚ_p|p-adic|Tate|Weil)',
            re.IGNORECASE | re.DOTALL
        ),
        "analytic": re.compile(
            r'sorry.*?(?:analytic|meromorphic|continuation|gamma|Γ|Riemann)',
            re.IGNORECASE | re.DOTALL
        )
    }
    
    def __init__(self, lean_dir):
        self.lean_dir = Path(lean_dir)
        self.sorries = defaultdict(list)
        self.stats = defaultdict(int)
        
    def log(self, message, level="INFO"):
        """Log con timestamp"""
        timestamp = datetime.now().isoformat()
        print(f"[{timestamp}] [{level}] {message}")
        
    def find_lean_files(self):
        """Encuentra todos los archivos .lean"""
        lean_files = list(self.lean_dir.rglob("*.lean"))
        self.log(f"📁 Encontrados {len(lean_files)} archivos Lean")
        return lean_files
    
    def extract_context(self, lines, line_idx, context_size=3):
        """Extrae contexto alrededor de un sorry"""
        start = max(0, line_idx - context_size)
        end = min(len(lines), line_idx + context_size + 1)
        return '\n'.join(lines[start:end])
    
    def classify_deep(self, code, context):
        """Clasificación multi-categórica de sorry"""
        categories = []
        
        # Verificar cada categoría
        for category, pattern in self.PATTERNS.items():
            if pattern.search(context):
                categories.append(category)
        
        if not categories:
            categories = ["unknown"]
        
        return categories
    
    def analyze_file(self, filepath):
        """Analiza un archivo Lean en busca de sorries"""
        try:
            with open(filepath, 'r', encoding='utf-8') as f:
                content = f.read()
                lines = content.split('\n')
            
            # Buscar todos los 'sorry' con word boundary
            sorry_pattern = re.compile(r'\bsorry\b', re.IGNORECASE)
            for line_idx, line in enumerate(lines):
                if sorry_pattern.search(line):
                    context = self.extract_context(lines, line_idx)
                    categories = self.classify_deep(line, context)
                    
                    # Determinar categoría primaria (primera que coincide)
                    primary_category = categories[0]
                    
                    sorry_info = {
                        "line": line_idx + 1,
                        "code": line.strip(),
                        "context": context,
                        "categories": categories,
                        "primary_category": primary_category
                    }
                    
                    # Guardar relativo al directorio Lean
                    rel_path = str(filepath.relative_to(self.lean_dir.parent))
                    self.sorries[rel_path].append(sorry_info)
                    
                    # Actualizar estadísticas
                    self.stats["total_sorries"] += 1
                    for cat in categories:
                        self.stats[f"category_{cat}"] += 1
                    
        except Exception as e:
            self.log(f"⚠️ Error analizando {filepath}: {e}", "WARNING")
    
    def analyze_all(self):
        """Analiza todos los archivos Lean"""
        self.log("🔍 AMDA DEEP V2.0 - Iniciando análisis...")
        
        lean_files = self.find_lean_files()
        
        for filepath in lean_files:
            self.analyze_file(filepath)
        
        self.log(f"✅ Análisis completo: {self.stats['total_sorries']} sorries encontrados")
        
    def generate_report(self, output_path):
        """Genera reporte JSON con análisis detallado"""
        report = {
            "timestamp": datetime.now().isoformat(),
            "version": "AMDA Deep V2.0",
            "summary": {
                "total_sorries": self.stats["total_sorries"],
                "total_files": len(self.sorries),
                "by_category": {}
            },
            "detailed": dict(self.sorries)
        }
        
        # Resumen por categoría
        for key, value in self.stats.items():
            if key.startswith("category_"):
                category = key.replace("category_", "")
                report["summary"]["by_category"][category] = value
        
        # Calcular porcentajes
        total = self.stats["total_sorries"]
        if total > 0:
            for cat in report["summary"]["by_category"]:
                count = report["summary"]["by_category"][cat]
                percentage = (count / total) * 100
                self.log(f"  - {cat}: {count} ({percentage:.1f}%)")
        
        with open(output_path, 'w', encoding='utf-8') as f:
            json.dump(report, f, indent=2, ensure_ascii=False)
        
        self.log(f"📊 Reporte guardado en: {output_path}")
        
        return report

def main():
    """Función principal"""
    if len(sys.argv) < 3:
        print("Uso: amda_analyzer.py <lean_dir> <output_json>")
        sys.exit(1)
    
    lean_dir = Path(sys.argv[1])
    output_path = Path(sys.argv[2])
    
    if not lean_dir.exists():
        print(f"❌ Error: Directorio {lean_dir} no existe")
        sys.exit(1)
    
    analyzer = AMDAAnalyzer(lean_dir)
    analyzer.analyze_all()
    analyzer.generate_report(output_path)
    
    print(f"\n✅ AMDA Deep V2.0 completado")
    print(f"   Total sorries: {analyzer.stats['total_sorries']}")
    print(f"   Archivos analizados: {len(analyzer.sorries)}")

if __name__ == "__main__":
    main()
