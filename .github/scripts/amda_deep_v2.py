#!/usr/bin/env python3
"""
AMDA DEEP LEARNING V2.0 - Analizador contextual profundo con IA
Análisis semántico de sorries con búsqueda de soluciones en múltiples repositorios
AMDA DEEP V2.0 - Análisis semántico multi-categórico de sorries
"""

import json
import re
import sys
from pathlib import Path
import pickle
import numpy as np
from collections import defaultdict
from typing import Dict, List, Any, Optional

class AMDADeepV2:
    def __init__(self, lean_dir: Optional[Path] = None):
        self.repo_root = Path(__file__).parent.parent.parent
        self.lean_dir = lean_dir or (self.repo_root / 'formalization' / 'lean')
        self.knowledge_base = Path('/tmp/noesis_knowledge_v2')
        self.knowledge = None
        
        self.results = {
            "total_sorries": 0,
            "by_category": defaultdict(int),
            "by_file": {},
            "enriched_sorries": []
        }
        
        # Cargar conocimiento de otros repositorios
        self.load_knowledge()
        
        # Patrones mejorados con contexto semántico
        self.PATTERNS = {
            "trivial": re.compile(
                r'sorry.*?(?:rfl|trivial|refl|simp|by\s+simp|by\s+norm_num|by\s+exact\s+rfl)',
                re.IGNORECASE | re.DOTALL
            ),
            "correspondence": re.compile(
                r'sorry.*?(?:H_ψ|H_Ψ|spectrum|eigenvalue|zeta|ζ|ceros|γ|γₙ).*?(?:correspond|equiv|bij|↔|bijection)',
                re.IGNORECASE | re.DOTALL
            ),
            "qcal": re.compile(
                r'sorry.*?(?:QCAL|Noetic|coherence|coherencia|Ψ|f₀|141\.7|888|πCODE|resonancia)',
                re.IGNORECASE | re.DOTALL
            ),
            "adelic": re.compile(
                r'sorry.*?(?:ad[ée]lic|S-finite|𝔸|ℚ_p|p-adic|Tate|Weil)',
                re.IGNORECASE | re.DOTALL
            ),
            "spectral": re.compile(
                r'sorry.*?(?:spectral|operator|Fredholm|determinant|trace|traza|Hilbert|Schatten)',
                re.IGNORECASE | re.DOTALL
            ),
            "analytic": re.compile(
                r'sorry.*?(?:analytic|meromorphic|continuation|gamma|Γ|zeta|ζ|Riemann)',
                re.IGNORECASE | re.DOTALL
            )
        }
    
    def load_knowledge(self):
        """Carga el conocimiento de otros repositorios"""
        kb_file = self.knowledge_base / 'knowledge_v2.pkl'
        if kb_file.exists():
            try:
                with open(kb_file, 'rb') as f:
                    self.knowledge = pickle.load(f)
                print(f"✓ Conocimiento cargado: {len(self.knowledge.get('theorems', []))} teoremas")
            except Exception as e:
                print(f"⚠ Error cargando conocimiento: {e}")
                self.knowledge = None
        else:
            print("⚠ Base de conocimiento no encontrada")
            self.knowledge = None
    
    def scan_file_deep(self, filepath: Path):
        """Escaneo profundo con contexto semántico"""
        try:
            with open(filepath, 'r', encoding='utf-8', errors='ignore') as f:
                content = f.read()
                lines = content.split('\n')
        except Exception as e:
            print(f"Error leyendo {filepath}: {e}")
            return
        
        file_sorries = []
        
        for i, line in enumerate(lines):
            if 'sorry' in line:
                # Obtener contexto amplio (10 líneas antes y después)
                start = max(0, i-10)
                end = min(len(lines), i+11)
                context = '\n'.join(lines[start:end])
                
                # Clasificación múltiple
                categories = self.classify_deep(context)
                
                # Buscar soluciones similares en otros repositorios
                similar_solutions = self.find_similar_solutions(context, categories)
                
                # Extraer el teorema o definición circundante
                theorem_context = self.extract_theorem_context(lines, i)
                
                # Calcular complejidad
                complexity = self.calculate_complexity(context)
                
                sorry_info = {
                    "file": str(filepath.relative_to(self.repo_root)),
                    "line": i+1,
                    "code": line.strip(),
                    "context": context,
                    "theorem_context": theorem_context,
                    "categories": categories,
                    "primary_category": max(categories, key=categories.get) if categories else "unknown",
                    "complexity": complexity,
                    "similar_solutions": similar_solutions,
                    "priority": self.calculate_priority(categories, complexity)
                }
                
                file_sorries.append(sorry_info)
                self.results["total_sorries"] += 1
                for cat, weight in categories.items():
                    if weight > 0:
                        self.results["by_category"][cat] += 1
        
        if file_sorries:
            self.results["by_file"][str(filepath.relative_to(self.repo_root))] = file_sorries
            self.results["enriched_sorries"].extend(file_sorries)
    
    def classify_deep(self, context: str) -> Dict[str, float]:
        """Clasificación semántica profunda (múltiples categorías con pesos)"""
        categories = {}
        context_lower = context.lower()
        
        for cat, pattern in self.PATTERNS.items():
            matches = pattern.findall(context)
            categories[cat] = len(matches) if matches else 0
        
        # Normalizar
        total = sum(categories.values())
        if total > 0:
            for cat in categories:
                categories[cat] /= total
        else:
            # Si no hay coincidencias, todas son desconocidas
            categories = {cat: 0.0 for cat in self.PATTERNS.keys()}
            categories["unknown"] = 1.0
        
        return categories
    
    def find_similar_solutions(self, context: str, categories: Dict[str, float]) -> List[Dict]:
        """Busca soluciones similares en otros repositorios"""
        if not self.knowledge:
            return []
        
        solutions = []
        context_words = set(context.lower().split()[:50])
        
        # Buscar en patrones de prueba
        for pattern in self.knowledge.get("proof_patterns", [])[:200]:
            similarity = self.calculate_similarity_jaccard(context, pattern["proof"])
            if similarity > 0.3:  # Umbral de similitud
                solutions.append({
                    "repo": pattern["repo"],
                    "type": "proof_pattern",
                    "similarity": similarity,
                    "preview": pattern["proof"][:200]
                })
        
        # Buscar en teoremas
        for theorem in self.knowledge.get("theorems", [])[:200]:
            similarity = self.calculate_similarity_jaccard(context, theorem["statement"])
            if similarity > 0.3:
                solutions.append({
                    "repo": theorem["repo"],
                    "type": "theorem",
                    "name": theorem["name"],
                    "similarity": similarity,
                    "preview": theorem["statement"][:200]
                })
        
        solutions.sort(key=lambda x: x["similarity"], reverse=True)
        return solutions[:3]  # Top 3
    
    def calculate_similarity_jaccard(self, text1: str, text2: str) -> float:
        """Calcula similitud entre textos usando Jaccard"""
        words1 = set(text1.lower().split())
        words2 = set(text2.lower().split())
        
        if not words1 or not words2:
            return 0.0
        
        intersection = words1 & words2
        union = words1 | words2
        
        return len(intersection) / len(union) if union else 0.0
    
    def extract_theorem_context(self, lines: List[str], sorry_line: int) -> str:
        """Extrae el teorema o definición que contiene el sorry"""
        # Buscar hacia arriba
        theorem_lines = []
        for i in range(sorry_line, max(0, sorry_line - 30), -1):
            line = lines[i]
            theorem_lines.insert(0, line)
            if any(keyword in line for keyword in ['theorem', 'def', 'lemma', 'example']):
                break
        
        # Buscar hacia abajo hasta encontrar un salto de línea significativo
        for i in range(sorry_line+1, min(sorry_line+20, len(lines))):
            line = lines[i]
            theorem_lines.append(line)
            if line.strip() == '':
                break
        
        return '\n'.join(theorem_lines)
    
    def calculate_complexity(self, context: str) -> float:
        """Calcula la complejidad del sorry"""
        score = 0.0
        
        # Longitud del contexto
        score += len(context) / 1000
        
        # Número de símbolos matemáticos
        math_symbols = len(re.findall(r'[∀∃∈⊂∪∩∫∑∏∂∇λμℂℝℚℤ→↔⟨⟩]', context))
        score += math_symbols / 10
        
        # Número de referencias a otros teoremas
        refs = len(re.findall(r'by\s+[a-zA-Z_]+', context))
        score += refs * 0.5
        
        return min(10.0, score)  # Escala 0-10
    
    def calculate_priority(self, categories: Dict[str, float], complexity: float) -> float:
        """Calcula prioridad basada en categorías y complejidad"""
        priority_map = {
            "trivial": 1.0,
            "qcal": 2.0,
            "adelic": 3.0,
            "spectral": 4.0,
            "analytic": 5.0,
            "correspondence": 5.0,
            "unknown": 6.0
        }
        
        if not categories:
            base_priority = 5.0
        else:
            primary = max(categories, key=categories.get)
            base_priority = priority_map.get(primary, 5.0)
        
        # Ajustar por complejidad
        return base_priority + (complexity / 10)
    
    def generate_report(self) -> Dict[str, Any]:
        """Genera reporte enriquecido"""
        avg_complexity = 0.0
        if self.results["enriched_sorries"]:
            avg_complexity = np.mean([s["complexity"] for s in self.results["enriched_sorries"]])
        
        total_similar_solutions = sum(
            len(s.get("similar_solutions", [])) 
            for s in self.results["enriched_sorries"]
        )
        
        repos_with_solutions = set(
            sol["repo"] 
            for s in self.results["enriched_sorries"] 
            for sol in s.get("similar_solutions", [])
        )
        
        report = {
            "summary": {
                "total_sorries": self.results["total_sorries"],
                "by_category": dict(self.results["by_category"]),
                "files_affected": len(self.results["by_file"])
            },
            "detailed": self.results["by_file"],
            "statistics": {
                "avg_complexity": float(avg_complexity),
                "total_similar_solutions": total_similar_solutions,
                "repositories_with_solutions": len(repos_with_solutions),
                "solution_repos": list(repos_with_solutions)
            },
            "metadata": {
                "analysis_date": "2026-02-16",
                "version": "2.0",
                "knowledge_base": self.knowledge is not None
from collections import defaultdict
import pickle

class AmDADeepV2:
    def __init__(self):
        self.repo_root = Path(__file__).parent.parent.parent
        self.lean_dir = self.repo_root / 'formalization' / 'lean'
        self.knowledge_base = Path('/tmp/noesis_knowledge_v2')
        
        # Patrones de clasificación multi-categórica
        self.PATTERNS = {
            "trivial": {
                "keywords": ["rfl", "simp", "norm_num", "trivial", "reflexivity", "refl"],
                "complexity": 1,
                "weight": 0.8
            },
            "correspondence": {
                "keywords": ["correspondence", "bijection", "trace_formula", "spectral_map", "adelic_map"],
                "complexity": 4,
                "weight": 0.7
            },
            "qcal": {
                "keywords": ["QCAL", "Ψ", "H_ψ", "f₀", "141.7001", "C =", "coherence", "frequency"],
                "complexity": 3,
                "weight": 0.75
            },
            "adelic": {
                "keywords": ["adelic", "A_K", "GL", "idele", "local", "global", "restricted"],
                "complexity": 5,
                "weight": 0.6
            },
            "spectral": {
                "keywords": ["spectrum", "eigenvalue", "operator", "Fredholm", "self_adjoint", "trace_class"],
                "complexity": 4,
                "weight": 0.65
            },
            "analytic": {
                "keywords": ["zeta", "ζ", "analytic", "continuation", "meromorphic", "residue"],
                "complexity": 5,
                "weight": 0.6
            }
        }
        
        # Cargar conocimiento de otros repositorios
        self.knowledge = self.load_knowledge()
    
    def log(self, message, level="INFO"):
        """Logging simple"""
        print(f"[{level}] {message}")
    
    def load_knowledge(self):
        """Carga conocimiento de otros repositorios"""
        kb_file = self.knowledge_base / 'knowledge_v2.pkl'
        if kb_file.exists():
            with open(kb_file, 'rb') as f:
                knowledge = pickle.load(f)
            self.log(f"📚 Conocimiento cargado: {len(knowledge.get('proof_patterns', []))} patrones")
            return knowledge
        else:
            self.log("⚠️ Base de conocimiento no encontrada", "WARNING")
            return {"proof_patterns": [], "theorems": [], "definitions": []}
    
    def classify_deep(self, code, context):
        """Clasificación multi-categórica con puntajes"""
        scores = {}
        
        # Texto combinado para análisis
        text = (code + " " + context).lower()
        
        for category, info in self.PATTERNS.items():
            score = 0
            for keyword in info["keywords"]:
                if keyword.lower() in text:
                    score += info["weight"]
            
            if score > 0:
                scores[category] = score
        
        # Si no hay categorías, marcar como desconocido
        if not scores:
            scores["unknown"] = 1.0
        
        # Categoría principal (mayor puntaje)
        primary = max(scores.items(), key=lambda x: x[1])[0] if scores else "unknown"
        
        return {
            "primary_category": primary,
            "all_categories": scores,
            "complexity": self.PATTERNS.get(primary, {}).get("complexity", 5)
        }
    
    def find_similar_from_knowledge(self, code, context, min_similarity=0.3):
        """Busca soluciones similares en la base de conocimiento"""
        if not self.knowledge:
            return []
        
        # Jaccard similarity
        query_words = set((code + " " + context).lower().split())
        solutions = []
        
        for pattern in self.knowledge.get("proof_patterns", []):
            pattern_words = set(pattern["proof"][:200].lower().split())
            
            # Skip if either set is empty or union is empty
            if not query_words or not pattern_words:
                continue
            
            union = query_words | pattern_words
            if not union:
                continue
            
            similarity = len(query_words & pattern_words) / len(union)
            
            if similarity > min_similarity:
                solutions.append({
                    "repo": pattern["repo"],
                    "proof_snippet": pattern["proof"][:100],
                    "similarity": similarity,
                    "type": "proof_pattern"
                })
        
        # Ordenar por similitud
        solutions.sort(key=lambda x: x["similarity"], reverse=True)
        return solutions[:3]
    
    def extract_context(self, lines, line_idx, window=3):
        """Extrae contexto alrededor de un sorry"""
        start = max(0, line_idx - window)
        end = min(len(lines), line_idx + window + 1)
        
        context_lines = lines[start:end]
        return "\n".join(context_lines)
    
    def analyze_file(self, filepath):
        """Analiza un archivo Lean en busca de sorries"""
        try:
            with open(filepath, 'r', encoding='utf-8') as f:
                content = f.read()
                lines = content.split('\n')
        except Exception as e:
            self.log(f"⚠️ Error leyendo {filepath}: {e}", "WARNING")
            return []
        
        sorries = []
        
        for i, line in enumerate(lines):
            if 'sorry' in line:
                # Extraer contexto
                context = self.extract_context(lines, i)
                
                # Clasificar
                classification = self.classify_deep(line, context)
                
                # Buscar soluciones similares
                similar = self.find_similar_from_knowledge(line, context)
                
                sorry_info = {
                    "line": i + 1,
                    "code": line.strip(),
                    "context": context,
                    "primary_category": classification["primary_category"],
                    "all_categories": classification["all_categories"],
                    "complexity": classification["complexity"],
                    "similar_solutions": similar
                }
                
                sorries.append(sorry_info)
        
        return sorries
    
    def analyze_repository(self):
        """Analiza todos los archivos Lean del repositorio"""
        self.log("🔍 AMDA DEEP V2.0 iniciando análisis...")
        
        # Encontrar todos los archivos .lean
        lean_files = list(self.lean_dir.rglob("*.lean"))
        self.log(f"📁 Encontrados {len(lean_files)} archivos .lean")
        
        all_sorries = {}
        total_count = 0
        category_counts = defaultdict(int)
        
        for filepath in lean_files:
            sorries = self.analyze_file(filepath)
            
            if sorries:
                relative_path = str(filepath.relative_to(self.repo_root))
                all_sorries[relative_path] = sorries
                total_count += len(sorries)
                
                # Contar por categoría
                for sorry in sorries:
                    category_counts[sorry["primary_category"]] += 1
        
        # Calcular estadísticas
        category_stats = {}
        for cat, count in category_counts.items():
            percentage = (count / total_count * 100) if total_count > 0 else 0
            category_stats[cat] = {
                "count": count,
                "percentage": percentage
            }
        
        # Generar reporte
        report = {
            "total_sorries": total_count,
            "total_files": len(all_sorries),
            "category_distribution": category_stats,
            "detailed": all_sorries,
            "summary": {
                "most_common_category": max(category_counts.items(), key=lambda x: x[1])[0] if category_counts else "none",
                "avg_complexity": sum(s["complexity"] for sorries in all_sorries.values() for s in sorries) / max(1, total_count)
            }
        }
        
        return report
    
    def run(self, output_path: Optional[Path] = None) -> int:
        """Ejecuta el analizador"""
        if not self.lean_dir.exists():
            print(f"❌ Directorio Lean no encontrado: {self.lean_dir}")
            return 1
        
        lean_files = list(self.lean_dir.rglob('*.lean'))
        print(f"🔍 Analizando {len(lean_files)} archivos Lean...")
        
        for file in lean_files:
            self.scan_file_deep(file)
        
        report = self.generate_report()
        
        if output_path is None:
            output_path = self.repo_root / 'amda_deep_report_v2.json'
        
        with open(output_path, 'w') as f:
            json.dump(report, f, indent=2)
        
        print(f"\n📊 Reporte AMDA Deep V2.0:")
        print(json.dumps(report["summary"], indent=2))
        print(f"\n📈 Estadísticas:")
        print(json.dumps(report["statistics"], indent=2))
        print(f"\n💾 Reporte guardado en: {output_path}")
        
        return 0


def main():
    """Punto de entrada principal"""
    import argparse
    
    parser = argparse.ArgumentParser(description='AMDA DEEP V2.0 - Analizador Contextual')
    parser.add_argument('--lean-dir', type=Path, help='Directorio de archivos Lean')
    parser.add_argument('--output', type=Path, help='Archivo de salida')
    
    args = parser.parse_args()
    
    analyzer = AMDADeepV2(lean_dir=args.lean_dir)
    sys.exit(analyzer.run(output_path=args.output))


if __name__ == "__main__":
    main()
    def generate_report_markdown(self, report):
        """Genera un reporte en markdown"""
        md = f"""# 📊 AMDA DEEP V2.0 - Reporte de Análisis

## Resumen General
- **Total sorries:** {report['total_sorries']}
- **Archivos afectados:** {report['total_files']}
- **Categoría más común:** {report['summary']['most_common_category']}
- **Complejidad promedio:** {report['summary']['avg_complexity']:.2f}

## Distribución por Categoría
"""
        
        for cat, stats in sorted(report['category_distribution'].items(), key=lambda x: x[1]['count'], reverse=True):
            md += f"\n### {cat.upper()}\n"
            md += f"- **Count:** {stats['count']}\n"
            md += f"- **Percentage:** {stats['percentage']:.1f}%\n"
        
        md += "\n## Top 10 Archivos con más sorries\n"
        
        file_counts = [(path, len(sorries)) for path, sorries in report['detailed'].items()]
        file_counts.sort(key=lambda x: x[1], reverse=True)
        
        for path, count in file_counts[:10]:
            md += f"- `{path}`: {count} sorries\n"
        
        return md

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Uso: amda_deep_v2.py <output_json> [output_md]")
        sys.exit(1)
    
    output_json = sys.argv[1]
    output_md = sys.argv[2] if len(sys.argv) > 2 else None
    
    amda = AmDADeepV2()
    report = amda.analyze_repository()
    
    # Guardar JSON
    with open(output_json, 'w') as f:
        json.dump(report, f, indent=2)
    
    print(f"\n✅ Análisis completado:")
    print(f"   📊 Total sorries: {report['total_sorries']}")
    print(f"   📁 Archivos: {report['total_files']}")
    print(f"   📝 Reporte guardado en: {output_json}")
    
    # Guardar Markdown si se especificó
    if output_md:
        md_content = amda.generate_report_markdown(report)
        with open(output_md, 'w') as f:
            f.write(md_content)
        print(f"   📄 Reporte Markdown: {output_md}")
