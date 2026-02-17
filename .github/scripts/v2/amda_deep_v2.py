#!/usr/bin/env python3
"""
AMDA DEEP V2.0 - Análisis semántico multi-categórico de sorries
"""

import json
import re
import sys
from pathlib import Path
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
    
    def classify_deep(self, code, context, debug=False):
        """Clasificación multi-categórica con puntajes y logging detallado"""
        scores = {}
        
        # Texto combinado para análisis
        text = (code + " " + context).lower()
        
        if debug:
            print(f"🔍 Analizando contexto: {text[:100]}...")
        
        for category, info in self.PATTERNS.items():
            score = 0
            matches = []
            for keyword in info["keywords"]:
                if keyword.lower() in text:
                    score += info["weight"]
                    matches.append(keyword)
            
            if score > 0:
                scores[category] = score
                if debug:
                    print(f"  ✅ {category}: {len(matches)} matches ({', '.join(matches[:3])})")
            elif debug:
                print(f"  ❌ {category}: 0 matches")
        
        # Verificar si es trivial (debería detectarse)
        if debug and "trivial" in scores and scores["trivial"] > 0:
            print(f"  ⚠️ ¡TRIVIAL DETECTADO! Debería procesarse con rfl/simp")
        
        # Si no hay categorías, marcar como desconocido
        if not scores:
            scores["unknown"] = 1.0
            if debug:
                print(f"  ⚠️ Clasificado como UNKNOWN - no se encontraron patrones")
        
        # Categoría principal (mayor puntaje)
        primary = max(scores.items(), key=lambda x: x[1])[0] if scores else "unknown"
        
        # Validación: si hay evidencia de trivial pero se clasificó como unknown, corregir
        if primary == "unknown" and any(kw in text for kw in ["rfl", "trivial", "simp", "norm_num"]):
            if debug:
                print(f"  🔧 CORRECCIÓN: Detectado patrón trivial en 'unknown', reclasificando...")
            primary = "trivial"
            scores["trivial"] = 0.8
        
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
    
    def analyze_file(self, filepath, debug=False):
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
                
                # Clasificar (con debug si está activado)
                classification = self.classify_deep(line, context, debug=debug)
                
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
