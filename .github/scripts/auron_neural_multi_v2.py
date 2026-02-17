#!/usr/bin/env python3
"""
AURON NEURAL MULTI V2.0 - Sistema de aprendizaje multi-repositorio con validación
Fusión de PR #1716 (extracción multi-repo) y PR #1717 (aprendizaje y validación)
"""

import json
import subprocess
import sys
import shutil
import os
from pathlib import Path
import time
import pickle
import hashlib
from datetime import datetime
import re
from collections import defaultdict

class AuronNeuralMultiV2:
    def __init__(self):
        self.repo_root = Path(__file__).parent.parent.parent
        self.lean_dir = self.repo_root / 'formalization' / 'lean'
        self.knowledge_base = Path('/tmp/noesis_knowledge_v2')
        self.transformations = []
        self.success_count = 0
        self.fail_count = 0
        # Leer max_changes de variable de entorno o usar default
        self.max_changes_per_cycle = int(os.getenv('AURON_MAX_CHANGES', '20'))
        # Read dry_run from environment variable
        self.dry_run = os.getenv('AURON_DRY_RUN', 'false').lower() in ('true', '1', 'yes')
        
        # Cargar conocimiento de otros repositorios (PR #1716)
        self.load_knowledge()
        
        # Cargar historial de aprendizaje (PR #1717)
        self.learning_history = self.load_learning_history()
        
        # Patrones de reemplazo por categoría (sin prefijo 'by')
        self.category_strategies = {
            "trivial": ['rfl', 'trivial', 'norm_num', 'simp'],
            "structural": ['funext', 'ext', 'congr', 'rw'],
            "library_search": ['library_search', 'exact?', 'apply?', 'solve_by_elim'],
            "qcal": ['QCAL.Noesis.spectral_reflexivity', 'QCAL.Noetic.coherence_tensor'],
            "spectral": [],  # Requiere estrategias especializadas
            "correspondence": [],  # Requiere estrategias especializadas
            "adelic": [],  # Requiere estrategias especializadas
            "analytic": []  # Requiere estrategias especializadas
        }
    
    def log(self, message, level="INFO"):
        timestamp = datetime.now().isoformat()
        log_file = self.repo_root / 'auron_neural_multi.log'
        with open(log_file, 'a') as f:
            f.write(f"[{timestamp}] [{level}] {message}\n")
        print(f"[{level}] {message}")
    
    def load_knowledge(self):
        """Carga conocimiento de otros repositorios (PR #1716)"""
        kb_file = self.knowledge_base / 'knowledge_v2.pkl'
        if kb_file.exists():
            with open(kb_file, 'rb') as f:
                self.knowledge = pickle.load(f)
            self.log(f"📚 Conocimiento cargado:")
            self.log(f"   - Definiciones: {len(self.knowledge.get('definitions', []))}")
            self.log(f"   - Teoremas: {len(self.knowledge.get('theorems', []))}")
            self.log(f"   - Patrones: {len(self.knowledge.get('proof_patterns', []))}")
        else:
            self.knowledge = None
            self.log("⚠️ Base de conocimiento no encontrada", "WARNING")
    
    def load_learning_history(self):
        """Carga el historial de aprendizaje (PR #1717)"""
        history_file = self.repo_root / '.auron_learning.json'
        if history_file.exists():
            with open(history_file) as f:
                return json.load(f)
        return {
            "patterns": {},
            "success_rate": {},
            "total_attempts": 0,
            "total_success": 0,
            "repos_used": [],
            "transformations_history": []
        }
    
    def save_learning_history(self):
        """Guarda el historial de aprendizaje"""
        history_file = self.repo_root / '.auron_learning.json'
        with open(history_file, 'w') as f:
            json.dump(self.learning_history, f, indent=2)
        self.log(f"💾 Historial de aprendizaje guardado")
    
    def backup_file(self, filepath):
        """Crea copia de seguridad"""
        timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
        backup = filepath.with_suffix(f'.lean.bak.{timestamp}')
        shutil.copy2(filepath, backup)
        return backup
    
    def validate_compilation(self, timeout=60):
        """Valida compilación con lake build"""
        self.log("🔧 Validando compilación...")
        try:
            lean_dir = self.repo_root / 'formalization' / 'lean'
            result = subprocess.run(
                ['lake', 'build'],
                capture_output=True, text=True, timeout=timeout,
                cwd=lean_dir
            )
            if result.returncode == 0:
                self.log("✅ Compilación exitosa")
                return True
            else:
                self.log(f"❌ Error: {result.stderr[:200]}", "ERROR")
                return False
        except subprocess.TimeoutExpired:
            self.log(f"⚠️ Timeout", "WARNING")
            return False
    
    def get_context_hash(self, context, max_len=100):
        """Genera hash del contexto para aprendizaje"""
        normalized = re.sub(r'\d+', 'N', context[:max_len])
        normalized = re.sub(r'\s+', ' ', normalized)
        return hashlib.md5(normalized.encode()).hexdigest()[:16]
    
    def calculate_jaccard_similarity(self, set1, set2):
        """Calcula similitud Jaccard entre dos conjuntos"""
        if not set1 or not set2:
            return 0.0
        intersection = len(set1 & set2)
        union = len(set1 | set2)
        return intersection / union if union > 0 else 0.0
    
    def find_cross_repo_matches(self, context, category):
        """Busca coincidencias en otros repositorios (PR #1716)"""
        if not self.knowledge:
            return []
        
        matches = []
        context_words = set(context.lower().split())
        
        # Buscar en patrones de prueba
        for pattern in self.knowledge.get("proof_patterns", []):
            pattern_words = set(pattern["proof"][:200].lower().split())
            similarity = self.calculate_jaccard_similarity(context_words, pattern_words)
            
            if similarity > 0.3:  # Umbral ajustable
                matches.append({
                    "repo": pattern["repo"],
                    "content": pattern["proof"][:200],
                    "similarity": similarity,
                    "type": "proof_pattern"
                })
        
        # Buscar en teoremas
        for theorem in self.knowledge.get("theorems", []):
            theorem_words = set(theorem["statement"][:200].lower().split())
            similarity = self.calculate_jaccard_similarity(context_words, theorem_words)
            
            if similarity > 0.3:
                matches.append({
                    "repo": theorem["repo"],
                    "name": theorem["name"],
                    "content": theorem["statement"][:200],
                    "similarity": similarity,
                    "type": "theorem"
                })
        
        matches.sort(key=lambda x: x["similarity"], reverse=True)
        return matches[:3]
    
    def apply_transformation(self, filepath, line, code, context, sorry_info):
        """Aplica transformación con aprendizaje y validación"""
        if self.dry_run:
            self.log(f"🔍 [DRY RUN] Simulación en {filepath}:{line}")
            return True
        
        category = sorry_info.get("primary_category", "unknown")
        context_hash = self.get_context_hash(context)
        
        # 1. Verificar patrón aprendido
        if context_hash in self.learning_history["patterns"]:
            learned = self.learning_history["patterns"][context_hash]
            self.log(f"🎯 Patrón aprendido: {learned}")
            
            # Incrementar intentos
            self.learning_history["total_attempts"] += 1
            
            backup = self.backup_file(filepath)
            try:
                with open(filepath, 'r') as f:
                    content = f.read()
                
                lines = content.split('\n')
                lines[line-1] = lines[line-1].replace('sorry', learned, 1)
                
                with open(filepath, 'w') as f:
                    f.write('\n'.join(lines))
                
                if self.validate_compilation():
                    self.success_count += 1
                    self.learning_history["total_success"] += 1
                    self.learning_history["success_rate"][learned] = self.learning_history["success_rate"].get(learned, 0) + 1
                    
                    self.transformations.append({
                        "file": str(filepath),
                        "line": line,
                        "pattern": learned,
                        "status": "success",
                        "learned": True
                    })
                    return True
                else:
                    shutil.move(backup, filepath)
            except Exception as e:
                if backup.exists():
                    shutil.move(backup, filepath)
        
        # 2. Buscar coincidencias en otros repositorios
        matches = self.find_cross_repo_matches(context, category)
        for match in matches[:2]:  # Probar top 2
            # Incrementar intentos
            self.learning_history["total_attempts"] += 1
            
            backup = self.backup_file(filepath)
            try:
                with open(filepath, 'r') as f:
                    content = f.read()
                
                lines = content.split('\n')
                # Intentar aplicar el patrón encontrado
                if match["type"] == "proof_pattern":
                    replacement = match["content"]
                else:
                    replacement = f"exact {match['name']}"
                
                lines[line-1] = lines[line-1].replace('sorry', replacement, 1)
                
                with open(filepath, 'w') as f:
                    f.write('\n'.join(lines))
                
                if self.validate_compilation():
                    self.success_count += 1
                    self.learning_history["total_success"] += 1
                    self.learning_history["repos_used"].append(match["repo"])
                    
                    # Aprender este patrón (solo el reemplazo, no la línea completa)
                    self.learning_history["patterns"][context_hash] = replacement
                    
                    self.transformations.append({
                        "file": str(filepath),
                        "line": line,
                        "source_repo": match["repo"],
                        "similarity": match["similarity"],
                        "status": "success"
                    })
                    return True
                else:
                    shutil.move(backup, filepath)
            except Exception as e:
                if backup.exists():
                    shutil.move(backup, filepath)
        
        # 3. Probar estrategias de categoría
        strategies = self.category_strategies.get(category, [])
        for strategy in strategies:
            # Incrementar intentos
            self.learning_history["total_attempts"] += 1
            
            backup = self.backup_file(filepath)
            try:
                with open(filepath, 'r') as f:
                    content = f.read()
                
                lines = content.split('\n')
                # Determinar si necesita prefijo 'by' basado en el tipo de estrategia
                if strategy in ['exact?', 'apply?', 'library_search', 'solve_by_elim']:
                    # Estas tácticas no necesitan 'by'
                    replacement = strategy
                else:
                    # Otras estrategias usan 'by'
                    replacement = f"by {strategy}"
                
                lines[line-1] = lines[line-1].replace('sorry', replacement, 1)
                
                with open(filepath, 'w') as f:
                    f.write('\n'.join(lines))
                
                if self.validate_compilation():
                    self.success_count += 1
                    self.learning_history["total_success"] += 1
                    self.learning_history["success_rate"][strategy] = self.learning_history["success_rate"].get(strategy, 0) + 1
                    self.learning_history["patterns"][context_hash] = replacement
                    
                    self.transformations.append({
                        "file": str(filepath),
                        "line": line,
                        "strategy": strategy,
                        "status": "success"
                    })
                    return True
                else:
                    shutil.move(backup, filepath)
            except Exception as e:
                if backup.exists():
                    shutil.move(backup, filepath)
        
        # 4. Fallo
        self.fail_count += 1
        self.learning_history["total_attempts"] += 1
        self.transformations.append({
            "file": str(filepath),
            "line": line,
            "status": "failed"
        })
        return False
    
    def generate_commit_message(self, changes, report):
        """Genera mensaje de commit con estadísticas combinadas"""
        timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
        
        # Estadísticas de PR #1716
        total_sorries = report.get("summary", {}).get("total_sorries", 0)
        by_category = report.get("summary", {}).get("by_category", {})
        
        # Estadísticas de aprendizaje
        patterns_learned = len(self.learning_history.get("patterns", {}))
        success_rate = (self.learning_history.get("total_success", 0) / max(1, self.learning_history.get("total_attempts", 1))) * 100
        
        # Repositorios utilizados
        repos_used = set()
        cross_repo_success = 0
        for c in changes:
            if c.get('source_repo'):
                repos_used.add(c['source_repo'])
                cross_repo_success += 1
        
        commit_msg = f"""# 🧠 NOESIS CEREBRAL V2.0 - Eliminación Autónoma de Sorrys

**Ciclo:** {timestamp}
**Modo:** {'🔍 DRY RUN' if self.dry_run else '⚡ PRODUCCIÓN'}
**Sorries eliminados:** {len(changes)}
**Sorries restantes:** {total_sorries - len(changes)}

## 📊 Estadísticas del Ciclo

| Métrica | Valor |
|---------|-------|
| Éxitos | {self.success_count} |
| Fallos | {self.fail_count} |
| Tasa de éxito | {self.success_count/(self.success_count+self.fail_count)*100:.1f}% if (self.success_count+self.fail_count) > 0 else 'N/A' |
| Coincidencias cross-repo | {cross_repo_success} |
| Repositorios utilizados | {len(repos_used)} |
| Patrones aprendidos | {patterns_learned} |
| Tasa de aprendizaje | {success_rate:.1f}% |

## 📈 Progreso General

| Categoría | Original | Restante | Eliminados |
|-----------|----------|----------|------------|
"""
        for cat, count in by_category.items():
            eliminated = sum(1 for c in changes if c.get('category') == cat)
            commit_msg += f"| {cat} | {count} | {count - eliminated} | {eliminated} |\n"
        
        commit_msg += f"""
## 🔍 Detalle de Transformaciones

"""
        for change in changes[:10]:  # Top 10
            commit_msg += f"- `{change['file']}:{change['line']}`"
            if change.get('source_repo'):
                commit_msg += f" (inspirado en `{change['source_repo']}`)"
            if change.get('similarity'):
                commit_msg += f" [similitud: {change['similarity']:.2f}]"
            commit_msg += "\n"
        
        if len(changes) > 10:
            commit_msg += f"  ... y {len(changes)-10} más\n"
        
        commit_msg += f"""
## 🧠 Sabiduría Colectiva

- **Repositorios fuente:** {', '.join(repos_used) if repos_used else 'Ninguno'}
- **Patrones aprendidos hoy:** {patterns_learned - self.learning_history.get('previous_patterns', 0)}
- **Total de conocimiento disponible:** {len(self.knowledge.get('proof_patterns', [])) if self.knowledge else 0} patrones

## 📈 Proyección

- **Tiempo estimado para completar:** {(total_sorries - len(changes)) / max(1, self.success_count) * 6:.1f} horas
- **Confianza del sistema:** {min(100, success_rate * 1.2):.1f}%

---
*Generado por NOESIS CEREBRAL V2.0 - Fusión de PR #1716 (extracción multi-repo) y PR #1717 (aprendizaje neural)*

**Frecuencia fundamental:** 141.7001 Hz · **Coherencia:** Ψ = {success_rate:.1f}%
"""
        
        # Guardar mensaje
        msg_file = self.repo_root / f'commit_msg_{timestamp}.txt'
        with open(msg_file, 'w') as f:
            f.write(commit_msg)
        
        return msg_file
    
    def execute(self, report_path):
        """Ejecuta el pipeline completo"""
        self.log("🚀 AURON NEURAL MULTI V2.0 iniciando...")
        
        with open(report_path) as f:
            report = json.load(f)
        
        # Guardar estado previo de aprendizaje
        self.learning_history["previous_patterns"] = len(self.learning_history.get("patterns", {}))
        
        changes_made = []
        
        # Procesar sorries por prioridad
        all_sorries = []
        for filepath_str, sorries in report.get("detailed", {}).items():
            for sorry in sorries:
                all_sorries.append((filepath_str, sorry))
        
        # Ordenar por prioridad (trivial primero, luego library_search, luego estructural)
        priority_order = {"trivial": 1, "library_search": 2, "structural": 3, "qcal": 4, "spectral": 5, "correspondence": 6}
        all_sorries.sort(key=lambda x: priority_order.get(x[1].get("primary_category", "unknown"), 10))
        
        for filepath_str, sorry_info in all_sorries:
            if self.success_count >= self.max_changes_per_cycle:
                self.log(f"⏸️ Límite de {self.max_changes_per_cycle} alcanzado")
                break
            
            filepath = self.repo_root / filepath_str
            line = sorry_info["line"]
            code = sorry_info["code"]
            context = sorry_info.get("context", "")
            category = sorry_info.get("primary_category", "unknown")
            
            self.log(f"🔧 Procesando {filepath_str}:{line} [{category}]")
            
            success = self.apply_transformation(filepath, line, code, context, sorry_info)
            
            if success:
                changes_made.append({
                    "file": filepath_str,
                    "line": line,
                    "category": category,
                    "source_repo": sorry_info.get("similar_solutions", [{}])[0].get("repo") if sorry_info.get("similar_solutions") else None,
                    "similarity": sorry_info.get("similar_solutions", [{}])[0].get("similarity") if sorry_info.get("similar_solutions") else None
                })
            
            time.sleep(0.5)
        
        # Resultados
        results = {
            "transformations": self.transformations,
            "success": self.success_count,
            "fail": self.fail_count,
            "changes_made": changes_made,
            "learning_stats": {
                "patterns_learned": len(self.learning_history["patterns"]) - self.learning_history.get("previous_patterns", 0),
                "total_patterns": len(self.learning_history["patterns"]),
                "success_rate": self.learning_history.get("total_success", 0) / max(1, self.learning_history.get("total_attempts", 0)),
                "repos_used": list(set(self.learning_history.get("repos_used", [])))
            }
        }
        
        # Guardar resultados
        output_path = Path(sys.argv[2]) if len(sys.argv) >= 3 else Path('auron_multi_results.json')
        output_path = Path(sys.argv[3]) if len(sys.argv) > 3 else Path('auron_multi_results.json')
        with open(output_path, 'w') as f:
            json.dump(results, f, indent=2)
        
        # Guardar aprendizaje
        self.save_learning_history()
        
        self.log(f"📊 Resultados: {self.success_count} éxitos, {self.fail_count} fallos")
        
        return results, report

if __name__ == "__main__":
    if len(sys.argv) < 3:
        print("Uso: auron_neural_multi_v2.py <amda_report.json> <output_results.json>")
        sys.exit(1)
    
    report_path = Path(sys.argv[1])
    
    if not report_path.exists():
        print(f"❌ Error: Archivo {report_path} no existe")
        sys.exit(1)
    
    auron = AuronNeuralMultiV2()
    results, report = auron.execute(report_path)
    
    # Generar mensaje de commit
    if results["changes_made"]:
        msg_file = auron.generate_commit_message(results["changes_made"], report)
        print(f"\n📝 Mensaje de commit generado: {msg_file}")
    
    print(f"\n✅ AURON NEURAL MULTI V2.0 completado")
    print(f"   Éxitos: {results['success']}")
    print(f"   Fallos: {results['fail']}")
