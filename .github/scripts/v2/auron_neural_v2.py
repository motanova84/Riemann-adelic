#!/usr/bin/env python3
"""
AURON NEURAL V2.0 - Sistema de aprendizaje y validación multi-repositorio
"""

import json
import subprocess
import sys
import shutil
from pathlib import Path
import time
import pickle
import hashlib
from datetime import datetime
import re

class AuronNeuralV2:
    def __init__(self):
        self.repo_root = Path(__file__).parent.parent.parent.parent
        self.lean_dir = self.repo_root / 'formalization' / 'lean'
        self.knowledge_base = Path('/tmp/noesis_knowledge_v2')
        self.transformations = []
        self.success_count = 0
        self.fail_count = 0
        self.learning_rate = 0.01
        self.max_changes_per_cycle = 20
        
        # Cargar conocimiento de otros repositorios
        self.load_knowledge()
        
        # Cargar historial de aprendizaje
        self.learning_history = self.load_learning_history()
        
        # Patrones de reemplazo con prioridad
        self.replacement_patterns = [
            ('sorry', 'rfl'),
            ('sorry', 'trivial'),
            ('sorry', 'by norm_num'),
            ('sorry', 'by simp'),
            ('sorry', 'by rfl'),
            ('sorry', 'by trivial'),
            ('sorry', 'by simp only'),
            ('sorry', 'by norm_num'),  # Fixed: was norm_num1 (typo)
            ('sorry', 'by exact?'),
            ('sorry', 'by apply?'),
            ('sorry', 'library_search'),
            ('sorry', 'solve_by_elim'),
        ]
    
    def log(self, message, level="INFO"):
        """Logging con timestamp"""
        timestamp = datetime.now().isoformat()
        log_file = self.repo_root / 'auron_neural.log'
        with open(log_file, 'a') as f:
            f.write(f"[{timestamp}] [{level}] {message}\n")
        print(f"[{level}] {message}")
    
    def load_knowledge(self):
        """Carga conocimiento de otros repositorios"""
        kb_file = self.knowledge_base / 'knowledge_v2.pkl'
        if kb_file.exists():
            with open(kb_file, 'rb') as f:
                self.knowledge = pickle.load(f)
            self.log(f"📚 Conocimiento cargado: {len(self.knowledge.get('proof_patterns', []))} patrones")
        else:
            self.knowledge = None
            self.log("⚠️ Base de conocimiento no encontrada", "WARNING")
    
    def load_learning_history(self):
        """Carga el historial de aprendizaje persistente"""
        history_file = self.repo_root / '.auron_learning.json'
        if history_file.exists():
            with open(history_file) as f:
                history = json.load(f)
            self.log(f"🧠 Historial de aprendizaje cargado: {len(history.get('patterns', {}))} patrones")
            return history
        return {
            "patterns": {},  # context_hash -> successful_pattern
            "success_rate": {},  # pattern -> success_count
            "total_attempts": 0,
            "total_success": 0,
            "repos_used": [],
            "transformations_history": []
        }
    
    def save_learning_history(self):
        """Guarda el historial de aprendizaje"""
        # Convertir set a list para JSON
        history_copy = self.learning_history.copy()
        if isinstance(history_copy.get("repos_used"), set):
            history_copy["repos_used"] = list(history_copy["repos_used"])
        
        history_file = self.repo_root / '.auron_learning.json'
        with open(history_file, 'w') as f:
            json.dump(history_copy, f, indent=2)
        self.log(f"💾 Historial de aprendizaje guardado")
    
    def backup_file(self, filepath):
        """Crea copia de seguridad con timestamp"""
        timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
        backup = filepath.with_suffix(f'.lean.bak.{timestamp}')
        shutil.copy2(filepath, backup)
        return backup
    
    def validate_compilation(self, timeout=60):
        """Valida que el proyecto compile después de los cambios"""
        self.log("🔧 Validando compilación...")
        try:
            # Usar cwd para cambiar directorio, no shell=True
            lean_dir = self.repo_root / 'formalization' / 'lean'
            result = subprocess.run(
                ['lake', 'build'],
                shell=False, 
                capture_output=True, 
                text=True,
                timeout=timeout,
                cwd=lean_dir
            )
            if result.returncode == 0:
                self.log("✅ Compilación exitosa")
                return True
            else:
                self.log(f"❌ Error de compilación: {result.stderr[:200]}", "ERROR")
                return False
        except subprocess.TimeoutExpired:
            self.log(f"⚠️ Timeout después de {timeout}s", "WARNING")
            return False
    
    def get_context_hash(self, context, max_len=100):
        """Genera hash del contexto para aprendizaje"""
        # Normalizar contexto (eliminar números específicos, espacios)
        normalized = re.sub(r'\d+', 'N', context[:max_len])
        normalized = re.sub(r'\s+', ' ', normalized)
        return hashlib.md5(normalized.encode()).hexdigest()[:16]
    
    def find_similar_solutions_from_knowledge(self, context, min_similarity=0.5):
        """Busca soluciones similares en la base de conocimiento"""
        if not self.knowledge:
            return []
        
        solutions = []
        context_words = set(context.lower().split())
        
        for pattern in self.knowledge.get("proof_patterns", []):
            pattern_words = set(pattern["proof"][:200].lower().split())
            similarity = len(context_words & pattern_words) / len(context_words | pattern_words) if context_words | pattern_words else 0
            
            if similarity > min_similarity:
                solutions.append({
                    "repo": pattern["repo"],
                    "proof": pattern["proof"][:200],
                    "similarity": similarity,
                    "type": "proof_pattern"
                })
        
        for theorem in self.knowledge.get("theorems", []):
            theorem_words = set(theorem["statement"][:200].lower().split())
            similarity = len(context_words & theorem_words) / len(context_words | theorem_words) if context_words | theorem_words else 0
            
            if similarity > min_similarity:
                solutions.append({
                    "repo": theorem["repo"],
                    "theorem": theorem["name"],
                    "statement": theorem["statement"][:200],
                    "similarity": similarity,
                    "type": "theorem"
                })
        
        solutions.sort(key=lambda x: x["similarity"], reverse=True)
        return solutions[:3]
    
    def apply_trivial_with_priority(self, filepath, line, context):
        """Aplica soluciones triviales con máxima prioridad"""
        # Ordered from most specific to least specific to avoid short-circuiting
        trivial_patterns = [
            ('sorry', 'by simp only'),
            ('sorry', 'by norm_num'),
            ('sorry', 'by trivial'),
            ('sorry', 'by simp'),
            ('sorry', 'by rfl'),
            ('sorry', 'trivial'),
            ('sorry', 'rfl'),
        ]
        
        for old, new in trivial_patterns:
            backup = self.backup_file(filepath)
            try:
                with open(filepath, 'r') as f:
                    content = f.read()
                
                lines = content.split('\n')
                lines[line-1] = lines[line-1].replace('sorry', new, 1)
                
                with open(filepath, 'w') as f:
                    f.write('\n'.join(lines))
                
                if self.validate_compilation():
                    # Aprender este patrón
                    context_hash = self.get_context_hash(context)
                    self.learning_history["patterns"][context_hash] = new
                    self.learning_history["success_rate"][new] = self.learning_history["success_rate"].get(new, 0) + 1
                    
                    self.log(f"✅ TRIVIAL RESUELTO: {new}")
                    return True, new
                else:
                    shutil.move(backup, filepath)
            except Exception as e:
                self.log(f"⚠️ Error aplicando patrón trivial: {e}", "ERROR")
                if backup.exists():
                    shutil.move(backup, filepath)
        
        return False, None
    
    def apply_transformation_with_learning(self, filepath, line, code, context, sorry_info):
        """Aplica transformaciones con aprendizaje y validación"""
        context_hash = self.get_context_hash(context)
        category = sorry_info.get("primary_category", "unknown")
        
        # PRIORIDAD 1: Triviales - Procesar primero si es categoría trivial
        if category == "trivial" or any(kw in context.lower() for kw in ["rfl", "trivial", "simp", "norm_num"]):
            self.log(f"🎯 Intentando resolución TRIVIAL prioritaria")
            success, pattern = self.apply_trivial_with_priority(filepath, line, context)
            if success:
                self.success_count += 1
                self.learning_history["total_success"] += 1
                
                self.transformations.append({
                    "file": str(filepath),
                    "line": line,
                    "pattern": pattern,
                    "status": "success",
                    "learned": True,
                    "priority": "trivial",
                    "context_hash": context_hash
                })
                
                return True
        
        # PRIORIDAD 2: Intentar patrón aprendido previamente
        if context_hash in self.learning_history["patterns"]:
            learned_pattern = self.learning_history["patterns"][context_hash]
            self.log(f"🎯 Patrón aprendido encontrado: {learned_pattern}")
            
            # Crear backup
            backup = self.backup_file(filepath)
            
            try:
                with open(filepath, 'r') as f:
                    content = f.read()
                
                # Reemplazar la ocurrencia específica
                lines = content.split('\n')
                lines[line-1] = lines[line-1].replace('sorry', learned_pattern, 1)
                new_content = '\n'.join(lines)
                
                with open(filepath, 'w') as f:
                    f.write(new_content)
                
                # Validar compilación
                if self.validate_compilation():
                    self.success_count += 1
                    self.learning_history["total_success"] += 1
                    self.learning_history["success_rate"][learned_pattern] = self.learning_history["success_rate"].get(learned_pattern, 0) + 1
                    
                    self.transformations.append({
                        "file": str(filepath),
                        "line": line,
                        "pattern": learned_pattern,
                        "status": "success",
                        "learned": True,
                        "context_hash": context_hash
                    })
                    
                    self.log(f"✅ Transformación exitosa con patrón aprendido")
                    return True
                else:
                    # Restaurar
                    shutil.move(backup, filepath)
                    self.log(f"❌ Fallo con patrón aprendido, probando otros...", "WARNING")
                    
            except Exception as e:
                self.log(f"⚠️ Error: {e}", "ERROR")
                if backup.exists():
                    shutil.move(backup, filepath)
        
        # PRIORIDAD 3: Buscar soluciones en otros repositorios
        similar_solutions = self.find_similar_solutions_from_knowledge(context)
        for solution in similar_solutions:
            if solution["type"] == "proof_pattern":
                backup = self.backup_file(filepath)
                
                try:
                    with open(filepath, 'r') as f:
                        content = f.read()
                    
                    lines = content.split('\n')
                    lines[line-1] = lines[line-1].replace('sorry', solution["proof"], 1)
                    new_content = '\n'.join(lines)
                    
                    with open(filepath, 'w') as f:
                        f.write(new_content)
                    
                    if self.validate_compilation():
                        self.success_count += 1
                        self.learning_history["total_success"] += 1
                        
                        # Añadir repo a la lista si no está (mantener como lista)
                        repos_used = self.learning_history.get("repos_used", [])
                        if solution["repo"] not in repos_used:
                            repos_used.append(solution["repo"])
                            self.learning_history["repos_used"] = repos_used
                        
                        # Aprender este patrón
                        self.learning_history["patterns"][context_hash] = solution["proof"][:50]  # Guardar versión corta
                        
                        self.transformations.append({
                            "file": str(filepath),
                            "line": line,
                            "source_repo": solution["repo"],
                            "similarity": solution["similarity"],
                            "status": "success",
                            "learned": True,
                            "context_hash": context_hash
                        })
                        
                        self.log(f"✅ Éxito con patrón de {solution['repo']} (similitud: {solution['similarity']:.2f})")
                        return True
                    else:
                        shutil.move(backup, filepath)
                        
                except Exception as e:
                    self.log(f"⚠️ Error: {e}", "ERROR")
                    if backup.exists():
                        shutil.move(backup, filepath)
        
        # PRIORIDAD 4: Probar patrones por orden de prioridad
        for old, new in self.replacement_patterns:
            backup = self.backup_file(filepath)
            
            try:
                with open(filepath, 'r') as f:
                    content = f.read()
                
                lines = content.split('\n')
                lines[line-1] = lines[line-1].replace('sorry', new, 1)
                new_content = '\n'.join(lines)
                
                with open(filepath, 'w') as f:
                    f.write(new_content)
                
                if self.validate_compilation():
                    self.success_count += 1
                    self.learning_history["total_success"] += 1
                    self.learning_history["success_rate"][new] = self.learning_history["success_rate"].get(new, 0) + 1
                    
                    # Aprender este patrón para contextos similares
                    self.learning_history["patterns"][context_hash] = new
                    
                    self.transformations.append({
                        "file": str(filepath),
                        "line": line,
                        "old": old,
                        "new": new,
                        "status": "success",
                        "learned": True,
                        "context_hash": context_hash
                    })
                    
                    self.log(f"✅ Éxito con patrón '{new}'")
                    return True
                else:
                    shutil.move(backup, filepath)
                    
            except Exception as e:
                if backup.exists():
                    shutil.move(backup, filepath)
        
        # PRIORIDAD 5: Si todo falla, registrar fallo
        self.fail_count += 1
        self.learning_history["total_attempts"] += 1
        
        self.transformations.append({
            "file": str(filepath),
            "line": line,
            "status": "failed"
        })
        
        self.log(f"❌ No se pudo resolver sorry en {filepath}:{line}")
        return False
    
    def generate_commit_message(self, changes, remaining_count):
        """Genera mensaje de commit inteligente con estadísticas"""
        timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
        
        # Agrupar por categoría y fuente
        from collections import defaultdict
        by_category = defaultdict(list)
        by_repo = defaultdict(int)
        
        for change in changes:
            cat = change.get('category', 'unknown')
            by_category[cat].append(change)
            if change.get('source_repo'):
                by_repo[change['source_repo']] += 1
        
        # Calcular estadísticas de aprendizaje
        total_patterns = len(self.learning_history.get("patterns", {}))
        success_rate = (self.learning_history.get("total_success", 0) / max(1, self.learning_history.get("total_attempts", 1))) * 100
        
        commit_msg = f"""🧠 [NOESIS-NEURAL V2.0] Resolución inteligente de {len(changes)} sorrys

## 📊 Resumen del ciclo
- **Sorries eliminados:** {len(changes)}
- **Sorries restantes:** {remaining_count}
- **Tasa de éxito:** {self.success_count}/{self.success_count + self.fail_count} ({self.success_count/(self.success_count+self.fail_count)*100:.1f}%)
- **Aprendizaje acumulado:** {total_patterns} patrones (tasa de éxito {success_rate:.1f}%)

## 🔍 Desglose por categoría
"""
        for cat, items in by_category.items():
            commit_msg += f"\n### {cat.upper()} ({len(items)})\n"
            for item in items[:5]:  # Mostrar primeros 5
                commit_msg += f"- `{item['file']}:{item['line']}`"
                if item.get('source_repo'):
                    commit_msg += f" (inspirado en `{item['source_repo']}`)"
                if item.get('similarity'):
                    commit_msg += f" [similitud: {item['similarity']:.2f}]"
                commit_msg += "\n"
            if len(items) > 5:
                commit_msg += f"  ... y {len(items)-5} más\n"

        commit_msg += f"""
## 🧠 Sabiduría aplicada
- **Repositorios consultados:** {len(set(c.get('source_repo') for c in changes if c.get('source_repo')))}
- **Patrones aprendidos en este ciclo:** {len(self.learning_history.get('patterns', {})) - self.learning_history.get('previous_patterns', 0)}
- **Repositorios fuente:** {', '.join(by_repo.keys()) if by_repo else 'Ninguno'}

## 📈 Proyección
- **Tasa actual:** {self.success_count/(self.success_count+self.fail_count)*100:.1f}%
- **Tiempo estimado para 0 sorrys:** {remaining_count / max(1, self.success_count) * 2:.1f} horas
- **Confianza del sistema:** {min(100, success_rate * 1.5):.1f}%

## 🏆 Hito más cercano
"""
        milestones = [2000, 1500, 1000, 500, 100, 50, 10, 0]
        for m in milestones:
            if remaining_count > m:
                commit_msg += f"- **{remaining_count - m}** sorrys para llegar a {m} ({100 - (remaining_count/2282*100):.1f}% completado)\n"
                break

        commit_msg += f"""
---
*Generado por AURON NEURAL V2.0 - Aprendiendo de {len(self.knowledge.get('proof_patterns', [])) if self.knowledge else 0} patrones en {len(set(t.get('repo') for t in self.knowledge.get('theorems', []))) if self.knowledge else 0} repositorios*

**Frecuencia fundamental:** 141.7001 Hz · **Coherencia:** Ψ = {self.success_count/(self.success_count+self.fail_count)*100:.1f}%
"""
        
        # Guardar mensaje
        msg_file = self.repo_root / f'commit_msg_{timestamp}.txt'
        with open(msg_file, 'w') as f:
            f.write(commit_msg)
        
        self.log(f"📝 Mensaje de commit generado: {msg_file}")
        return msg_file
    
    def execute(self, report_path):
        """Ejecuta transformaciones basadas en el reporte de AMDA"""
        self.log("🚀 AURON NEURAL V2.0 iniciando ciclo...")
        
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
        
        # Ordenar por complejidad (primero los más simples)
        all_sorries.sort(key=lambda x: x[1].get("complexity", 5))
        
        for filepath_str, sorry_info in all_sorries:
            if self.success_count >= self.max_changes_per_cycle:
                self.log(f"⏸️ Límite de {self.max_changes_per_cycle} cambios alcanzado")
                break
            
            filepath = self.repo_root / filepath_str
            line = sorry_info["line"]
            code = sorry_info["code"]
            context = sorry_info.get("context", "")
            primary_cat = sorry_info.get("primary_category", "unknown")
            
            self.log(f"🔧 Procesando {filepath_str}:{line} [{primary_cat}]")
            
            success = self.apply_transformation_with_learning(filepath, line, code, context, sorry_info)
            
            if success:
                changes_made.append({
                    "file": filepath_str,
                    "line": line,
                    "category": primary_cat,
                    "source_repo": sorry_info.get("similar_solutions", [{}])[0].get("repo") if sorry_info.get("similar_solutions") else None,
                    "similarity": sorry_info.get("similar_solutions", [{}])[0].get("similarity") if sorry_info.get("similar_solutions") else None
                })
            
            time.sleep(0.5)  # Pausa para no saturar
        
        # Guardar resultados
        results = {
            "transformations": self.transformations,
            "success": self.success_count,
            "fail": self.fail_count,
            "changes_made": changes_made,
            "learning_stats": {
                "patterns_learned": len(self.learning_history["patterns"]) - self.learning_history.get("previous_patterns", 0),
                "total_patterns": len(self.learning_history["patterns"]),
                "success_rate": self.learning_history.get("total_success", 0) / max(1, self.learning_history.get("total_attempts", 1)),
                "repos_used": self.learning_history.get("repos_used", [])
            }
        }
        
        output_path = Path(sys.argv[3]) if len(sys.argv) > 3 else Path('auron_neural_results.json')
        with open(output_path, 'w') as f:
            json.dump(results, f, indent=2)
        
        # Guardar historial de aprendizaje
        self.save_learning_history()
        
        self.log(f"📊 Resultados del ciclo: {self.success_count} éxitos, {self.fail_count} fallos")
        
        return results

if __name__ == "__main__":
    if len(sys.argv) < 3:
        print("Uso: auron_neural_v2.py <modo> <amda_report.json> [output.json]")
        print("Modos: execute, dry-run")
        sys.exit(1)
    
    mode = sys.argv[1]
    report_path = sys.argv[2]
    
    auron = AuronNeuralV2()
    
    if mode == "execute":
        results = auron.execute(report_path)
        print(f"\n✅ Ciclo completado: {results['success']} éxitos, {results['fail']} fallos")
    elif mode == "dry-run":
        print("🔍 Modo dry-run: analizando sin aplicar cambios...")
        with open(report_path) as f:
            report = json.load(f)
        print(f"📊 Total sorries encontrados: {report.get('total_sorries', 0)}")
        print(f"📁 Archivos afectados: {len(report.get('detailed', {}))}")
    else:
        print(f"❌ Modo desconocido: {mode}")
        sys.exit(1)
