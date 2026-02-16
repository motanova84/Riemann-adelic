#!/usr/bin/env python3
"""
AURON NEURAL V2.0 - Ejecutor con aprendizaje reforzado multi-repo
Aprende de transformaciones exitosas y valida con compilación
"""

import json
import sys
import subprocess
import pickle
import time
import hashlib
from pathlib import Path
from typing import Dict, List, Any, Optional
from datetime import datetime
from collections import defaultdict
import shutil

class AuronNeuralV2:
    def __init__(self, dry_run: bool = False, max_changes: int = 20):
        self.repo_root = Path(__file__).parent.parent.parent
        self.lean_dir = self.repo_root / 'formalization' / 'lean'
        self.knowledge_base = Path('/tmp/noesis_knowledge_v2')
        self.dry_run = dry_run
        self.max_changes = max_changes
        
        # Contadores de éxito/fallo
        self.success_count = 0
        self.fail_count = 0
        self.learning_rate = 0.01
        
        # Total de sorries del reporte AMDA (se establece en run())
        self.total_sorries_from_amda = 0
        
        self.changes = {
            "files_modified": [],
            "sorries_eliminated": 0,
            "transformations": [],
            "metadata": {
                "version": "2.0",
                "execution_date": datetime.now().isoformat()
            }
        }
        
        # Cargar conocimiento multi-repo
        self.load_knowledge()
        
        # Cargar historial de aprendizaje
        self.learning_history = self.load_learning_history()
        
        # Estrategias de resolución (ordenadas por prioridad)
        self.STRATEGIES = {
            "trivial": self._resolve_trivial,
            "qcal": self._resolve_qcal,
            "adelic": self._resolve_adelic,
            "spectral": self._resolve_spectral
        }
    
    def load_knowledge(self):
        """Carga conocimiento de otros repositorios"""
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
    
    def load_learning_history(self):
        """Carga el historial de aprendizaje"""
        history_file = self.repo_root / '.auron_learning.json'
        if history_file.exists():
            try:
                with open(history_file) as f:
                    history = json.load(f)
                    print(f"✓ Historial de aprendizaje cargado: {len(history.get('patterns', {}))} patrones")
                    return history
            except Exception as e:
                print(f"⚠ Error cargando historial: {e}")
        
        return {
            "patterns": {},
            "success_rate": {},
            "total_attempts": 0,
            "last_updated": datetime.now().isoformat()
        }
    
    def save_learning_history(self):
        """Guarda el historial de aprendizaje"""
        history_file = self.repo_root / '.auron_learning.json'
        self.learning_history["last_updated"] = datetime.now().isoformat()
        try:
            with open(history_file, 'w') as f:
                json.dump(self.learning_history, f, indent=2)
            print(f"✓ Historial de aprendizaje guardado")
        except Exception as e:
            print(f"⚠ Error guardando historial: {e}")
    
    def backup_file(self, filepath: Path) -> Path:
        """Crea copia de seguridad"""
        backup = filepath.with_suffix('.lean.bak')
        shutil.copy2(filepath, backup)
        return backup
    
    def test_compilation(self, timeout: int = 60) -> bool:
        """Prueba compilación con lake build"""
        if self.dry_run:
            return True
        
        try:
            result = subprocess.run(
                "cd formalization/lean && lake build",
                shell=True,
                capture_output=True,
                text=True,
                timeout=timeout,
                cwd=self.repo_root
            )
            return result.returncode == 0
        except subprocess.TimeoutExpired:
            print("⏱️ Timeout en compilación")
            return False
        except Exception as e:
            print(f"⚠ Error en compilación: {e}")
            return False
    
    def apply_trivial_with_learning(self, filepath: Path, line: int, code: str, 
                                    context: str, sorry_info: Dict) -> bool:
        """Aplica soluciones triviales con aprendizaje"""
        replacements = [
            'rfl',
            'trivial',
            'by norm_num',
            'by simp',
            'by rfl',
            'by trivial',
            'by simp only',
            'norm_num',
        ]
        
        # Aprender de intentos anteriores (usar contexto como clave)
        pattern_key = hashlib.md5(context[:100].encode()).hexdigest()[:16]
        was_learned = pattern_key in self.learning_history["patterns"]  # Capturar antes de actualizar
        
        if was_learned:
            # Usar la solución que funcionó antes primero
            learned_solution = self.learning_history["patterns"][pattern_key]
            replacements = [learned_solution] + [r for r in replacements if r != learned_solution]
        
        backup = self.backup_file(filepath)
        
        for replacement in replacements:
            try:
                with open(filepath, 'r', encoding='utf-8') as f:
                    lines = f.readlines()
                
                # Reemplazar la ocurrencia específica en la línea
                if line - 1 < len(lines) and 'sorry' in lines[line - 1]:
                    lines[line - 1] = lines[line - 1].replace('sorry', replacement, 1)
                    
                    with open(filepath, 'w', encoding='utf-8') as f:
                        f.writelines(lines)
                    
                    # Incrementar intentos por cada reemplazo probado
                    self.learning_history["total_attempts"] += 1
                    
                    # Probar compilación
                    if self.test_compilation():
                        self.success_count += 1
                        
                        # Actualizar aprendizaje
                        self.learning_history["patterns"][pattern_key] = replacement
                        self.learning_history["success_rate"][pattern_key] = \
                            self.learning_history["success_rate"].get(pattern_key, 0) + 1
                        
                        # Registrar transformación
                        self.changes["transformations"].append({
                            "file": str(filepath.relative_to(self.repo_root)),
                            "line": line,
                            "old": 'sorry',
                            "new": replacement,
                            "original_category": sorry_info.get("primary_category", "trivial"),
                            "status": "success",
                            "pattern_key": pattern_key,
                            "learned": was_learned  # Usar el valor capturado antes
                        })
                        
                        self.changes["sorries_eliminated"] += 1
                        if str(filepath.relative_to(self.repo_root)) not in self.changes["files_modified"]:
                            self.changes["files_modified"].append(str(filepath.relative_to(self.repo_root)))
                        
                        print(f"✅ Éxito con '{replacement}'" + (" [patrón aprendido]" if was_learned else ""))
                        return True
                    else:
                        # Restaurar
                        shutil.copy2(backup, filepath)
                
            except Exception as e:
                print(f"⚠ Error: {e}")
                if backup.exists():
                    shutil.copy2(backup, filepath)
        
        # Registrar fallo
        self.fail_count += 1
        
        return False
    
    def apply_cross_repo_solution(self, filepath: Path, line: int, code: str, 
                                  context: str, sorry_info: Dict) -> bool:
        """Aplica soluciones encontradas en otros repositorios"""
        if not sorry_info.get("similar_solutions"):
            return False
        
        best_solution = sorry_info["similar_solutions"][0]
        
        if best_solution["type"] == "proof_pattern" and best_solution.get("similarity", 0) > 0.5:
            # Intentar aplicar el patrón de prueba
            backup = self.backup_file(filepath)
            
            try:
                with open(filepath, 'r', encoding='utf-8') as f:
                    lines = f.readlines()
                
                # Reemplazar 'sorry' con la prueba encontrada (limitada)
                proof = best_solution["preview"][:200]  # Limitar tamaño
                if line - 1 < len(lines) and 'sorry' in lines[line - 1]:
                    lines[line - 1] = lines[line - 1].replace('sorry', proof, 1)
                    
                    with open(filepath, 'w', encoding='utf-8') as f:
                        f.writelines(lines)
                    
                    if self.test_compilation():
                        self.success_count += 1
                        self.changes["transformations"].append({
                            "file": str(filepath.relative_to(self.repo_root)),
                            "line": line,
                            "source_repo": best_solution["repo"],
                            "original_category": sorry_info.get("primary_category"),
                            "status": "success",
                            "cross_repo": True,
                            "similarity": best_solution["similarity"]
                        })
                        
                        self.changes["sorries_eliminated"] += 1
                        if str(filepath.relative_to(self.repo_root)) not in self.changes["files_modified"]:
                            self.changes["files_modified"].append(str(filepath.relative_to(self.repo_root)))
                        
                        print(f"✅ Éxito con solución de {best_solution['repo']}")
                        return True
                    else:
                        shutil.copy2(backup, filepath)
                        
            except Exception as e:
                print(f"⚠ Error: {e}")
                if backup.exists():
                    shutil.copy2(backup, filepath)
        
        return False
    
    def load_amda_report(self, report_path: Path) -> Dict[str, Any]:
        """Carga el reporte de AMDA Deep V2.0"""
        if not report_path.exists():
            raise FileNotFoundError(f"Reporte AMDA no encontrado: {report_path}")
        
        with open(report_path, 'r') as f:
            return json.load(f)
    
    def _resolve_trivial(self, sorry_info: Dict) -> Optional[str]:
        """Resuelve sorries triviales con rfl, simp, etc."""
        context = sorry_info.get("context", "").lower()
        
        # Patrón 1: Reflexividad
        if any(word in context for word in ["refl", "equal", "same", "identity"]):
            return "rfl"
        
        # Patrón 2: Simplificación
        if any(word in context for word in ["simp", "trivial", "obvious"]):
            return "simp"
        
        # Patrón 3: Normalización
        if "norm_num" in context or "numeric" in context:
            return "norm_num"
        
        return None
    
    def _resolve_qcal(self, sorry_info: Dict) -> Optional[str]:
        """Resuelve sorries relacionados con QCAL"""
        context = sorry_info.get("context", "")
        
        # Buscar soluciones similares de otros repos
        similar_solutions = sorry_info.get("similar_solutions", [])
        
        for solution in similar_solutions:
            if solution.get("type") == "theorem" and "QCAL" in solution.get("preview", ""):
                # Sugerir uso del teorema similar
                return f"apply {solution.get('name', 'QCAL_theorem')}"
        
        # No hay solución disponible - devolver None para evitar falsos positivos
        return None
    
    def _resolve_adelic(self, sorry_info: Dict) -> Optional[str]:
        """Resuelve sorries relacionados con estructuras adélicas"""
        # No hay solución disponible - devolver None para evitar falsos positivos
        # TODO: Implementar resolución real cuando esté disponible
        return None
    
    def _resolve_spectral(self, sorry_info: Dict) -> Optional[str]:
        """Resuelve sorries relacionados con teoría espectral"""
        # No hay solución disponible - devolver None para evitar falsos positivos
        # TODO: Implementar resolución real cuando esté disponible
        return None
    
    def apply_transformation(self, filepath: Path, sorry_info: Dict) -> bool:
        """Aplica una transformación a un archivo específico"""
        if self.dry_run:
            print(f"[DRY-RUN] Transformaría {filepath} línea {sorry_info['line']}")
            return True
        
        line = sorry_info['line']
        code = sorry_info.get('code', '')
        context = sorry_info.get('context', '')
        primary_category = sorry_info.get("primary_category", "unknown")
        
        print(f"🔧 Procesando {filepath}:{line} [{primary_category}]")
        
        # Intentar con aprendizaje para triviales
        if primary_category == "trivial":
            if self.apply_trivial_with_learning(filepath, line, code, context, sorry_info):
                return True
        
        # Intentar con soluciones cross-repo
        if sorry_info.get("similar_solutions"):
            if self.apply_cross_repo_solution(filepath, line, code, context, sorry_info):
                return True
        
        # Intentar estrategia estándar (sin compilación)
        strategy = self.STRATEGIES.get(primary_category)
        if strategy:
            new_code = strategy(sorry_info)
            if new_code:
                return self._apply_standard_transformation(filepath, line, new_code, sorry_info)
        
        print(f"⏭️  No aplicable para {filepath}:{line}")
        return False
    
    def _apply_standard_transformation(self, filepath: Path, line: int, 
                                       new_code: str, sorry_info: Dict) -> bool:
        """Aplica transformación estándar con compilación"""
        # Solo contar como eliminado si el nuevo código ya no contiene 'sorry'
        if 'sorry' in new_code:
            print(f"⚠ La transformación propuesta aún contiene 'sorry'")
            return False
        
        backup_path = filepath.with_suffix('.lean.bak')
        shutil.copy2(filepath, backup_path)
        
        try:
            with open(filepath, 'r', encoding='utf-8') as f:
                lines = f.readlines()
            
            if line - 1 < len(lines) and 'sorry' in lines[line - 1]:
                original_line = lines[line - 1]
                indentation = len(original_line) - len(original_line.lstrip())
                lines[line - 1] = ' ' * indentation + new_code + '\n'
                
                with open(filepath, 'w', encoding='utf-8') as f:
                    f.writelines(lines)
                
                # Probar compilación si no es dry-run
                if not self.dry_run and not self.test_compilation():
                    print(f"⚠ Compilación falló, revirtiendo...")
                    shutil.copy2(backup_path, filepath)
                    return False
                
                self.changes["transformations"].append({
                    "file": str(filepath.relative_to(self.repo_root)),
                    "line": line,
                    "original_category": sorry_info.get("primary_category"),
                    "resolved_category": sorry_info.get("primary_category"),
                    "original_code": original_line.strip(),
                    "new_code": new_code,
                    "sources": sorry_info.get("similar_solutions", []),
                    "remaining": -1
                })
                
                self.changes["sorries_eliminated"] += 1
                
                if str(filepath.relative_to(self.repo_root)) not in self.changes["files_modified"]:
                    self.changes["files_modified"].append(str(filepath.relative_to(self.repo_root)))
                
                print(f"✓ Transformado {filepath}:{line}")
                return True
            else:
                print(f"⚠ Sorry no encontrado en línea especificada")
                return False
                
        except Exception as e:
            print(f"❌ Error aplicando transformación: {e}")
            if backup_path.exists():
                shutil.copy2(backup_path, filepath)
            return False
    
    def generate_intelligent_commit(self, changes: List[Dict], remaining_count: int) -> str:
        """Genera un commit inteligente con todos los cambios agrupados"""
        timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
        
        # Agrupar por categoría
        by_category = defaultdict(list)
        for change in changes:
            cat = change.get('original_category', 'unknown')
            by_category[cat].append(change)
        
        # Crear mensaje de commit
        success_rate = (self.success_count / (self.success_count + self.fail_count) * 100) if (self.success_count + self.fail_count) > 0 else 0
        
        commit_msg = f"""🧠 [NOESIS-NEURAL] Resolución inteligente de {len(changes)} sorrys

## 📊 Resumen
- **Sorries eliminados:** {len(changes)}
- **Sorries restantes:** {remaining_count}
- **Tasa de éxito:** {success_rate:.1f}%

## 🔍 Detalles por categoría
"""
        
        for cat, items in by_category.items():
            commit_msg += f"\n### {cat.upper()} ({len(items)})\n"
            for item in items[:3]:  # Mostrar primeros 3
                commit_msg += f"- `{item['file']}:{item['line']}`"
                if item.get('source_repo'):
                    commit_msg += f" (inspirado en `{item['source_repo']}`)"
                if item.get('learned'):
                    commit_msg += " [patrón aprendido]"
                commit_msg += "\n"
            if len(items) > 3:
                commit_msg += f"... y {len(items) - 3} más\n"
        
        # Estadísticas de sabiduría aplicada
        repos_consulted = len(set(c.get('source_repo') for c in changes if c.get('source_repo')))
        
        commit_msg += f"""
## 🧠 Sabiduría aplicada
- **Repositorios consultados:** {repos_consulted}
- **Patrones de aprendizaje:** {len(self.learning_history['patterns'])}
- **Intentos totales:** {self.learning_history['total_attempts']}
"""
        
        if self.knowledge:
            commit_msg += f"- **Base de conocimiento:** {len(self.knowledge.get('proof_patterns', []))} patrones en {len(set(t.get('repo') for t in self.knowledge.get('theorems', [])))} repositorios\n"
        
        commit_msg += f"""
---
*Generado por AURON NEURAL V2.0 con aprendizaje y compilación*
*∴𓂀Ω∞³Φ*
"""
        
        return commit_msg
    
    def process_sorries(self, amda_report: Dict) -> int:
        """Procesa sorries del reporte AMDA"""
        enriched_sorries = amda_report.get("detailed", {})
        
        # Ordenar por prioridad
        all_sorries = []
        for file_path, sorries in enriched_sorries.items():
            for sorry in sorries:
                sorry["filepath"] = self.repo_root / file_path
                all_sorries.append(sorry)
        
        all_sorries.sort(key=lambda x: x.get("priority", 10))
        
        # Procesar hasta max_changes
        processed = 0
        for sorry in all_sorries[:self.max_changes]:
            if self.apply_transformation(sorry["filepath"], sorry):
                processed += 1
            
            # Pausa para no saturar (solo si no es dry-run)
            if not self.dry_run:
                time.sleep(1)
        
        return processed
    
    def generate_report(self) -> Dict[str, Any]:
        """Genera reporte de transformaciones"""
        # Calcular remaining desde el reporte AMDA (no hardcoded)
        remaining = self.total_sorries_from_amda - self.changes["sorries_eliminated"]
        
        return {
            "summary": {
                "files_modified": len(self.changes["files_modified"]),
                "sorries_eliminated": self.changes["sorries_eliminated"],
                "success_count": self.success_count,
                "fail_count": self.fail_count,
                "dry_run": self.dry_run
            },
            "changes": self.changes,
            "learning": {
                "patterns_learned": len(self.learning_history["patterns"]),
                "total_attempts": self.learning_history["total_attempts"]
            },
            "commit_message": self.generate_intelligent_commit(
                self.changes["transformations"], 
                remaining
            ) if self.changes["transformations"] else ""
        }
    
    def run(self, amda_report_path: Path, output_path: Optional[Path] = None) -> int:
        """Ejecuta el ejecutor neural"""
        print("🤖 AURON NEURAL V2.0 (con aprendizaje) iniciando...")
        
        try:
            # Cargar reporte AMDA
            amda_report = self.load_amda_report(amda_report_path)
            
            # Guardar total de sorries del reporte para cálculo correcto
            self.total_sorries_from_amda = amda_report.get("summary", {}).get("total_sorries", 0)
            
            # Procesar sorries
            processed = self.process_sorries(amda_report)
            
            # Generar reporte
            report = self.generate_report()
            
            if output_path is None:
                output_path = self.repo_root / 'auron_neural_report_v2.json'
            
            with open(output_path, 'w') as f:
                json.dump(report, f, indent=2)
            
            # Guardar historial de aprendizaje
            self.save_learning_history()
            
            print(f"\n📊 Reporte AURON Neural V2.0:")
            print(json.dumps(report["summary"], indent=2))
            print(f"💾 Reporte guardado en: {output_path}")
            
            if report.get("commit_message"):
                msg_file = self.repo_root / f'commit_msg_{datetime.now().strftime("%Y%m%d_%H%M%S")}.txt'
                with open(msg_file, 'w') as f:
                    f.write(report["commit_message"])
                print(f"📝 Mensaje de commit guardado en: {msg_file}")
            
            return 0
            
        except Exception as e:
            print(f"❌ Error: {e}")
            import traceback
            traceback.print_exc()
            return 1


def main():
    """Punto de entrada principal"""
    import argparse
    
    parser = argparse.ArgumentParser(description='AURON NEURAL V2.0 - Ejecutor con Aprendizaje')
    parser.add_argument('amda_report', type=Path, help='Ruta al reporte de AMDA')
    parser.add_argument('--output', type=Path, help='Archivo de salida')
    parser.add_argument('--dry-run', action='store_true', help='Modo de prueba')
    parser.add_argument('--max-changes', type=int, default=20, help='Máximo de cambios')
    
    args = parser.parse_args()
    
    executor = AuronNeuralV2(dry_run=args.dry_run, max_changes=args.max_changes)
    sys.exit(executor.run(args.amda_report, output_path=args.output))


if __name__ == "__main__":
    main()
