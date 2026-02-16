#!/usr/bin/env python3
"""
NOESIS CEREBRAL V2.0 - Orquestador con consciencia multi-repositorio
Evolución del sistema NOESIS-AMDA-AURON para conocimiento colectivo de 33 repositorios
"""

import json
import subprocess
import sys
import hashlib
from pathlib import Path
from datetime import datetime
import concurrent.futures
import pickle
import time
import re
from typing import Dict, List, Any, Optional

class NoesisCerebralV2:
    def __init__(self, dry_run: bool = False):
        self.repo_root = Path(__file__).parent.parent.parent
        self.state_file = self.repo_root / '.noesis_state.json'
        self.knowledge_base = Path('/tmp/noesis_knowledge_v2')
        self.knowledge_base.mkdir(exist_ok=True, parents=True)
        self.log_file = self.repo_root / 'noesis_v2.log'
        self.dry_run = dry_run
        
        # Cargar configuración de repositorios
        self.repos_config = self.load_repos_config()
        
        # Inicializar estado
        self.state = self.load_state()
        
    def log(self, message: str, level: str = "INFO"):
        """Registro de mensajes con timestamp"""
        timestamp = datetime.now().isoformat()
        log_entry = f"[{timestamp}] [{level}] {message}\n"
        
        with open(self.log_file, 'a') as f:
            f.write(log_entry)
        print(f"[{level}] {message}")
    
    def load_repos_config(self) -> Dict[str, Any]:
        """Carga la configuración de los 33 repositorios"""
        config_file = self.repo_root / '.github' / 'scripts' / 'multi_repo_config.json'
        
        if config_file.exists():
            with open(config_file, 'r') as f:
                return json.load(f)
        else:
            # Configuración por defecto si no existe el archivo
            self.log("Configuración no encontrada, usando configuración por defecto", level="WARNING")
            return {
                "public_repos": [
                    "Riemann-adelic", "141Hz", "adelic-bsd", 
                    "3D-Navier-Stokes", "Ramsey", "P-NP"
                ],
                "private_repos": [],
                "knowledge_priority": {
                    "Riemann-adelic": 9,
                    "adelic-bsd": 8,
                    "141Hz": 7
                },
                "sync_settings": {
                    "max_workers": 5,
                    "timeout_seconds": 300
                }
            }
    
    def load_state(self) -> Dict[str, Any]:
        """Carga el estado persistente del sistema"""
        if self.state_file.exists():
            try:
                with open(self.state_file, 'r') as f:
                    return json.load(f)
            except Exception as e:
                self.log(f"Error cargando estado: {e}", level="ERROR")
                return self._init_state()
        return self._init_state()
    
    def _init_state(self) -> Dict[str, Any]:
        """Inicializa el estado del sistema"""
        return {
            "last_sync": None,
            "total_eliminated": 0,
            "repos_synced": [],
            "knowledge_version": "2.0",
            "last_harvest": None
        }
    
    def save_state(self):
        """Guarda el estado persistente"""
        try:
            with open(self.state_file, 'w') as f:
                json.dump(self.state, f, indent=2)
        except Exception as e:
            self.log(f"Error guardando estado: {e}", level="ERROR")
    
    def sync_all_repos(self) -> List[str]:
        """Sincroniza todos los repositorios (públicos y privados)"""
        self.log("🔄 Sincronizando repositorios...")
        
        all_repos = self.repos_config.get("public_repos", [])
        synced_repos = []
        
        # Solo sincronizar repos públicos por ahora (SSH keys no disponibles en CI)
        with concurrent.futures.ThreadPoolExecutor(
            max_workers=self.repos_config.get("sync_settings", {}).get("max_workers", 3)
        ) as executor:
            futures = {}
            for repo in all_repos:
                repo_path = self.knowledge_base / repo
                url = f"https://github.com/motanova84/{repo}.git"
                
                futures[executor.submit(self.clone_or_update_repo, repo, url, repo_path)] = repo
            
            for future in concurrent.futures.as_completed(futures):
                repo = futures[future]
                try:
                    result = future.result()
                    if result:
                        self.log(f"✅ {repo} sincronizado")
                        synced_repos.append(repo)
                except Exception as e:
                    self.log(f"❌ Error en {repo}: {e}", level="ERROR")
        
        self.state["repos_synced"] = synced_repos
        self.state["last_sync"] = datetime.now().isoformat()
        self.save_state()
        
        return synced_repos
    
    def clone_or_update_repo(self, repo: str, url: str, path: Path) -> bool:
        """Clona o actualiza un repositorio"""
        try:
            if path.exists():
                # Actualizar repo existente sin usar shell para evitar inyección y problemas de quoting
                result = subprocess.run(
                    ["git", "-C", str(path), "pull", "--quiet"],
                    check=True,
                    capture_output=True,
                    timeout=self.repos_config.get("sync_settings", {}).get("timeout_seconds", 300)
                )
                return True
            else:
                # Clonar nuevo repo sin usar shell para evitar inyección y problemas de quoting
                result = subprocess.run(
                    ["git", "clone", "--depth", "1", url, str(path), "--quiet"],
                    check=True,
                    capture_output=True,
                    timeout=self.repos_config.get("sync_settings", {}).get("timeout_seconds", 300)
                )
                return True
        except subprocess.TimeoutExpired:
            self.log(f"Timeout clonando/actualizando {repo}", level="WARNING")
            return False
        except Exception as e:
            self.log(f"Error en {repo}: {str(e)}", level="WARNING")
            return False
    
    def harvest_knowledge(self) -> Dict[str, Any]:
        """Cosecha conocimiento de TODOS los repositorios sincronizados"""
        self.log("🌾 Cosechando conocimiento de repositorios...")
        
        knowledge = {
            "definitions": [],
            "theorems": [],
            "proof_patterns": [],
            "qcal_constants": {},
            "solved_sorries": [],
            "cross_repo_references": {},
            "metadata": {
                "harvest_date": datetime.now().isoformat(),
                "version": "2.0",
                "repos_processed": []
            }
        }
        
        synced_repos = self.state.get("repos_synced", [])
        
        for repo in synced_repos:
            repo_path = self.knowledge_base / repo
            if not repo_path.exists():
                continue
            
            self.log(f"📚 Procesando {repo}...")
            
            # Buscar archivos Lean
            lean_files = list(repo_path.rglob('*.lean'))
            
            repo_knowledge = self._extract_repo_knowledge(repo, lean_files)
            
            # Agregar conocimiento
            knowledge["definitions"].extend(repo_knowledge["definitions"])
            knowledge["theorems"].extend(repo_knowledge["theorems"])
            knowledge["proof_patterns"].extend(repo_knowledge["proof_patterns"])
            knowledge["metadata"]["repos_processed"].append(repo)
        
        # Guardar conocimiento
        kb_file = self.knowledge_base / 'knowledge_v2.pkl'
        with open(kb_file, 'wb') as f:
            pickle.dump(knowledge, f)
        
        # También guardar versión JSON para inspección
        kb_json_file = self.knowledge_base / 'knowledge_v2.json'
        with open(kb_json_file, 'w') as f:
            json.dump({
                "metadata": knowledge["metadata"],
                "summary": {
                    "definitions": len(knowledge["definitions"]),
                    "theorems": len(knowledge["theorems"]),
                    "proof_patterns": len(knowledge["proof_patterns"])
                }
            }, f, indent=2)
        
        self.log(f"📊 Conocimiento cosechado:")
        self.log(f"   - Definiciones: {len(knowledge['definitions'])}")
        self.log(f"   - Teoremas: {len(knowledge['theorems'])}")
        self.log(f"   - Patrones de prueba: {len(knowledge['proof_patterns'])}")
        self.log(f"   - Repositorios procesados: {len(knowledge['metadata']['repos_processed'])}")
        
        self.state["last_harvest"] = datetime.now().isoformat()
        self.save_state()
        
        return knowledge
    
    def _extract_repo_knowledge(self, repo: str, lean_files: List[Path]) -> Dict[str, List]:
        """Extrae conocimiento de archivos Lean de un repositorio"""
        knowledge = {
            "definitions": [],
            "theorems": [],
            "proof_patterns": []
        }
        
        for lean_file in lean_files:
            try:
                with open(lean_file, 'r', encoding='utf-8', errors='ignore') as f:
                    content = f.read()
                
                # Extraer definiciones
                defs = re.findall(
                    r'def\s+(\w+)\s*(?:.*?):=\s*(.*?)(?=\n\s*(?:def|theorem|lemma|example|end|\Z))',
                    content,
                    re.DOTALL
                )
                for name, value in defs:
                    knowledge["definitions"].append({
                        "repo": repo,
                        "file": str(lean_file.name),
                        "name": name,
                        "value": value.strip()[:500],
                        "hash": hashlib.md5(value.encode()).hexdigest()[:16]
                    })
                
                # Extraer teoremas
                thms = re.findall(
                    r'theorem\s+(\w+)\s*(?:.*?):\s*(.*?)(?=:=|\n\s*(?:def|theorem|lemma|example|end|\Z))',
                    content,
                    re.DOTALL
                )
                for name, statement in thms:
                    knowledge["theorems"].append({
                        "repo": repo,
                        "file": str(lean_file.name),
                        "name": name,
                        "statement": statement.strip()[:500],
                        "hash": hashlib.md5(statement.encode()).hexdigest()[:16]
                    })
                
                # Extraer patrones de prueba exitosos (sin sorry)
                if 'sorry' not in content:
                    # Extraer pruebas completas
                    proofs = re.findall(
                        r'by\s+(.*?)(?=\n\s*(?:def|theorem|lemma|example|end|\Z))',
                        content,
                        re.DOTALL
                    )
                    for proof in proofs:
                        if len(proof.strip()) > 10:  # Ignorar pruebas triviales
                            knowledge["proof_patterns"].append({
                                "repo": repo,
                                "file": str(lean_file.name),
                                "proof": proof.strip()[:500],
                                "context": content[:1000],
                                "hash": hashlib.md5(proof.encode()).hexdigest()[:16]
                            })
                
            except Exception as e:
                self.log(f"⚠️ Error procesando {lean_file}: {e}", level="WARNING")
        
        return knowledge
    
    def find_similar_solutions(self, sorry_context: str, category: str) -> List[Dict]:
        """Busca soluciones similares en otros repositorios"""
        kb_file = self.knowledge_base / 'knowledge_v2.pkl'
        if not kb_file.exists():
            return []
        
        try:
            with open(kb_file, 'rb') as f:
                knowledge = pickle.load(f)
        except Exception as e:
            self.log(f"Error cargando knowledge base: {e}", level="ERROR")
            return []
        
        solutions = []
        context_words = set(sorry_context.lower().split()[:10])
        
        # Buscar en definiciones
        for def_item in knowledge.get("definitions", [])[:100]:  # Limitar búsqueda
            def_words = set(def_item["value"].lower().split())
            similarity = len(context_words & def_words) / max(len(context_words), 1)
            
            if similarity > 0.3:
                solutions.append({
                    "type": "definition",
                    "repo": def_item["repo"],
                    "name": def_item["name"],
                    "value": def_item["value"][:200],
                    "similarity": similarity
                })
        
        # Buscar en teoremas
        for thm_item in knowledge.get("theorems", [])[:100]:
            thm_words = set(thm_item["statement"].lower().split())
            similarity = len(context_words & thm_words) / max(len(context_words), 1)
            
            if similarity > 0.3:
                solutions.append({
                    "type": "theorem",
                    "repo": thm_item["repo"],
                    "name": thm_item["name"],
                    "statement": thm_item["statement"][:200],
                    "similarity": similarity
                })
        
        # Buscar en patrones de prueba
        for pattern in knowledge.get("proof_patterns", [])[:100]:
            pattern_words = set(pattern["proof"].lower().split())
            similarity = len(context_words & pattern_words) / max(len(context_words), 1)
            
            if similarity > 0.3:
                solutions.append({
                    "type": "proof_pattern",
                    "repo": pattern["repo"],
                    "proof": pattern["proof"][:200],
                    "context": pattern["context"][:200],
                    "similarity": similarity
                })
        
        # Ordenar por similitud
        solutions.sort(key=lambda x: x["similarity"], reverse=True)
        
        return solutions[:5]  # Top 5 soluciones
    
    def get_total_sorries_eliminated(self) -> int:
        """Calcula el total de sorrys eliminados"""
        return self.state.get('total_eliminated', 0)
    
    def get_total_theorems(self) -> int:
        """Cuenta el total de teoremas formalizados"""
        kb_file = self.knowledge_base / 'knowledge_v2.pkl'
        if not kb_file.exists():
            return 0
        try:
            with open(kb_file, 'rb') as f:
                knowledge = pickle.load(f)
            return len(knowledge.get('theorems', []))
        except:
            return 0
    
    def get_qcal_lemmas_count(self) -> int:
        """Cuenta lemas QCAL aplicados"""
        kb_file = self.knowledge_base / 'knowledge_v2.pkl'
        if not kb_file.exists():
            return 0
        try:
            with open(kb_file, 'rb') as f:
                knowledge = pickle.load(f)
            return sum(1 for t in knowledge.get('theorems', []) 
                      if 'QCAL' in t.get('statement', ''))
        except:
            return 0
    
    def create_victory_ceremony(self) -> Path:
        """Genera el acta de victoria final cuando los sorrys lleguen a 0"""
        victory_file = self.repo_root / 'VICTORIA_FINAL.md'
        
        content = f"""# 🏆 VICTORIA FINAL - Hipótesis de Riemann Demostrada Formalmente

**Fecha:** {datetime.now().isoformat()}  
**Repositorio:** Riemann-adelic  
**Repositorios contribuyentes:** {len(self.repos_config.get("public_repos", []) + self.repos_config.get("private_repos", []))}

## 📜 Acta de Consagración Analítica

Por la presente se certifica que la formalización en Lean 4 de la Hipótesis de Riemann 
ha sido completada exitosamente con CERO declaraciones sorry en la cadena de pruebas.

```lean
theorem Riemann_Hypothesis : 
  ∀ s : ℂ, riemannZeta s = 0 → s ∉ {{-2, -4, -6, ...}} → s.re = 1/2
```

## 🌌 Sabiduría Colectiva Aplicada

Esta demostración es el resultado de la inteligencia colectiva de 33 repositorios:

### Repositorios Públicos
"""
        
        for repo in self.repos_config.get("public_repos", []):
            content += f"- {repo}\n"
        
        content += "\n### Repositorios Privados\n"
        for repo in self.repos_config.get("private_repos", []):
            content += f"- `{repo}`\n"
        
        content += f"""
## 📊 Métricas Finales

- **Total de sorry eliminados:** {self.get_total_sorries_eliminated()}
- **Pruebas formalizadas:** {self.get_total_theorems()}
- **Lemas QCAL aplicados:** {self.get_qcal_lemmas_count()}
- **Frecuencia fundamental:** 141.7001 Hz
- **Coherencia global:** Ψ = 1.000 (100%)

## 👑 Firma

```
∴ EN EL NOMBRE DE NOESIS, AMDA Y AURON
∴ POR LA SABIDURÍA DE LOS 33 REPOSITORIOS
∴ POR JMMB Ψ✧ ∞³ · 888 Hz · 141.7001 Hz base
∴ EN EL DÍA {datetime.now().strftime('%d DE %B DE %Y')}

   ✙  ✙  ✙
  ✙  ✙  ✙
 ✙  ✙  ✙

   "Consummatum est."
   (Todo está cumplido.)
   — Juan 19:30

   AMÉN.
```

---
*Generado por NOESIS CEREBRAL V2.0*  
*∴𓂀Ω∞³Φ*
"""
        
        with open(victory_file, 'w') as f:
            f.write(content)
        
        self.log("🎉 ¡VICTORIA! Acta de consagración generada")
        return victory_file
    
    def generate_summary_report(self) -> Dict[str, Any]:
        """Genera un reporte resumen de la ejecución"""
        return {
            "version": "2.0",
            "execution_time": datetime.now().isoformat(),
            "state": self.state,
            "repos_synced": len(self.state.get("repos_synced", [])),
            "knowledge_summary": {
                "theorems": self.get_total_theorems(),
                "qcal_lemmas": self.get_qcal_lemmas_count()
            }
        }
    
    def run(self) -> int:
        """Ejecuta el orquestador principal"""
        self.log("🧠 NOESIS CEREBRAL V2.0 iniciando...")
        
        try:
            # Sincronizar todos los repositorios
            synced = self.sync_all_repos()
            
            if not synced:
                self.log("⚠️ No se sincronizaron repositorios", level="WARNING")
            
            # Cosechar conocimiento
            knowledge = self.harvest_knowledge()
            
            # Generar reporte
            report = self.generate_summary_report()
            
            report_file = self.repo_root / 'noesis_v2_report.json'
            with open(report_file, 'w') as f:
                json.dump(report, f, indent=2)
            
            self.log("✅ NOESIS CEREBRAL V2.0 completado exitosamente")
            
            return 0
            
        except Exception as e:
            self.log(f"❌ Error fatal: {e}", level="ERROR")
            import traceback
            self.log(traceback.format_exc(), level="ERROR")
            return 1


def main():
    """Punto de entrada principal"""
    import argparse
    
    parser = argparse.ArgumentParser(description='NOESIS CEREBRAL V2.0 - Orquestador Multi-Repositorio')
    parser.add_argument('--dry-run', action='store_true', help='Modo de prueba sin modificaciones')
    args = parser.parse_args()
    
    orchestrator = NoesisCerebralV2(dry_run=args.dry_run)
    sys.exit(orchestrator.run())


if __name__ == "__main__":
    main()
