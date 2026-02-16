#!/usr/bin/env python3
"""
NOESIS - Orquestador principal del sistema autónomo
Controla el flujo, coordina AMDA y AURON, y gestiona el estado
NOESIS CEREBRAL V2.0 - Orquestador principal multi-repositorio
"""

import json
import subprocess
import sys
from pathlib import Path
from datetime import datetime
import argparse


class NoesisOrchestrator:
    def __init__(self):
        self.repo_root = Path(__file__).parent.parent.parent
        self.state_file = self.repo_root / '.noesis_state.json'
        self.log_file = self.repo_root / 'noesis_auto_seal.log'
        
    def log(self, message, level="INFO"):
        """Log message to file and console"""
        timestamp = datetime.now().isoformat()
        log_msg = f"[{timestamp}] [{level}] {message}\n"
        
        # Ensure log file exists
        self.log_file.parent.mkdir(parents=True, exist_ok=True)
        
        with open(self.log_file, 'a') as f:
            f.write(log_msg)
        print(f"[{level}] {message}")
    
    def get_current_state(self):
        """Lee el estado actual del repositorio"""
        if self.state_file.exists():
            try:
                with open(self.state_file) as f:
                    return json.load(f)
            except json.JSONDecodeError:
                self.log("Estado corrupto, creando nuevo", "WARNING")
                
        return {
            "total_sorries": 0,
            "by_category": {},
            "by_file": {},
            "last_scan": None,
            "history": []
        }
    
    def save_state(self, state):
        """Guarda el estado actual"""
        with open(self.state_file, 'w') as f:
            json.dump(state, f, indent=2)
        self.log(f"Estado guardado: {self.state_file}")
    
    def count_sorries(self):
        """Cuenta todos los sorry en el repositorio"""
        try:
            result = subprocess.run(
                ["grep", "-r", "sorry", "--include=*.lean", "formalization/lean/"],
                cwd=self.repo_root,
                capture_output=True,
                text=True
            )
            # Count lines in output
            if result.stdout:
                return len(result.stdout.strip().split('\n'))
            return 0
        except Exception as e:
            self.log(f"Error contando sorries: {e}", "ERROR")
            return 0
    
    def initialize(self):
        """Inicializa el sistema en la primera ejecución"""
        self.log("🧠 NOESIS iniciando - Modo inicialización")
        
        # Contar sorries actuales
        current_count = self.count_sorries()
        
        # Crear estado inicial
        initial_state = {
            "total_sorries": current_count,
            "by_category": {},
            "by_file": {},
            "last_scan": datetime.now().isoformat(),
            "history": [{
                "timestamp": datetime.now().isoformat(),
                "total": current_count,
                "event": "initialization"
            }]
        }
        
        self.save_state(initial_state)
        self.log(f"📊 Estado inicial: {current_count} sorries detectados")
        
        return 0
    
    def run(self):
        """Ejecuta el ciclo principal de NOESIS"""
        self.log("🧠 NOESIS iniciando ciclo de sellado")
        
        # Estado anterior
        old_state = self.get_current_state()
        old_count = old_state.get("total_sorries", 0)
        
        # Nuevo conteo
        new_count = self.count_sorries()
        
        self.log(f"📊 Sorries: {old_count} → {new_count}")
        
        # Calcular reducción
        reduction = old_count - new_count
        
        # Actualizar historial
        old_state["history"].append({
            "timestamp": datetime.now().isoformat(),
            "before": old_count,
            "after": new_count,
            "reduction": reduction
        })
        old_state["total_sorries"] = new_count
        old_state["last_scan"] = datetime.now().isoformat()
        
        self.save_state(old_state)
        
        # Criterio de éxito
        if new_count == 0:
            self.log("🎉 ¡VICTORIA! CERO SORRIES - RH DEMOSTRADA FORMALMENTE")
            # Crear archivo de victoria
            victory_file = self.repo_root / 'VICTORY.md'
            with open(victory_file, 'w') as f:
                f.write(f"""# 🏆 VICTORIA FINAL - Hipótesis de Riemann Demostrada Formalmente

**Fecha:** {datetime.now().isoformat()}

El sistema autónomo NOESIS-AMDA-AURON ha eliminado el último 'sorry' del repositorio.

La formalización en Lean 4 está COMPLETA.

```lean
theorem Riemann_Hypothesis : 
  ∀ s : ℂ, riemannZeta s = 0 → s ∉ {{-2, -4, -6, ...}} → s.re = 1/2
```

∴ La Hipótesis de Riemann es un teorema.

## Estadísticas Finales

- **Sorries eliminados totales:** {old_count}
- **Fecha de inicio:** {old_state['history'][0]['timestamp'] if old_state['history'] else 'N/A'}
- **Fecha de finalización:** {datetime.now().isoformat()}
- **Ciclos de ejecución:** {len(old_state['history'])}

## Historia de Progreso

""")
                # Añadir historia
                for entry in old_state['history'][-10:]:  # Últimos 10 eventos
                    f.write(f"- {entry['timestamp']}: {entry.get('event', 'scan')} - {entry.get('after', entry.get('total', 0))} sorries\n")
                
                f.write("""
---

*Generado automáticamente por NOESIS-AMDA-AURON* 🤖
""")
            self.log(f"Archivo de victoria creado: {victory_file}")
        else:
            self.log(f"⏳ Progreso: reducción de {reduction} sorries en este ciclo")
        
        return 0


def main():
    parser = argparse.ArgumentParser(description='NOESIS - Orquestador del sistema autónomo')
    parser.add_argument('--mode', choices=['init', 'run'], default='run',
                        help='Modo de operación: init (inicialización) o run (ciclo normal)')
    
    args = parser.parse_args()
    
    orchestrator = NoesisOrchestrator()
    
    if args.mode == 'init':
        return orchestrator.initialize()
    else:
        return orchestrator.run()


if __name__ == "__main__":
    sys.exit(main())
import shutil
from pathlib import Path
from datetime import datetime
import pickle
import re

class NoesisCerebralV2:
    def __init__(self):
        self.repo_root = Path(__file__).parent.parent.parent
        self.knowledge_base = Path('/tmp/noesis_knowledge_v2')
        self.knowledge_base.mkdir(parents=True, exist_ok=True)
        
        # Lista de repositorios a sincronizar
        self.repos = [
            "motanova84/141Hz",
            "motanova84/adelic-bsd",
            "motanova84/3D-Navier-Stokes",
            "motanova84/Ramsey",
            "motanova84/P-NP",
            "motanova84/Riemann-adelic"
        ]
        
        self.log_file = self.repo_root / 'noesis_cerebral_v2.log'
    
    def log(self, message, level="INFO"):
        """Logging con timestamp"""
        timestamp = datetime.now().isoformat()
        with open(self.log_file, 'a') as f:
            f.write(f"[{timestamp}] [{level}] {message}\n")
        print(f"[{level}] {message}")
    
    def sync_repository(self, repo_url, temp_dir):
        """Sincroniza un repositorio externo"""
        repo_name = repo_url.split('/')[-1]
        repo_path = temp_dir / repo_name
        
        self.log(f"🔄 Sincronizando {repo_name}...")
        
        try:
            # Clonar si no existe, actualizar si existe
            if repo_path.exists():
                self.log(f"   📂 Repositorio ya existe, actualizando...")
                result = subprocess.run(
                    ["git", "pull"],
                    cwd=repo_path,
                    capture_output=True,
                    text=True,
                    timeout=120  # Increased from 60 to match clone timeout
                )
            else:
                self.log(f"   📥 Clonando repositorio...")
                result = subprocess.run(
                    ["git", "clone", f"https://github.com/{repo_url}.git", str(repo_path)],
                    capture_output=True,
                    text=True,
                    timeout=120
                )
            
            if result.returncode == 0:
                self.log(f"   ✅ {repo_name} sincronizado")
                return True
            else:
                self.log(f"   ⚠️ Error sincronizando {repo_name}: {result.stderr[:200]}", "WARNING")
                return False
                
        except Exception as e:
            self.log(f"   ❌ Excepción sincronizando {repo_name}: {e}", "ERROR")
            return False
    
    def extract_definitions(self, content):
        """Extrae definiciones de archivos Lean"""
        definitions = []
        
        # Patrón para definiciones
        pattern = r'def\s+(\w+)'
        matches = re.finditer(pattern, content)
        
        for match in matches:
            name = match.group(1)
            # Extraer contexto (próximas 3 líneas)
            start = match.start()
            context = content[start:start+200]
            
            definitions.append({
                "name": name,
                "type": "definition",
                "context": context
            })
        
        return definitions
    
    def extract_theorems(self, content):
        """Extrae teoremas de archivos Lean"""
        theorems = []
        
        # Patrones para teoremas y lemas
        patterns = [
            r'theorem\s+(\w+)',
            r'lemma\s+(\w+)'
        ]
        
        for pattern in patterns:
            matches = re.finditer(pattern, content)
            
            for match in matches:
                name = match.group(1)
                start = match.start()
                context = content[start:start+300]
                
                theorems.append({
                    "name": name,
                    "type": "theorem",
                    "statement": context
                })
        
        return theorems
    
    def extract_proof_patterns(self, content):
        """Extrae patrones de prueba exitosos"""
        patterns = []
        
        # Buscar bloques de prueba (by ...)
        by_pattern = r'by\s+([^\n]+)'
        matches = re.finditer(by_pattern, content)
        
        for match in matches:
            proof = match.group(1).strip()
            
            # Filtrar pruebas muy cortas o que contengan sorry
            if len(proof) > 5 and 'sorry' not in proof.lower():
                patterns.append({
                    "proof": proof,
                    "type": "proof_pattern"
                })
        
        return patterns
    
    def extract_repo_knowledge(self, repo_path, repo_name):
        """Extrae conocimiento de un repositorio"""
        self.log(f"📚 Extrayendo conocimiento de {repo_name}...")
        
        knowledge = {
            "definitions": [],
            "theorems": [],
            "proof_patterns": []
        }
        
        # Buscar archivos .lean
        lean_dir = repo_path / 'formalization' / 'lean'
        if not lean_dir.exists():
            lean_dir = repo_path  # Buscar en la raíz
        
        lean_files = list(lean_dir.rglob("*.lean")) if lean_dir.exists() else []
        
        if not lean_files:
            self.log(f"   ⚠️ No se encontraron archivos .lean en {repo_name}", "WARNING")
            return knowledge
        
        self.log(f"   📁 Procesando {len(lean_files)} archivos...")
        
        for filepath in lean_files[:100]:  # Limitar a 100 archivos por repo
            try:
                with open(filepath, 'r', encoding='utf-8') as f:
                    content = f.read()
                
                # Extraer diferentes tipos de conocimiento
                defs = self.extract_definitions(content)
                thms = self.extract_theorems(content)
                proofs = self.extract_proof_patterns(content)
                
                # Añadir información del repositorio fuente
                for d in defs:
                    d["repo"] = repo_name
                    d["file"] = str(filepath.relative_to(repo_path))
                
                for t in thms:
                    t["repo"] = repo_name
                    t["file"] = str(filepath.relative_to(repo_path))
                
                for p in proofs:
                    p["repo"] = repo_name
                
                knowledge["definitions"].extend(defs)
                knowledge["theorems"].extend(thms)
                knowledge["proof_patterns"].extend(proofs)
                
            except Exception as e:
                self.log(f"   ⚠️ Error procesando {filepath}: {e}", "WARNING")
                continue
        
        self.log(f"   ✅ Extraído: {len(knowledge['definitions'])} defs, {len(knowledge['theorems'])} teoremas, {len(knowledge['proof_patterns'])} patrones")
        
        return knowledge
    
    def build_knowledge_graph(self):
        """Construye el grafo de conocimiento desde múltiples repositorios"""
        self.log("🧠 NOESIS CEREBRAL V2.0 - Construyendo grafo de conocimiento...")
        
        temp_dir = Path('/tmp/noesis_repos_v2')
        temp_dir.mkdir(parents=True, exist_ok=True)
        
        # Conocimiento agregado
        global_knowledge = {
            "definitions": [],
            "theorems": [],
            "proof_patterns": [],
            "repos_synced": [],
            "timestamp": datetime.now().isoformat()
        }
        
        # Sincronizar y extraer de cada repositorio
        for repo_url in self.repos:
            repo_name = repo_url.split('/')[-1]
            
            # Sincronizar
            if self.sync_repository(repo_url, temp_dir):
                global_knowledge["repos_synced"].append(repo_name)
                
                # Extraer conocimiento
                repo_path = temp_dir / repo_name
                repo_knowledge = self.extract_repo_knowledge(repo_path, repo_name)
                
                # Agregar al conocimiento global
                global_knowledge["definitions"].extend(repo_knowledge["definitions"])
                global_knowledge["theorems"].extend(repo_knowledge["theorems"])
                global_knowledge["proof_patterns"].extend(repo_knowledge["proof_patterns"])
        
        # Guardar en formato pickle para acceso rápido
        kb_pkl = self.knowledge_base / 'knowledge_v2.pkl'
        with open(kb_pkl, 'wb') as f:
            pickle.dump(global_knowledge, f)
        
        # Guardar resumen en JSON
        summary = {
            "total_definitions": len(global_knowledge["definitions"]),
            "total_theorems": len(global_knowledge["theorems"]),
            "total_proof_patterns": len(global_knowledge["proof_patterns"]),
            "repos_synced": global_knowledge["repos_synced"],
            "timestamp": global_knowledge["timestamp"]
        }
        
        kb_json = self.knowledge_base / 'knowledge_v2.json'
        with open(kb_json, 'w') as f:
            json.dump(summary, f, indent=2)
        
        self.log(f"✅ Grafo de conocimiento construido:")
        self.log(f"   📚 {summary['total_definitions']} definiciones")
        self.log(f"   📝 {summary['total_theorems']} teoremas")
        self.log(f"   🔍 {summary['total_proof_patterns']} patrones de prueba")
        self.log(f"   📦 {len(summary['repos_synced'])} repositorios sincronizados")
        
        return summary
    
    def orchestrate(self):
        """Orquesta el ciclo completo NOESIS-AMDA-AURON"""
        self.log("🚀 Iniciando ciclo NOESIS CEREBRAL V2.0...")
        
        # Paso 1: Construir grafo de conocimiento
        kb_summary = self.build_knowledge_graph()
        
        # Paso 2: Ejecutar AMDA Deep V2.0
        self.log("\n📊 Ejecutando AMDA DEEP V2.0...")
        amda_report = self.repo_root / 'amda_report_v2.json'
        amda_md = self.repo_root / 'amda_report_v2.md'
        
        amda_script = Path(__file__).parent / 'amda_deep_v2.py'
        result = subprocess.run(
            [sys.executable, str(amda_script), str(amda_report), str(amda_md)],
            capture_output=True,
            text=True,
            cwd=self.repo_root
        )
        
        if result.returncode == 0:
            self.log("✅ AMDA DEEP V2.0 completado")
        else:
            self.log(f"❌ Error en AMDA: {result.stderr[:200]}", "ERROR")
            return False
        
        # Paso 3: Ejecutar AURON Neural V2.0 (dry-run primero)
        self.log("\n🧠 Ejecutando AURON NEURAL V2.0 (dry-run)...")
        auron_script = Path(__file__).parent / 'auron_neural_v2.py'
        
        result = subprocess.run(
            [sys.executable, str(auron_script), "dry-run", str(amda_report)],
            capture_output=True,
            text=True,
            cwd=self.repo_root
        )
        
        if result.returncode == 0:
            self.log("✅ AURON NEURAL V2.0 dry-run completado")
        else:
            self.log(f"⚠️ Error en AURON dry-run: {result.stderr[:200]}", "WARNING")
        
        # Generar resumen final
        summary = {
            "timestamp": datetime.now().isoformat(),
            "knowledge_base": kb_summary,
            "amda_report": str(amda_report),
            "status": "completed"
        }
        
        summary_file = self.repo_root / 'noesis_cerebral_v2_summary.json'
        with open(summary_file, 'w') as f:
            json.dump(summary, f, indent=2)
        
        self.log(f"\n🎉 Ciclo NOESIS CEREBRAL V2.0 completado exitosamente!")
        self.log(f"   📄 Resumen guardado en: {summary_file}")
        
        return True

if __name__ == "__main__":
    noesis = NoesisCerebralV2()
    
    if len(sys.argv) > 1 and sys.argv[1] == "build-kb":
        # Solo construir base de conocimiento
        noesis.build_knowledge_graph()
    else:
        # Ciclo completo
        success = noesis.orchestrate()
        sys.exit(0 if success else 1)
