#!/usr/bin/env python3
"""
NOESIS CEREBRAL V2.0 - Orchestrator
Sincroniza múltiples repositorios y extrae conocimiento para AMDA y AURON
"""

import json
import subprocess
import sys
import pickle
from pathlib import Path
from datetime import datetime
import re
from collections import defaultdict

class NoesisOrchestrator:
    """Orquestador central del sistema NOESIS CEREBRAL V2.0"""
    
    # Constantes de configuración
    MAX_CONTENT_LENGTH = 200  # Caracteres máximos para contenido extraído
    
    def __init__(self, config_path):
        self.config = self.load_config(config_path)
        self.knowledge_dir = Path('/tmp/noesis_knowledge_v2')
        self.knowledge_dir.mkdir(parents=True, exist_ok=True)
        self.knowledge = {
            "definitions": [],
            "theorems": [],
            "proof_patterns": [],
            "repos_synced": []
        }
        
    def log(self, message, level="INFO"):
        """Log con timestamp"""
        timestamp = datetime.now().isoformat()
        print(f"[{timestamp}] [{level}] {message}")
    
    def load_config(self, config_path):
        """Carga configuración de repositorios"""
        with open(config_path) as f:
            return json.load(f)
    
    def sync_repo(self, repo_url, repo_name, branch="main"):
        """Clona o actualiza un repositorio"""
        repo_path = self.knowledge_dir / repo_name
        
        try:
            if repo_path.exists():
                self.log(f"📦 Actualizando {repo_name}...")
                subprocess.run(
                    ["git", "-C", str(repo_path), "pull"],
                    capture_output=True, check=True, timeout=30
                )
            else:
                self.log(f"📥 Clonando {repo_name}...")
                subprocess.run(
                    ["git", "clone", "--depth", "1", "--branch", branch, 
                     repo_url, str(repo_path)],
                    capture_output=True, check=True, timeout=60
                )
            
            return True
        except subprocess.TimeoutExpired:
            self.log(f"⚠️ Timeout sincronizando {repo_name}", "WARNING")
            return False
        except subprocess.CalledProcessError as e:
            self.log(f"⚠️ Error sincronizando {repo_name}: {e}", "WARNING")
            return False
    
    def extract_definitions(self, content):
        """Extrae definiciones de un archivo Lean"""
        definitions = []
        # Patrón para definiciones: def nombre ...
        pattern = re.compile(r'def\s+(\w+)(?:\s+\(.*?\))?\s*:=?\s*(.*?)(?=\n\S|\Z)', re.DOTALL)
        
        for match in pattern.finditer(content):
            definitions.append({
                "name": match.group(1),
                "content": match.group(2).strip()[:self.MAX_CONTENT_LENGTH]
            })
        
        return definitions
    
    def extract_theorems(self, content):
        """Extrae teoremas de un archivo Lean"""
        theorems = []
        # Patrón para teoremas: theorem nombre ...
        pattern = re.compile(r'theorem\s+(\w+)(?:\s+\(.*?\))?\s*:\s*(.*?)(?:by|:=)', re.DOTALL)
        
        for match in pattern.finditer(content):
            theorems.append({
                "name": match.group(1),
                "statement": match.group(2).strip()[:self.MAX_CONTENT_LENGTH]
            })
        
        return theorems
    
    def extract_proof_patterns(self, content):
        """Extrae patrones de prueba de un archivo Lean"""
        patterns = []
        # Buscar bloques de prueba
        proof_pattern = re.compile(r'by\s+(.*?)(?=\n\s*$|\n\w)', re.DOTALL)
        
        for match in proof_pattern.finditer(content):
            proof = match.group(1).strip()
            if proof and len(proof) < 500:  # Limitar tamaño
                patterns.append({
                    "proof": proof
                })
        
        return patterns
    
    def extract_repo_knowledge(self, repo_name):
        """Extrae conocimiento de un repositorio"""
        repo_path = self.knowledge_dir / repo_name
        lean_files = list(repo_path.rglob("*.lean"))
        
        self.log(f"📚 Extrayendo conocimiento de {repo_name} ({len(lean_files)} archivos)...")
        
        repo_definitions = []
        repo_theorems = []
        repo_patterns = []
        
        for lean_file in lean_files:
            try:
                with open(lean_file, 'r', encoding='utf-8') as f:
                    content = f.read()
                
                # Extraer elementos
                definitions = self.extract_definitions(content)
                theorems = self.extract_theorems(content)
                patterns = self.extract_proof_patterns(content)
                
                # Añadir metadatos de repositorio
                for d in definitions:
                    d["repo"] = repo_name
                    d["file"] = str(lean_file.relative_to(repo_path))
                
                for t in theorems:
                    t["repo"] = repo_name
                    t["file"] = str(lean_file.relative_to(repo_path))
                
                for p in patterns:
                    p["repo"] = repo_name
                    p["file"] = str(lean_file.relative_to(repo_path))
                
                repo_definitions.extend(definitions)
                repo_theorems.extend(theorems)
                repo_patterns.extend(patterns)
                
            except Exception as e:
                self.log(f"⚠️ Error procesando {lean_file}: {e}", "WARNING")
        
        self.log(f"  - Definiciones: {len(repo_definitions)}")
        self.log(f"  - Teoremas: {len(repo_theorems)}")
        self.log(f"  - Patrones de prueba: {len(repo_patterns)}")
        
        return repo_definitions, repo_theorems, repo_patterns
    
    def sync_all_repos(self):
        """Sincroniza todos los repositorios configurados"""
        self.log("🌐 NOESIS CEREBRAL V2.0 - Iniciando sincronización de repositorios...")
        
        for repo in self.config["repositories"]:
            repo_name = repo["name"]
            repo_url = repo["url"]
            branch = repo.get("branch", "main")
            
            success = self.sync_repo(repo_url, repo_name, branch)
            
            if success:
                # Extraer conocimiento
                definitions, theorems, patterns = self.extract_repo_knowledge(repo_name)
                
                self.knowledge["definitions"].extend(definitions)
                self.knowledge["theorems"].extend(theorems)
                self.knowledge["proof_patterns"].extend(patterns)
                self.knowledge["repos_synced"].append(repo_name)
        
        self.log(f"✅ Sincronización completa:")
        self.log(f"   - Repositorios: {len(self.knowledge['repos_synced'])}")
        self.log(f"   - Definiciones: {len(self.knowledge['definitions'])}")
        self.log(f"   - Teoremas: {len(self.knowledge['theorems'])}")
        self.log(f"   - Patrones: {len(self.knowledge['proof_patterns'])}")
    
    def save_knowledge(self):
        """Guarda la base de conocimiento"""
        # Guardar en pickle (formato eficiente)
        pkl_file = self.knowledge_dir / 'knowledge_v2.pkl'
        with open(pkl_file, 'wb') as f:
            pickle.dump(self.knowledge, f)
        
        # Guardar resumen en JSON (legible)
        json_file = self.knowledge_dir / 'knowledge_v2.json'
        summary = {
            "timestamp": datetime.now().isoformat(),
            "repos_synced": self.knowledge["repos_synced"],
            "total_definitions": len(self.knowledge["definitions"]),
            "total_theorems": len(self.knowledge["theorems"]),
            "total_patterns": len(self.knowledge["proof_patterns"])
        }
        with open(json_file, 'w') as f:
            json.dump(summary, f, indent=2)
        
        self.log(f"💾 Conocimiento guardado en {self.knowledge_dir}")
    
    def generate_report(self):
        """Genera reporte de sincronización"""
        report = {
            "timestamp": datetime.now().isoformat(),
            "version": "NOESIS CEREBRAL V2.0",
            "knowledge_base": {
                "location": str(self.knowledge_dir),
                "repos_synced": self.knowledge["repos_synced"],
                "total_items": len(self.knowledge["definitions"]) + 
                              len(self.knowledge["theorems"]) + 
                              len(self.knowledge["proof_patterns"]),
                "definitions": len(self.knowledge["definitions"]),
                "theorems": len(self.knowledge["theorems"]),
                "proof_patterns": len(self.knowledge["proof_patterns"])
            }
        }
        
        report_file = Path('noesis_sync_report.json')
        with open(report_file, 'w') as f:
            json.dump(report, f, indent=2)
        
        self.log(f"📊 Reporte generado: {report_file}")
        
        return report

def main():
    """Función principal"""
    if len(sys.argv) < 2:
        print("Uso: noesis_orchestrator.py <config.json>")
        sys.exit(1)
    
    config_path = Path(sys.argv[1])
    
    if not config_path.exists():
        print(f"❌ Error: Archivo de configuración {config_path} no existe")
        sys.exit(1)
    
    orchestrator = NoesisOrchestrator(config_path)
    orchestrator.sync_all_repos()
    orchestrator.save_knowledge()
    report = orchestrator.generate_report()
    
    print(f"\n✅ NOESIS CEREBRAL V2.0 - Sincronización completa")
    print(f"   Repositorios: {len(report['knowledge_base']['repos_synced'])}")
    print(f"   Total items: {report['knowledge_base']['total_items']}")

if __name__ == "__main__":
    main()
