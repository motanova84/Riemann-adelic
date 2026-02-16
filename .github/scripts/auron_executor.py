#!/usr/bin/env python3
"""
AURON EXECUTOR - Aplicador Universal de Resoluciones Operacionales Noéticas
Ejecuta transformaciones para eliminar sorrys basándose en el análisis de AMDA.

Autor: José Manuel Mota Burruezo (JMMB Ψ✧)
Fecha: 16 febrero 2026
DOI: 10.5281/zenodo.17379721
"""

import json
import re
import sys
import shutil
import subprocess
from pathlib import Path
from datetime import datetime
import argparse


class AuronExecutor:
    """Ejecutor de transformaciones para eliminar sorrys."""
    
    # Estrategias de eliminación por categoría
    STRATEGIES = {
        'trivial': ['rfl', 'trivial', 'exact rfl'],
        'library_search': ['simp', 'simp_all', 'omega'],
        'simplification': ['simp', 'simp_all', 'simp [*]'],
        'unknown': []  # Requiere análisis manual
    }
    
    def __init__(self, repo_root, cross_repo=False, dry_run=False):
        self.repo_root = Path(repo_root)
        self.cross_repo = cross_repo
        self.dry_run = dry_run
        self.formalization_dir = self.repo_root / 'formalization' / 'lean'
        self.backup_dir = self.repo_root / '.auron_backups' / datetime.now().strftime('%Y%m%d_%H%M%S')
        self.backup_dir.mkdir(parents=True, exist_ok=True)
        
        self.success_count = 0
        self.failure_count = 0
        self.transformations = []
        
    def log(self, message, level="INFO"):
        """Log mensaje a consola."""
        print(f"[{level}] {message}")
    
    def backup_file(self, filepath):
        """Crea un backup del archivo antes de modificarlo."""
        backup_path = self.backup_dir / filepath.relative_to(self.repo_root)
        backup_path.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(filepath, backup_path)
        return backup_path
    
    def apply_simple_strategy(self, filepath, line_num, category):
        """Aplica una estrategia simple de eliminación de sorry."""
        strategies = self.STRATEGIES.get(category, [])
        
        if not strategies:
            self.log(f"⏭️  Sin estrategia para categoría {category}", level="WARN")
            return False
        
        # Leer archivo
        with open(filepath, 'r', encoding='utf-8') as f:
            lines = f.read().split('\n')
        
        # Verificar que la línea contiene sorry
        if line_num > len(lines) or 'sorry' not in lines[line_num - 1]:
            self.log(f"⚠️  Sorry no encontrado en {filepath}:{line_num}", level="WARN")
            return False
        
        original_line = lines[line_num - 1]
        
        # Probar cada estrategia
        for strategy in strategies:
            if self.dry_run:
                self.log(f"🔍 [DRY-RUN] Probaría reemplazar 'sorry' con '{strategy}' en {filepath}:{line_num}")
                self.transformations.append({
                    'file': str(filepath.relative_to(self.repo_root)),
                    'line': line_num,
                    'category': category,
                    'original': original_line.strip(),
                    'proposed': original_line.replace('sorry', strategy).strip(),
                    'status': 'dry_run'
                })
                return True
            
            # Backup
            backup = self.backup_file(filepath)
            
            # Aplicar transformación
            new_line = original_line.replace('sorry', strategy)
            lines[line_num - 1] = new_line
            
            # Guardar
            with open(filepath, 'w', encoding='utf-8') as f:
                f.write('\n'.join(lines))
            
            # Probar compilación
            result = self.test_compilation()
            
            if result:
                self.log(f"✅ Sorry eliminado con '{strategy}' en {filepath}:{line_num}")
                self.success_count += 1
                self.transformations.append({
                    'file': str(filepath.relative_to(self.repo_root)),
                    'line': line_num,
                    'category': category,
                    'original': original_line.strip(),
                    'modified': new_line.strip(),
                    'strategy': strategy,
                    'status': 'success'
                })
                return True
            else:
                # Restaurar backup
                shutil.copy2(backup, filepath)
        
        self.log(f"❌ No se pudo eliminar sorry en {filepath}:{line_num}", level="WARN")
        self.failure_count += 1
        return False
    
    def apply_cross_repo_knowledge(self, filepath, line_num, cross_repo_hint):
        """Aplica conocimiento extraído de otros repositorios."""
        if not cross_repo_hint.get('cross_repo_hint'):
            return False
        
        source_repo = cross_repo_hint['source_repo']
        suggested_pattern = cross_repo_hint['suggested_pattern']
        
        self.log(f"🔗 Aplicando conocimiento de {source_repo}")
        
        # Intentar extraer la prueba completa
        proof_pattern = re.search(r'(by\s+.*?)(?=\n\s*\n|\Z)', suggested_pattern, re.DOTALL)
        
        if not proof_pattern:
            return False
        
        proof = proof_pattern.group(1).strip()
        
        # Leer archivo
        with open(filepath, 'r', encoding='utf-8') as f:
            lines = f.read().split('\n')
        
        if line_num > len(lines) or 'sorry' not in lines[line_num - 1]:
            return False
        
        original_line = lines[line_num - 1]
        
        if self.dry_run:
            self.log(f"🔍 [DRY-RUN] Probaría aplicar patrón de {source_repo} en {filepath}:{line_num}")
            self.transformations.append({
                'file': str(filepath.relative_to(self.repo_root)),
                'line': line_num,
                'source_repo': source_repo,
                'original': original_line.strip(),
                'proposed': original_line.replace('sorry', proof).strip(),
                'status': 'dry_run'
            })
            return True
        
        # Backup
        backup = self.backup_file(filepath)
        
        # Aplicar transformación
        new_line = original_line.replace('sorry', proof)
        lines[line_num - 1] = new_line
        
        # Guardar
        with open(filepath, 'w', encoding='utf-8') as f:
            f.write('\n'.join(lines))
        
        # Probar compilación
        result = self.test_compilation()
        
        if result:
            self.log(f"✅ Sorry eliminado con patrón de {source_repo} en {filepath}:{line_num}")
            self.success_count += 1
            self.transformations.append({
                'file': str(filepath.relative_to(self.repo_root)),
                'line': line_num,
                'source_repo': source_repo,
                'original': original_line.strip(),
                'modified': new_line.strip(),
                'status': 'success'
            })
            return True
        else:
            # Restaurar backup
            shutil.copy2(backup, filepath)
            return False
    
    def test_compilation(self):
        """Prueba la compilación de Lean."""
        # Por ahora, solo simular éxito en modo dry-run
        # En producción, ejecutaría: lake build
        if self.dry_run:
            return True
        
        # Compilación real (comentada para evitar timeouts en CI)
        # result = subprocess.run(
        #     "cd formalization/lean && lake build",
        #     shell=True,
        #     capture_output=True,
        #     text=True,
        #     timeout=300
        # )
        # return result.returncode == 0
        
        # Por seguridad, retornar False en modo producción sin compilador
        self.log("⚠️  Compilación Lean no disponible, asumiendo fallo", level="WARN")
        return False
    
    def execute_transformations(self, amda_report_file):
        """Ejecuta las transformaciones basadas en el reporte de AMDA."""
        self.log("⚡ AURON EXECUTOR - Iniciando transformaciones...")
        
        # Cargar reporte AMDA
        with open(amda_report_file, 'r') as f:
            report = json.load(f)
        
        sorrys = report['sorrys']
        self.log(f"📋 Procesando {len(sorrys)} sorrys...")
        
        # Procesar sólo los primeros 10 en modo seguro
        max_to_process = 10 if not self.dry_run else len(sorrys)
        
        for sorry in sorrys[:max_to_process]:
            filepath = self.repo_root / sorry['file']
            line_num = sorry['line']
            category = sorry['category']
            cross_repo_hint = sorry.get('cross_repo_hint', {})
            
            # Priorizar conocimiento cross-repo
            if self.cross_repo and cross_repo_hint.get('cross_repo_hint'):
                success = self.apply_cross_repo_knowledge(filepath, line_num, cross_repo_hint)
                if success:
                    continue
            
            # Aplicar estrategia simple
            self.apply_simple_strategy(filepath, line_num, category)
        
        self.log(f"\n📊 Resumen de ejecución:")
        self.log(f"   ✅ Exitosas: {self.success_count}")
        self.log(f"   ❌ Fallidas: {self.failure_count}")
        self.log(f"   📁 Backups en: {self.backup_dir}")
    
    def save_changes_report(self, output_file):
        """Guarda el reporte de cambios realizados."""
        report = {
            'timestamp': datetime.now().isoformat(),
            'dry_run': self.dry_run,
            'cross_repo_enabled': self.cross_repo,
            'success_count': self.success_count,
            'failure_count': self.failure_count,
            'backup_dir': str(self.backup_dir),
            'transformations': self.transformations
        }
        
        output_path = self.repo_root / output_file
        with open(output_path, 'w') as f:
            json.dump(report, f, indent=2)
        
        self.log(f"✅ Reporte de cambios guardado en {output_path}")
        return output_path


def main():
    """Punto de entrada principal."""
    parser = argparse.ArgumentParser(description='AURON Executor - Ejecutor de transformaciones')
    parser.add_argument('--input', required=True,
                        help='Archivo de entrada con el reporte de AMDA')
    parser.add_argument('--cross-repo', action='store_true',
                        help='Habilitar uso de conocimiento cross-repo')
    parser.add_argument('--output', default='auron_changes.json',
                        help='Archivo de salida para el reporte de cambios')
    parser.add_argument('--dry-run', action='store_true',
                        help='Modo de prueba sin aplicar cambios reales')
    
    args = parser.parse_args()
    
    repo_root = Path.cwd()
    executor = AuronExecutor(repo_root, cross_repo=args.cross_repo, dry_run=args.dry_run)
    executor.execute_transformations(args.input)
    executor.save_changes_report(args.output)
    
    return 0


if __name__ == "__main__":
    sys.exit(main())
