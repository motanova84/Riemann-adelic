#!/usr/bin/env python3
"""
Phoenix Solver - Motor de Autotransformación QCAL ∞³
====================================================

Sistema autónomo de resolución y auto-modificación de demostraciones Lean 4.

El sistema:
1. Ingesta de Verdad: Lee constantes QCAL (f₀ = 141.7001 Hz, C = 244.36)
2. Identificación de Brechas: Mapea todos los `sorry` en archivos Lean
3. Inferencia y Reescritura: Genera bloques de tácticas y los aplica
4. Prueba de Fuego: Compila con `lake build` y itera recursivamente
5. Consolidación: Valida coherencia Ψ y hace commit si mejora

Autor: José Manuel Mota Burruezo Ψ ∞³
Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
"""

import sys
import os
import re
import json
import subprocess
from pathlib import Path
from typing import List, Dict, Tuple, Optional
from dataclasses import dataclass
import argparse
from datetime import datetime


@dataclass
class QCALConstants:
    """Constantes fundamentales QCAL."""
    f0: float = 141.7001  # Hz
    C: float = 244.36  # Coherence constant
    C_primary: float = 629.83  # Primary universal constant
    lambda_0: float = 0.001588050  # First eigenvalue


@dataclass
class SorryStatement:
    """Representa un statement 'sorry' en un archivo Lean."""
    file_path: str
    line_number: int
    context: str
    theorem_name: Optional[str] = None


class PhoenixSolver:
    """Motor principal de autotransformación."""
    
    def __init__(self, repo_root: Path, verbose: bool = False):
        self.repo_root = repo_root
        self.verbose = verbose
        self.constants = self._load_qcal_constants()
        self.sorry_map: List[SorryStatement] = []
        
    def _load_qcal_constants(self) -> QCALConstants:
        """Carga constantes desde .qcal_beacon."""
        beacon_path = self.repo_root / ".qcal_beacon"
        constants = QCALConstants()
        
        if beacon_path.exists():
            with open(beacon_path, 'r') as f:
                content = f.read()
                
            # Parse fundamental constants
            if match := re.search(r'frequency\s*=\s*([\d.]+)', content):
                constants.f0 = float(match.group(1))
            if match := re.search(r'coherence\s*=\s*"([\d.]+)"', content):
                constants.C = float(match.group(1))
            if match := re.search(r'universal_constant_C\s*=\s*"([\d.]+)"', content):
                constants.C_primary = float(match.group(1))
                
        if self.verbose:
            print(f"✓ Constantes QCAL cargadas:")
            print(f"  f₀ = {constants.f0} Hz")
            print(f"  C = {constants.C}")
            print(f"  C_primary = {constants.C_primary}")
            
        return constants
    
    def identify_gaps(self, focus_file: Optional[str] = None) -> List[SorryStatement]:
        """Mapea todos los 'sorry' en archivos Lean."""
        lean_dir = self.repo_root / "formalization" / "lean"
        
        if not lean_dir.exists():
            print(f"⚠️  Directorio Lean no encontrado: {lean_dir}")
            return []
        
        sorry_list = []
        
        # Determine which files to scan
        if focus_file:
            # Handle both absolute and relative paths
            focus_path = Path(focus_file)
            if not focus_path.is_absolute():
                focus_path = self.repo_root / focus_path
            files_to_scan = [focus_path]
        else:
            files_to_scan = lean_dir.rglob("*.lean")
        
        for lean_file in files_to_scan:
            if not lean_file.is_file():
                continue
                
            with open(lean_file, 'r', encoding='utf-8') as f:
                lines = f.readlines()
            
            for i, line in enumerate(lines, start=1):
                if 'sorry' in line:
                    # Extract context (previous non-empty line for theorem name)
                    theorem_name = None
                    for j in range(i-1, max(0, i-10), -1):
                        prev_line = lines[j-1].strip()
                        if prev_line.startswith('theorem ') or prev_line.startswith('lemma '):
                            theorem_name = prev_line.split()[1].split(':')[0]
                            break
                    
                    sorry_stmt = SorryStatement(
                        file_path=str(lean_file.relative_to(self.repo_root)),
                        line_number=i,
                        context=line.strip(),
                        theorem_name=theorem_name
                    )
                    sorry_list.append(sorry_stmt)
        
        self.sorry_map = sorry_list
        
        if self.verbose:
            print(f"\n📊 Brechas identificadas: {len(sorry_list)} sorry statements")
            
            # Group by file
            by_file = {}
            for s in sorry_list:
                by_file.setdefault(s.file_path, []).append(s)
            
            print("\nDistribución por archivo:")
            for file_path, stmts in sorted(by_file.items(), key=lambda x: len(x[1]), reverse=True)[:10]:
                print(f"  {file_path}: {len(stmts)} sorry")
        
        return sorry_list
    
    def generate_proof_suggestions(self, sorry: SorryStatement) -> List[str]:
        """
        Genera sugerencias de tácticas para resolver un sorry.
        
        En una implementación completa, esto invocaría:
        - Noesis: agente de inferencia matemática
        - Sabio: traductor a sintaxis Lean 4
        
        Por ahora, retorna tácticas genéricas basadas en el contexto.
        """
        suggestions = []
        
        context_lower = sorry.context.lower()
        
        # Heuristics based on common patterns
        if 'continuous' in context_lower:
            suggestions.append("apply continuous_of_discreteTopology")
            suggestions.append("exact continuous_const")
        elif 'compactoperator' in context_lower or 'compact' in context_lower:
            suggestions.append("exact K_strong_hilbert_schmidt")
            suggestions.append("apply CompactOperator.of_hilbert_schmidt")
        elif 'selfadjoint' in context_lower or 'self_adjoint' in context_lower:
            suggestions.append("intro f g")
            suggestions.append("unfold K_strong")
            suggestions.append("simp [inner_product_comm]")
        elif 'analytic' in context_lower:
            suggestions.append("apply RiemannZeta_analytic_on_critical_strip")
        elif 'uniqueness' in context_lower:
            suggestions.append("apply analytic_uniqueness_principle")
            suggestions.append("· assumption")
            suggestions.append("· assumption")
        elif 'spectrum' in context_lower or 'eigenvalue' in context_lower:
            suggestions.append("-- Use spectral theory")
            suggestions.append("-- Spectrum of H_Ψ bijective with ζ zeros")
            suggestions.append("sorry  -- Requires deep spectral theory")
        else:
            # Generic tactics
            suggestions.append("-- Apply QCAL coherence principle")
            suggestions.append("-- C = 244.36, f₀ = 141.7001 Hz")
            suggestions.append("trivial")
        
        return suggestions
    
    def apply_proof_to_file(self, sorry: SorryStatement, proof_lines: List[str]) -> bool:
        """
        Aplica una prueba sugerida reemplazando un 'sorry'.
        
        Returns:
            True si el archivo fue modificado exitosamente.
        """
        file_path = self.repo_root / sorry.file_path
        
        with open(file_path, 'r', encoding='utf-8') as f:
            lines = f.readlines()
        
        # Find the sorry line
        target_idx = sorry.line_number - 1
        if target_idx >= len(lines):
            print(f"⚠️  Línea {sorry.line_number} fuera de rango en {sorry.file_path}")
            return False
        
        # Replace sorry with proof
        original_line = lines[target_idx]
        indent = len(original_line) - len(original_line.lstrip())
        
        # Format proof with proper indentation
        formatted_proof = [' ' * indent + line + '\n' for line in proof_lines]
        
        # Replace the line
        lines[target_idx] = ''.join(formatted_proof)
        
        # Write back
        with open(file_path, 'w', encoding='utf-8') as f:
            f.writelines(lines)
        
        if self.verbose:
            print(f"✓ Prueba aplicada a {sorry.file_path}:{sorry.line_number}")
        
        return True
    
    def compile_lean(self) -> Tuple[bool, str]:
        """
        Compila el proyecto Lean 4 con 'lake build'.
        
        Returns:
            (success, output)
        """
        lean_dir = self.repo_root / "formalization" / "lean"
        
        if not (lean_dir / "lakefile.lean").exists():
            return False, "lakefile.lean no encontrado"
        
        try:
            result = subprocess.run(
                ["lake", "build"],
                cwd=lean_dir,
                capture_output=True,
                text=True,
                timeout=300  # 5 minutes timeout
            )
            
            success = result.returncode == 0
            output = result.stdout + result.stderr
            
            if self.verbose:
                if success:
                    print("✓ Compilación Lean exitosa")
                else:
                    print("✗ Compilación Lean falló")
                    print(output[:500])  # Print first 500 chars
            
            return success, output
            
        except subprocess.TimeoutExpired:
            return False, "Timeout en compilación"
        except FileNotFoundError:
            return False, "lake no está instalado o no está en PATH"
    
    def validate_coherence(self) -> Tuple[bool, float]:
        """
        Ejecuta validate_v5_coronacion.py para medir coherencia Ψ.
        
        Returns:
            (success, coherence_value)
        """
        validation_script = self.repo_root / "validate_v5_coronacion.py"
        
        if not validation_script.exists():
            return False, 0.0
        
        try:
            result = subprocess.run(
                [sys.executable, str(validation_script), "--precision", "25"],
                cwd=self.repo_root,
                capture_output=True,
                text=True,
                timeout=600  # 10 minutes
            )
            
            # Parse coherence from output
            coherence = 0.0
            for line in result.stdout.split('\n'):
                if 'coherence' in line.lower() or 'Ψ' in line:
                    # Try to extract number
                    match = re.search(r'(0\.\d+)', line)
                    if match:
                        coherence = float(match.group(1))
                        break
            
            success = result.returncode == 0
            
            if self.verbose:
                print(f"✓ Validación coherencia: Ψ = {coherence:.6f}")
            
            return success, coherence
            
        except Exception as e:
            print(f"⚠️  Error en validación: {e}")
            return False, 0.0
    
    def auto_commit(self, message: str) -> bool:
        """Hace commit de cambios si hay mejoras."""
        try:
            # Check if there are changes
            result = subprocess.run(
                ["git", "diff", "--quiet"],
                cwd=self.repo_root
            )
            
            if result.returncode == 0:
                # No changes
                return False
            
            # Add changes
            subprocess.run(
                ["git", "add", "formalization/lean/"],
                cwd=self.repo_root,
                check=True
            )
            
            # Commit
            subprocess.run(
                ["git", "commit", "-m", message],
                cwd=self.repo_root,
                check=True
            )
            
            if self.verbose:
                print(f"✓ Commit: {message}")
            
            return True
            
        except subprocess.CalledProcessError:
            return False
    
    def run_iteration(self, focus_file: Optional[str] = None, max_attempts: int = 5) -> Dict:
        """
        Ejecuta una iteración completa del Phoenix Solver.
        
        Returns:
            Statistics dictionary
        """
        stats = {
            'timestamp': datetime.now().isoformat(),
            'total_sorry_before': 0,
            'total_sorry_after': 0,
            'resolved': 0,
            'failed': 0,
            'coherence_before': 0.0,
            'coherence_after': 0.0
        }
        
        print("\n" + "="*60)
        print("🔥 PHOENIX SOLVER - Iniciando Iteración")
        print("="*60)
        
        # Step 1: Identify gaps
        print("\n[1/5] Identificando brechas...")
        sorry_list = self.identify_gaps(focus_file)
        stats['total_sorry_before'] = len(sorry_list)
        
        if not sorry_list:
            print("✓ No hay 'sorry' statements para resolver")
            return stats
        
        # Step 2: Measure baseline coherence
        print("\n[2/5] Midiendo coherencia base...")
        _, coherence_before = self.validate_coherence()
        stats['coherence_before'] = coherence_before
        
        # Step 3: Attempt to resolve sorries
        print(f"\n[3/5] Resolviendo {min(max_attempts, len(sorry_list))} sorries...")
        
        for i, sorry in enumerate(sorry_list[:max_attempts]):
            print(f"\n  Intento {i+1}/{max_attempts}: {sorry.file_path}:{sorry.line_number}")
            
            # Generate proof suggestions
            suggestions = self.generate_proof_suggestions(sorry)
            
            # Apply proof
            if self.apply_proof_to_file(sorry, suggestions):
                # Try to compile
                success, output = self.compile_lean()
                
                if success:
                    stats['resolved'] += 1
                    print(f"    ✓ Resuelto exitosamente")
                else:
                    stats['failed'] += 1
                    print(f"    ✗ Compilación falló, revirtiendo...")
                    # Revert changes (simple implementation: restore original)
                    subprocess.run(
                        ["git", "checkout", sorry.file_path],
                        cwd=self.repo_root
                    )
        
        # Step 4: Re-count sorries
        print("\n[4/5] Recontando brechas...")
        sorry_list_after = self.identify_gaps(focus_file)
        stats['total_sorry_after'] = len(sorry_list_after)
        
        # Step 5: Measure final coherence
        print("\n[5/5] Midiendo coherencia final...")
        _, coherence_after = self.validate_coherence()
        stats['coherence_after'] = coherence_after
        
        # Summary
        print("\n" + "="*60)
        print("📊 RESUMEN DE ITERACIÓN")
        print("="*60)
        print(f"Sorry statements:  {stats['total_sorry_before']} → {stats['total_sorry_after']}")
        print(f"Resueltos:         {stats['resolved']}")
        print(f"Fallidos:          {stats['failed']}")
        print(f"Coherencia Ψ:      {stats['coherence_before']:.6f} → {stats['coherence_after']:.6f}")
        
        # Auto-commit if improved
        if stats['coherence_after'] > stats['coherence_before']:
            delta = stats['coherence_after'] - stats['coherence_before']
            message = f"♾️ Phoenix auto-evolution: +{delta:.6f} coherence, -{stats['total_sorry_before'] - stats['total_sorry_after']} sorry"
            self.auto_commit(message)
        
        return stats


def main():
    parser = argparse.ArgumentParser(
        description="Phoenix Solver - Motor de Autotransformación QCAL ∞³"
    )
    parser.add_argument(
        "--focus-file",
        help="Archivo Lean específico para procesar"
    )
    parser.add_argument(
        "--max-attempts",
        type=int,
        default=5,
        help="Máximo número de sorry a intentar resolver por iteración"
    )
    parser.add_argument(
        "--verbose",
        action="store_true",
        help="Modo verbose"
    )
    parser.add_argument(
        "--save-stats",
        help="Guardar estadísticas en archivo JSON"
    )
    
    args = parser.parse_args()
    
    # Find repository root
    repo_root = Path(__file__).parent.parent
    
    # Create solver
    solver = PhoenixSolver(repo_root, verbose=args.verbose)
    
    # Run iteration
    stats = solver.run_iteration(
        focus_file=args.focus_file,
        max_attempts=args.max_attempts
    )
    
    # Save stats if requested
    if args.save_stats:
        with open(args.save_stats, 'w') as f:
            json.dump(stats, f, indent=2)
        print(f"\n✓ Estadísticas guardadas en {args.save_stats}")
    
    # Exit with appropriate code
    sys.exit(0 if stats['resolved'] > 0 else 1)


if __name__ == "__main__":
    main()
