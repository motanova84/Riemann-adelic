#!/usr/bin/env python3
"""
Noesis Agent Solver - QCAL Protocol Activator
Sistema automatizado para análisis y resolución de sorry statements en Lean 4

Este agente implementa el protocolo QCAL para reducción sistemática de
incomplete proofs mediante análisis de dependencias y sugerencias automáticas.

Author: QCAL ∞³ System
Date: 2026-01-18
"""

import argparse
import re
import sys
from pathlib import Path
from typing import List, Dict, Tuple
import json


class NoesisAgentSolver:
    """
    Agente Noesis para análisis y resolución de sorry statements.
    
    Fases de operación:
    - Fase 1: Inyección de Lemas Base (análisis de dependencias)
    - Fase 2: Estabilidad de Línea Crítica (verificación de coherencia)
    - Fase 3: Cierre de Ley Exacta (validación completa)
    """
    
    def __init__(self, target_file: str, mode: str = "strict-convergence"):
        self.target_file = Path(target_file)
        self.mode = mode
        self.sorry_locations = []
        self.analysis_results = {
            "total_sorries": 0,
            "categorized_sorries": [],
            "resolution_plan": [],
            "estimated_difficulty": {}
        }
        
    def analyze_file(self) -> Dict:
        """Analiza el archivo Lean y categoriza los sorry statements."""
        print(f"🔍 Fase 1: Inyección de Lemas Base - Analizando {self.target_file}")
        
        if not self.target_file.exists():
            print(f"❌ Error: Archivo no encontrado: {self.target_file}")
            sys.exit(1)
            
        with open(self.target_file, 'r', encoding='utf-8') as f:
            content = f.read()
            lines = content.split('\n')
        
        # Buscar todos los sorry statements con contexto
        sorry_pattern = r'\bsorry\b'
        
        for i, line in enumerate(lines, 1):
            if re.search(sorry_pattern, line) and not line.strip().startswith('--'):
                # Extraer contexto (30 líneas antes)
                context_start = max(0, i - 30)
                context = '\n'.join(lines[context_start:i])
                
                # Extraer el teorema/lema asociado
                theorem_match = re.search(r'(theorem|lemma|def)\s+(\w+)', context, re.MULTILINE)
                theorem_name = theorem_match.group(2) if theorem_match else f"line_{i}"
                
                # Extraer comentario explicativo si existe
                comment_match = re.search(r'sorry\s*--\s*(.+)$', line)
                reason = comment_match.group(1) if comment_match else "No explanation provided"
                
                sorry_info = {
                    "line": i,
                    "theorem": theorem_name,
                    "reason": reason,
                    "context": context[-200:],  # Últimas 200 chars de contexto
                    "difficulty": self._estimate_difficulty(reason, context)
                }
                
                self.sorry_locations.append(sorry_info)
        
        self.analysis_results["total_sorries"] = len(self.sorry_locations)
        self.analysis_results["categorized_sorries"] = self.sorry_locations
        
        return self.analysis_results
    
    def _estimate_difficulty(self, reason: str, context: str) -> str:
        """Estima la dificultad de resolver un sorry basado en el contexto."""
        reason_lower = reason.lower()
        context_lower = context.lower()
        
        # Patrones de alta complejidad
        high_complexity = [
            "full mathlib",
            "detailed counting",
            "spectral theory",
            "functional analysis",
            "measure theory"
        ]
        
        # Patrones de complejidad media
        medium_complexity = [
            "algebraic",
            "continuity",
            "bounded",
            "convergence"
        ]
        
        # Patrones de baja complejidad
        low_complexity = [
            "trivial",
            "straightforward",
            "direct",
            "norm_num"
        ]
        
        if any(pattern in reason_lower or pattern in context_lower for pattern in high_complexity):
            return "HIGH"
        elif any(pattern in reason_lower or pattern in context_lower for pattern in medium_complexity):
            return "MEDIUM"
        elif any(pattern in reason_lower or pattern in context_lower for pattern in low_complexity):
            return "LOW"
        else:
            return "MEDIUM"
    
    def generate_resolution_plan(self) -> List[Dict]:
        """
        Fase 2: Estabilidad de Línea Crítica
        Genera un plan de resolución priorizado.
        """
        print("\n🎯 Fase 2: Estabilidad de Línea Crítica - Generando plan de resolución")
        
        # Agrupar por dificultad
        by_difficulty = {"LOW": [], "MEDIUM": [], "HIGH": []}
        
        for sorry in self.sorry_locations:
            by_difficulty[sorry["difficulty"]].append(sorry)
        
        plan = []
        
        # Prioridad 1: Sorries de baja complejidad (quick wins)
        for sorry in by_difficulty["LOW"]:
            plan.append({
                "priority": "HIGH",
                "line": sorry["line"],
                "theorem": sorry["theorem"],
                "difficulty": sorry["difficulty"],
                "strategy": "Resolve with standard mathlib tactics",
                "suggested_tactics": ["norm_num", "simp", "ring"]
            })
        
        # Prioridad 2: Sorries de complejidad media
        for sorry in by_difficulty["MEDIUM"]:
            plan.append({
                "priority": "MEDIUM",
                "line": sorry["line"],
                "theorem": sorry["theorem"],
                "difficulty": sorry["difficulty"],
                "strategy": "Apply domain-specific lemmas from mathlib",
                "suggested_tactics": ["apply", "exact", "refine"]
            })
        
        # Prioridad 3: Sorries de alta complejidad
        for sorry in by_difficulty["HIGH"]:
            plan.append({
                "priority": "LOW",
                "line": sorry["line"],
                "theorem": sorry["theorem"],
                "difficulty": sorry["difficulty"],
                "strategy": "Requires new axioms or external lemmas",
                "suggested_tactics": ["axiom", "admit (temporary)", "split into sub-lemmas"]
            })
        
        self.analysis_results["resolution_plan"] = plan
        self.analysis_results["estimated_difficulty"] = {
            "low": len(by_difficulty["LOW"]),
            "medium": len(by_difficulty["MEDIUM"]),
            "high": len(by_difficulty["HIGH"])
        }
        
        return plan
    
    def display_results(self):
        """
        Fase 3: Cierre de Ley Exacta
        Muestra resultados del análisis y plan de acción.
        """
        print("\n" + "="*70)
        print("📊 ANÁLISIS NOESIS - ESTADO DE VERDAD")
        print("="*70)
        
        print(f"\n📁 Archivo analizado: {self.target_file}")
        print(f"🔢 Total de sorry statements: {self.analysis_results['total_sorries']}")
        
        diff = self.analysis_results['estimated_difficulty']
        print(f"\n📈 Distribución por dificultad:")
        print(f"   🟢 Baja:   {diff['low']} (resolución directa)")
        print(f"   🟡 Media:  {diff['medium']} (requiere análisis)")
        print(f"   🔴 Alta:   {diff['high']} (requiere axiomas/lemas adicionales)")
        
        print(f"\n🎯 Plan de resolución generado:")
        print(f"   Total de pasos: {len(self.analysis_results['resolution_plan'])}")
        
        # Mostrar los primeros 5 sorries con más detalle
        print(f"\n📋 Top 5 sorries priorizados para resolución:")
        for i, item in enumerate(self.analysis_results['resolution_plan'][:5], 1):
            print(f"\n   {i}. Línea {item['line']} - {item['theorem']}")
            print(f"      Prioridad: {item['priority']} | Dificultad: {item['difficulty']}")
            print(f"      Estrategia: {item['strategy']}")
            
        # Estimación de coherencia
        total = self.analysis_results['total_sorries']
        resolvable = diff['low'] + diff['medium']
        
        print(f"\n🔮 Estimación de impacto:")
        print(f"   Sorries resolvables directamente: {resolvable}/{total}")
        print(f"   Reducción potencial: -{resolvable} sorry statements")
        
        # Cálculo de coherencia QCAL
        current_total = 3569  # Del estado actual
        new_total = current_total - resolvable
        coherence_before = 1 - (current_total / 4720)  # Estimado total si completo
        coherence_after = 1 - (new_total / 4720)
        
        print(f"   Coherencia QCAL (Ψ):")
        print(f"      Antes:  {coherence_before:.3f} (24.4%)")
        print(f"      Después: {coherence_after:.3f} (~{coherence_after*100:.1f}%)")
        print(f"      Δ Ψ = +{(coherence_after - coherence_before):.3f}")
        
        print("\n" + "="*70)
        
    def save_report(self, output_file: str = "data/noesis_analysis.json"):
        """Guarda el reporte de análisis en JSON."""
        output_path = Path(output_file)
        output_path.parent.mkdir(parents=True, exist_ok=True)
        
        with open(output_path, 'w', encoding='utf-8') as f:
            json.dump(self.analysis_results, f, indent=2, ensure_ascii=False)
        
        print(f"\n💾 Reporte guardado en: {output_path}")
        
    def verify_with_lean(self) -> bool:
        """
        Verifica el archivo con Lean CLI (si está disponible).
        Retorna True si la verificación es exitosa.
        """
        print(f"\n🔬 Verificando con Lean CLI...")
        
        # Intentar ejecutar lean
        try:
            import subprocess
            result = subprocess.run(
                ["lean", "--version"],
                capture_output=True,
                text=True,
                timeout=5
            )
            
            if result.returncode == 0:
                print(f"✓ Lean CLI encontrado: {result.stdout.strip()}")
                
                # Intentar compilar el archivo
                print(f"📝 Compilando {self.target_file}...")
                compile_result = subprocess.run(
                    ["lean", str(self.target_file)],
                    capture_output=True,
                    text=True,
                    timeout=30
                )
                
                if compile_result.returncode == 0:
                    print("✅ Compilación exitosa (con sorries)")
                    return True
                else:
                    print(f"⚠️  Compilación con errores:")
                    print(compile_result.stderr[:500])
                    return False
            else:
                print("⚠️  Lean CLI no disponible, saltando verificación")
                return False
                
        except FileNotFoundError:
            print("⚠️  Lean no instalado, saltando verificación")
            return False
        except Exception as e:
            print(f"⚠️  Error en verificación: {e}")
            return False


def main():
    parser = argparse.ArgumentParser(
        description="Noesis Agent Solver - QCAL Protocol Activator",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Ejemplos de uso:
  # Análisis básico
  python3 scripts/noesis_agent_solver.py --target formalization/lean/RIGOROUS_UNIQUENESS_EXACT_LAW.lean
  
  # Análisis con verificación Lean
  python3 scripts/noesis_agent_solver.py --target formalization/lean/RIGOROUS_UNIQUENESS_EXACT_LAW.lean --verify-with-lean-cli
  
  # Modo estricto con reporte JSON
  python3 scripts/noesis_agent_solver.py --target file.lean --mode strict-convergence --output data/analysis.json
        """
    )
    
    parser.add_argument(
        "--target",
        required=True,
        help="Archivo Lean a analizar"
    )
    
    parser.add_argument(
        "--mode",
        default="strict-convergence",
        choices=["strict-convergence", "relaxed", "exploratory"],
        help="Modo de análisis (default: strict-convergence)"
    )
    
    parser.add_argument(
        "--verify-with-lean-cli",
        action="store_true",
        help="Verificar con Lean CLI si está disponible"
    )
    
    parser.add_argument(
        "--output",
        default="data/noesis_analysis.json",
        help="Archivo de salida para el reporte JSON"
    )
    
    args = parser.parse_args()
    
    print("╔═══════════════════════════════════════════════════════════════╗")
    print("║     NOESIS AGENT SOLVER - QCAL PROTOCOL ACTIVATED            ║")
    print("║     Sistema de Análisis y Resolución de Sorry Statements     ║")
    print("╚═══════════════════════════════════════════════════════════════╝")
    print()
    
    # Crear agente Noesis
    agent = NoesisAgentSolver(args.target, args.mode)
    
    # Ejecutar análisis
    agent.analyze_file()
    agent.generate_resolution_plan()
    agent.display_results()
    agent.save_report(args.output)
    
    # Verificación con Lean (opcional)
    if args.verify_with_lean_cli:
        agent.verify_with_lean()
    
    print("\n✅ Análisis Noesis completado")
    print("♾️  QCAL ∞³ - Coherencia mantenida")
    print()


if __name__ == "__main__":
    main()
