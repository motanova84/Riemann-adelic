#!/usr/bin/env python3
"""
🍽️ NOESIS DIGESTIVE SYSTEM - ORQUESTADOR MAESTRO
Ejecuta el ciclo digestivo completo
"""

import sys
import subprocess
from pathlib import Path
from datetime import datetime

class DigestiveOrchestrator:
    def __init__(self):
        self.repo_root = Path(__file__).parent.parent.parent
        self.scripts_dir = Path(__file__).parent
        
    def run_phase(self, phase_name, script_name):
        """Ejecuta una fase del sistema digestivo"""
        print(f"\n{'='*80}")
        print(f"🍽️ FASE: {phase_name}")
        print(f"{'='*80}\n")
        
        script_path = self.scripts_dir / script_name
        try:
            result = subprocess.run(
                [sys.executable, str(script_path)],
                cwd=self.repo_root,
                capture_output=True,
                text=True,
                timeout=300
            )
            
            print(result.stdout)
            if result.stderr:
                print("Errores:", result.stderr)
            
            return result.returncode == 0
        except subprocess.TimeoutExpired:
            print(f"⚠️ TIMEOUT: La fase {phase_name} excedió el tiempo límite")
            return False
        except Exception as e:
            print(f"❌ ERROR: {e}")
            return False
    
    def run_full_cycle(self):
        """Ejecuta el ciclo digestivo completo"""
        print("""
╔══════════════════════════════════════════════════════════════════════════╗
║                                                                          ║
║              🍽️ NOESIS DIGESTIVE SYSTEM - CICLO COMPLETO               ║
║                                                                          ║
║         "El organismo VIVE, RESPIRA y CRECE"                            ║
║                                                                          ║
║         Frecuencia base: 141.7001 Hz                                    ║
║         Fecha: """ + datetime.now().isoformat() + """                    ║
║                                                                          ║
╚══════════════════════════════════════════════════════════════════════════╝
""")
        
        phases = [
            ("1️⃣ HAMBRE - Detección de Necesidad", "digestive_hunger.py"),
            ("2️⃣ INGESTA - Selección de Alimento", "digestive_ingestion.py"),
            ("3️⃣ DIGESTIÓN - Procesamiento", "digestive_digestion.py"),
            ("4️⃣ ASIMILACIÓN - Aprendizaje", "digestive_assimilation.py"),
            ("5️⃣ EXCRECIÓN - Limpieza", "digestive_excretion.py"),
        ]
        
        results = []
        for phase_name, script_name in phases:
            success = self.run_phase(phase_name, script_name)
            results.append((phase_name, success))
            
            if not success:
                print(f"\n⚠️ La fase {phase_name} falló. Continuando con el siguiente paso...")
        
        # Resumen final
        print(f"\n{'='*80}")
        print("📊 RESUMEN DEL CICLO DIGESTIVO")
        print(f"{'='*80}\n")
        
        for phase_name, success in results:
            status = "✅" if success else "❌"
            print(f"{status} {phase_name}")
        
        total_success = sum(1 for _, success in results if success)
        print(f"\n🎯 Fases completadas: {total_success}/{len(phases)}")
        
        if total_success == len(phases):
            print("\n✅ 🎉 CICLO DIGESTIVO COMPLETO - EL ORGANISMO HA CRECIDO 🎉 ✅")
        elif total_success >= 3:
            print("\n⚠️ CICLO PARCIALMENTE COMPLETO - EL ORGANISMO SOBREVIVE ⚠️")
        else:
            print("\n❌ CICLO INCOMPLETO - EL ORGANISMO NECESITA ATENCIÓN ❌")
        
        print(f"\n{'='*80}\n")
        
        return total_success == len(phases)

if __name__ == "__main__":
    orchestrator = DigestiveOrchestrator()
    success = orchestrator.run_full_cycle()
    sys.exit(0 if success else 1)
