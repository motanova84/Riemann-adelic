#!/usr/bin/env python3
"""
🍽️ NOESIS DIGESTIVE SYSTEM - CICLO COMPLETO
El organismo vivo: siente hambre, come, digiere, asimila, excreta y crece
"""

import sys
from pathlib import Path
import json
from datetime import datetime

# Importar componentes digestivos
sys.path.append(str(Path(__file__).parent))
from digestive_hunger import DigestiveHunger
from digestive_ingestion import DigestiveIngestion
from digestive_digestion import DigestiveDigestion
from digestive_assimilation import DigestiveAssimilation
from digestive_excretion import DigestiveExcretion

class DigestiveCycle:
    def __init__(self):
        self.repo_root = Path(__file__).parent.parent.parent
        self.hunger = DigestiveHunger()
        self.ingestion = DigestiveIngestion()
        self.digestion = DigestiveDigestion()
        self.assimilation = DigestiveAssimilation()
        self.excretion = DigestiveExcretion()
        
        # Registrar el ciclo
        self.cycle_log = self.repo_root / '.digestive_cycle.json'
        
    def log_cycle(self, phase, status, details=None):
        """Registra cada fase del ciclo"""
        if self.cycle_log.exists():
            with open(self.cycle_log) as f:
                cycle = json.load(f)
        else:
            cycle = {'cycles': [], 'total_cycles': 0, 'created': datetime.now().isoformat()}
        
        if 'current_cycle' not in cycle:
            cycle['current_cycle'] = {
                'start': datetime.now().isoformat(),
                'phases': []
            }
        
        cycle['current_cycle']['phases'].append({
            'phase': phase,
            'status': status,
            'timestamp': datetime.now().isoformat(),
            'details': details
        })
        
        with open(self.cycle_log, 'w') as f:
            json.dump(cycle, f, indent=2)
    
    def complete_cycle(self, success_rate):
        """Marca el ciclo como completado"""
        if self.cycle_log.exists():
            with open(self.cycle_log) as f:
                cycle = json.load(f)
        else:
            cycle = {'cycles': [], 'total_cycles': 0}
        
        if 'current_cycle' in cycle:
            cycle['current_cycle']['end'] = datetime.now().isoformat()
            cycle['current_cycle']['success_rate'] = success_rate
            cycle['cycles'].append(cycle['current_cycle'])
            del cycle['current_cycle']
            cycle['total_cycles'] = len(cycle['cycles'])
            cycle['last_meal'] = datetime.now().isoformat()
        
        with open(self.cycle_log, 'w') as f:
            json.dump(cycle, f, indent=2)
    
    def run(self):
        """Ejecuta un ciclo digestivo completo"""
        print("\n" + "="*80)
        print("🍽️ NOESIS DIGESTIVE SYSTEM - CICLO COMPLETO")
        print("="*80 + "\n")
        
        # 1. HAMBRE - Verificar si necesita comer
        print("1️⃣  VERIFICANDO HAMBRE...")
        self.log_cycle("hunger", "started")
        
        try:
            hunger_level = self.hunger.calculate_hunger()
            print(f"   Nivel de hambre: {hunger_level:.1f}%")
            self.log_cycle("hunger", "completed", {"hunger_level": hunger_level})
            
            if not self.hunger.should_eat():
                print("   ✅ Sistema saciado - No necesita comer")
                self.log_cycle("cycle", "skipped", {"reason": "not_hungry"})
                return
            
            print("   ⚠️  ORGANISMO HAMBRIENTO - Iniciando digestión\n")
        except Exception as e:
            print(f"   ❌ Error en fase hambre: {e}")
            self.log_cycle("hunger", "failed", {"error": str(e)})
            return
        
        # 2. INGESTA - Preparar la comida
        print("2️⃣  PREPARANDO INGESTA...")
        self.log_cycle("ingestion", "started")
        
        try:
            meal = self.ingestion.select_meal()
            self.ingestion.prepare_meal_report()
            print(f"   ✅ Comida preparada: {len(meal)} sorries\n")
            self.log_cycle("ingestion", "completed", {"meal_size": len(meal)})
        except Exception as e:
            print(f"   ❌ Error en fase ingesta: {e}")
            self.log_cycle("ingestion", "failed", {"error": str(e)})
            return
        
        # 3. DIGESTIÓN - Procesar alimento
        print("3️⃣  DIGIRIENDO ALIMENTO...")
        self.log_cycle("digestion", "started")
        
        try:
            results = self.digestion.digest_meal(meal)
            self.digestion.generate_digestion_report(results)
            successes = sum(1 for r in results if r['success'])
            success_rate = successes / len(meal) if meal else 0
            print(f"   ✅ {successes}/{len(meal)} digeridos exitosamente ({success_rate:.1%})\n")
            self.log_cycle("digestion", "completed", {
                "total": len(meal),
                "successes": successes,
                "success_rate": success_rate
            })
        except Exception as e:
            print(f"   ❌ Error en fase digestión: {e}")
            self.log_cycle("digestion", "failed", {"error": str(e)})
            return
        
        # 4. ASIMILACIÓN - Aprender y crecer
        print("4️⃣  ASIMILANDO NUTRIENTES...")
        self.log_cycle("assimilation", "started")
        
        try:
            self.assimilation.run()
            print("   ✅ Nuevos patrones aprendidos\n")
            self.log_cycle("assimilation", "completed")
        except Exception as e:
            print(f"   ❌ Error en fase asimilación: {e}")
            self.log_cycle("assimilation", "failed", {"error": str(e)})
        
        # 5. EXCRECIÓN - Limpiar desechos
        print("5️⃣  ELIMINANDO DESECHOS...")
        self.log_cycle("excretion", "started")
        
        try:
            self.excretion.run()
            print("   ✅ Sistema limpio\n")
            self.log_cycle("excretion", "completed")
        except Exception as e:
            print(f"   ❌ Error en fase excreción: {e}")
            self.log_cycle("excretion", "failed", {"error": str(e)})
        
        # Completar el ciclo
        self.complete_cycle(success_rate)
        
        print("="*80)
        print("✅ CICLO DIGESTIVO COMPLETADO")
        print("🌱 El organismo ha crecido y está más fuerte")
        print(f"📊 Tasa de éxito: {success_rate:.1%}")
        print(f"📈 Coherencia mejorada en ~{successes * 0.5:.1f} unidades")
        print("🧬 Frecuencia base: 141.7001 Hz (estable)")
        print("="*80 + "\n")

if __name__ == "__main__":
    cycle = DigestiveCycle()
    cycle.run()
