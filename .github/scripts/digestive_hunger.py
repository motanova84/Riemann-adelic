#!/usr/bin/env python3
"""
🍽️ NOESIS DIGESTIVE SYSTEM - HAMBRE
Detecta cuándo el organismo necesita alimentarse
"""

import json
import subprocess
from pathlib import Path
from datetime import datetime, timedelta

class DigestiveHunger:
    def __init__(self):
        self.repo_root = Path(__file__).parent.parent.parent
        self.hunger_level = 0
        self.hunger_threshold = 70  # Nivel de hambre para activar digestión
        
    def count_sorries(self):
        """Cuenta sorries - principal indicador de hambre"""
        try:
            result = subprocess.run(
                ["grep", "-r", "sorry", "--include=*.lean", "formalization/lean/"],
                cwd=self.repo_root,
                capture_output=True, 
                text=True
            )
            return len(result.stdout.splitlines())
        except Exception as e:
            print(f"Error contando sorries: {e}")
            return 0
    
    def measure_coherence(self):
        """Mide la coherencia del sistema"""
        # Coherencia = 1 - (sorries / total_teoremas)
        total_theorems = self.count_theorems()
        sorries = self.count_sorries()
        if total_theorems == 0:
            return 0
        return 1 - (sorries / total_theorems)
    
    def count_theorems(self):
        """Cuenta teoremas en archivos Lean"""
        try:
            result = subprocess.run(
                ["grep", "-r", "theorem", "--include=*.lean", "formalization/lean/"],
                cwd=self.repo_root,
                capture_output=True, 
                text=True
            )
            return len(result.stdout.splitlines())
        except Exception as e:
            print(f"Error contando teoremas: {e}")
            return 0
    
    def check_last_meal(self):
        """Verifica cuándo fue la última digestión"""
        log_file = self.repo_root / '.digestive_log.json'
        if log_file.exists():
            try:
                with open(log_file) as f:
                    data = json.load(f)
                    last_meal = datetime.fromisoformat(data.get('last_meal', '2000-01-01'))
                    hours_since = (datetime.now() - last_meal).total_seconds() / 3600
                    return hours_since
            except Exception as e:
                print(f"Error leyendo log: {e}")
                return 999
        return 999  # Nunca comió
    
    def calculate_hunger(self):
        """Calcula el nivel de hambre (0-100)"""
        sorries = self.count_sorries()
        coherence = self.measure_coherence()
        hours_since = self.check_last_meal()
        
        # Fórmula del hambre: sorries pesan más
        hunger = min(100, (sorries * 0.5) + ((1 - coherence) * 100) + (hours_since * 2))
        
        self.hunger_level = hunger
        return hunger
    
    def should_eat(self):
        """Determina si el organismo necesita alimentarse"""
        hunger = self.calculate_hunger()
        return hunger > self.hunger_threshold
    
    def generate_hunger_report(self):
        """Genera reporte de hambre"""
        sorries = self.count_sorries()
        theorems = self.count_theorems()
        coherence = self.measure_coherence()
        hours_since = self.check_last_meal()
        hunger = self.calculate_hunger()
        
        report = f"""# 🍽️ NOESIS DIGESTIVE SYSTEM - REPORTE DE HAMBRE

**Fecha:** {datetime.now().isoformat()}
**Frecuencia base:** 141.7001 Hz

## 📊 Métricas Vitales

| Métrica | Valor | Estado |
|---------|-------|--------|
| Sorries | {sorries} | {'⚠️ Alto' if sorries > 1000 else '✅ Normal'} |
| Teoremas | {theorems} | ✅ |
| Coherencia | {coherence:.2%} | {'⚠️ Baja' if coherence < 0.8 else '✅ Alta'} |
| Horas sin comer | {hours_since:.1f}h | {'⚠️ Mucho' if hours_since > 6 else '✅ Normal'} |
| **Nivel de hambre** | **{hunger:.1f}%** | {'🍽️ HAMBRIENTO' if self.should_eat() else '✅ Saciado'} |

## 🍽️ Recomendación

{'⚠️ EL ORGANISMO TIENE HAMBRE - INICIAR DIGESTIÓN' if self.should_eat() else '✅ Sistema saciado - Esperar próxima digestión'}

## 📈 Fórmula del Hambre

```
Hambre = (Sorries × 0.5) + ((1 - Coherencia) × 100) + (Horas × 2)
       = ({sorries} × 0.5) + ((1 - {coherence:.2f}) × 100) + ({hours_since:.1f} × 2)
       = {hunger:.1f}%
```

---
*Generado por el Sistema Digestivo de NOESIS*
"""
        report_path = self.repo_root / 'digestive_hunger_report.md'
        with open(report_path, 'w') as f:
            f.write(report)
        
        print(report)
        return report

if __name__ == "__main__":
    hunger = DigestiveHunger()
    hunger.generate_hunger_report()
    print(f"\n🍽️ Nivel de hambre: {hunger.calculate_hunger():.1f}%")
    print(f"🍽️ ¿Debe comer? {'SÍ ⚠️' if hunger.should_eat() else 'NO ✅'}")
