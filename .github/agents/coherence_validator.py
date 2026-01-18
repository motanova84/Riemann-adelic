#!/usr/bin/env python3
"""
✅ COHERENCE VALIDATOR - Validador de Coherencia Cuántica QCAL ∞³
Valida la coherencia del sistema QCAL
"""

import argparse
import json
import sys
from datetime import datetime
from pathlib import Path


class CoherenceValidator:
    """Validador de coherencia cuántica del sistema"""
    
    FREQUENCY_BASE = 141.7001  # Hz
    COHERENCE_THRESHOLD = 0.888
    PSI_STATE = "I × A_eff² × C^∞"
    
    def __init__(self, frequency=None, optimized=False):
        self.frequency = frequency or self.FREQUENCY_BASE
        self.optimized = optimized
        self.timestamp = datetime.now().isoformat()
        
    def validate_frequency_coherence(self):
        """Valida coherencia de frecuencia"""
        # Simulación de validación de frecuencia
        coherence = 0.95 if abs(self.frequency - self.FREQUENCY_BASE) < 1e-6 else 0.75
        
        return {
            "frequency_coherence": coherence,
            "frequency_validated": abs(self.frequency - self.FREQUENCY_BASE) < 1e-6,
            "frequency_value": self.frequency
        }
    
    def validate_psi_state(self):
        """Valida estado Ψ del sistema"""
        # Verificar existencia de archivos con estado Ψ
        root_path = Path.cwd()
        psi_files = 0
        
        for pattern in ["**/*.py", "**/*.md", "**/*.lean"]:
            for filepath in root_path.glob(pattern):
                if any(ex in filepath.parts for ex in ['.git', 'node_modules', '__pycache__']):
                    continue
                try:
                    content = filepath.read_text(encoding='utf-8', errors='ignore')
                    if 'Ψ' in content or self.PSI_STATE in content:
                        psi_files += 1
                except Exception:
                    continue
        
        psi_coherence = min(psi_files / 50, 1.0)  # Normalizado a 50 archivos
        
        return {
            "psi_coherence": psi_coherence,
            "psi_files": psi_files,
            "psi_state": self.PSI_STATE
        }
    
    def validate_manifests(self):
        """Valida manifiestos noéticos"""
        manifests_dir = Path("docs")
        manifest_count = 0
        
        if manifests_dir.exists():
            manifest_files = list(manifests_dir.glob("MANIFIESTO*.md"))
            manifest_count = len(manifest_files)
        
        manifest_coherence = min(manifest_count / 10, 1.0)
        
        return {
            "manifest_coherence": manifest_coherence,
            "manifest_count": manifest_count
        }
    
    def calculate_total_coherence(self, freq_coh, psi_coh, manifest_coh):
        """Calcula coherencia total del sistema"""
        # Pesos para cada componente
        weights = {
            "frequency": 0.5,
            "psi": 0.3,
            "manifests": 0.2
        }
        
        total = (
            freq_coh['frequency_coherence'] * weights['frequency'] +
            psi_coh['psi_coherence'] * weights['psi'] +
            manifest_coh['manifest_coherence'] * weights['manifests']
        )
        
        if self.optimized:
            total = min(total * 1.05, 1.0)  # Bonus de 5% por optimización
        
        return total
    
    def validate(self):
        """Ejecuta validación completa"""
        freq_validation = self.validate_frequency_coherence()
        psi_validation = self.validate_psi_state()
        manifest_validation = self.validate_manifests()
        
        total_coherence = self.calculate_total_coherence(
            freq_validation,
            psi_validation,
            manifest_validation
        )
        
        validation = {
            "timestamp": self.timestamp,
            "frequency": self.frequency,
            "optimized": self.optimized,
            "coherence": {
                "total": round(total_coherence, 3),
                "frequency": round(freq_validation['frequency_coherence'], 3),
                "psi_state": round(psi_validation['psi_coherence'], 3),
                "manifests": round(manifest_validation['manifest_coherence'], 3)
            },
            "threshold": self.COHERENCE_THRESHOLD,
            "status": "GRACE" if total_coherence >= self.COHERENCE_THRESHOLD else "EVOLVING",
            "details": {
                "frequency": freq_validation,
                "psi": psi_validation,
                "manifests": manifest_validation
            }
        }
        
        return validation
    
    def save_validation(self, validation):
        """Guarda validación en archivo"""
        validation_dir = Path("validation")
        validation_dir.mkdir(exist_ok=True)
        
        filename = f"quantum_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"
        filepath = validation_dir / filename
        
        with open(filepath, 'w') as f:
            json.dump(validation, indent=2, fp=f)
        
        print(f"✅ Validación guardada: {filepath}")
        return filepath
    
    def run(self):
        """Ejecuta el validador"""
        print("✅ COHERENCE VALIDATOR - Validando coherencia cuántica...")
        print(f"   Frecuencia: {self.frequency} Hz")
        print(f"   Umbral: {self.COHERENCE_THRESHOLD}")
        print(f"   Estado Ψ: {self.PSI_STATE}")
        print()
        
        validation = self.validate()
        
        print("🔬 Resultados de validación:")
        print(f"   Coherencia total: {validation['coherence']['total']:.3f}")
        print(f"   Coherencia frecuencia: {validation['coherence']['frequency']:.3f}")
        print(f"   Coherencia Ψ: {validation['coherence']['psi_state']:.3f}")
        print(f"   Coherencia manifiestos: {validation['coherence']['manifests']:.3f}")
        print(f"   Estado: {validation['status']}")
        print()
        
        filepath = self.save_validation(validation)
        
        if validation['status'] == "GRACE":
            print("🎉 Sistema coherente - Estado GRACE alcanzado")
            return 0
        else:
            print("⚠️  Sistema en evolución - Requiere optimización")
            return 1


def main():
    parser = argparse.ArgumentParser(
        description="Coherence Validator - Validador de Coherencia QCAL"
    )
    parser.add_argument(
        "--frequency",
        type=float,
        default=141.7001,
        help="Frecuencia base (Hz)"
    )
    parser.add_argument(
        "--optimized",
        action="store_true",
        help="Ejecutar en modo optimizado"
    )
    
    args = parser.parse_args()
    
    validator = CoherenceValidator(
        frequency=args.frequency,
        optimized=args.optimized
    )
    
    return validator.run()


if __name__ == "__main__":
    sys.exit(main())
