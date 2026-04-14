#!/usr/bin/env python3
"""
📊 METRICS COLLECTOR - Recolector de Métricas QCAL ∞³
Recopila y analiza métricas del sistema QCAL
"""

import argparse
import json
import re
import sys
from datetime import datetime
from pathlib import Path


class MetricsCollector:
    """Recolector de métricas del sistema QCAL"""
    
    FREQUENCY_BASE = 141.7001  # Hz
    QCAL_PATTERNS = [
        r'QCAL',
        r'∞³',
        r'Ψ',
        r'I × A_eff² × C',
        r'141\.7001'
    ]
    
    def __init__(self, frequency=None, optimized=False, detailed=False):
        self.frequency = frequency or self.FREQUENCY_BASE
        self.optimized = optimized
        self.detailed = detailed
        self.timestamp = datetime.now().isoformat()
        self.root_path = Path.cwd()
        
    def scan_files(self):
        """Escanea archivos del repositorio"""
        python_files = list(self.root_path.glob("**/*.py"))
        md_files = list(self.root_path.glob("**/*.md"))
        lean_files = list(self.root_path.glob("**/*.lean"))
        
        # Excluir ciertos directorios
        exclude_dirs = {'.git', 'node_modules', '__pycache__', '.venv', 'venv'}
        
        all_files = []
        for f in python_files + md_files + lean_files:
            if not any(ex in f.parts for ex in exclude_dirs):
                all_files.append(f)
        
        return all_files
    
    def count_qcal_references(self, files):
        """Cuenta referencias QCAL en archivos"""
        qcal_count = 0
        freq_count = 0
        infinity_count = 0
        psi_count = 0
        
        for filepath in files:
            try:
                content = filepath.read_text(encoding='utf-8', errors='ignore')
                
                if 'QCAL' in content:
                    qcal_count += 1
                if '141.7001' in content or str(self.frequency) in content:
                    freq_count += 1
                if '∞³' in content or 'infinity³' in content:
                    infinity_count += 1
                if 'Ψ' in content or 'Psi' in content:
                    psi_count += 1
                    
            except Exception:
                continue
        
        return {
            "qcal_references": qcal_count,
            "frequency_references": freq_count,
            "infinity_cubed_references": infinity_count,
            "psi_state_references": psi_count
        }
    
    def analyze_file_types(self, files):
        """Analiza distribución de tipos de archivo"""
        file_types = {}
        for f in files:
            ext = f.suffix
            file_types[ext] = file_types.get(ext, 0) + 1
        
        return file_types
    
    def calculate_qcal_density(self, total_files, qcal_refs):
        """Calcula densidad de referencias QCAL"""
        if total_files == 0:
            return 0.0
        return qcal_refs / total_files
    
    def collect_metrics(self):
        """Recopila todas las métricas"""
        files = self.scan_files()
        total_files = len(files)
        
        qcal_refs = self.count_qcal_references(files)
        file_types = self.analyze_file_types(files)
        
        qcal_density = self.calculate_qcal_density(
            total_files, 
            qcal_refs['qcal_references']
        )
        freq_density = self.calculate_qcal_density(
            total_files,
            qcal_refs['frequency_references']
        )
        
        metrics = {
            "timestamp": self.timestamp,
            "frequency": self.frequency,
            "optimized": self.optimized,
            "files": {
                "total_files": total_files,
                "by_type": file_types
            },
            "qcal": qcal_refs,
            "density": {
                "qcal_density": round(qcal_density, 4),
                "frequency_density": round(freq_density, 4)
            }
        }
        
        return metrics
    
    def save_metrics(self, metrics, output=None):
        """Guarda métricas en archivo"""
        metrics_dir = Path("metrics")
        metrics_dir.mkdir(exist_ok=True)
        
        if output:
            filepath = Path(output)
        else:
            filename = f"daily_{datetime.now().strftime('%Y%m%d')}.json"
            filepath = metrics_dir / filename
        
        with open(filepath, 'w') as f:
            json.dump(metrics, indent=2, fp=f)
        
        print(f"✅ Métricas guardadas: {filepath}")
        return filepath
    
    def run(self):
        """Ejecuta la recolección de métricas"""
        print("📊 METRICS COLLECTOR - Recopilando métricas...")
        print(f"   Frecuencia base: {self.frequency} Hz")
        print(f"   Modo optimizado: {self.optimized}")
        print()
        
        metrics = self.collect_metrics()
        
        print("📈 Métricas recopiladas:")
        print(f"   Total archivos: {metrics['files']['total_files']}")
        print(f"   Referencias QCAL: {metrics['qcal']['qcal_references']}")
        print(f"   Referencias f₀: {metrics['qcal']['frequency_references']}")
        print(f"   Densidad QCAL: {metrics['density']['qcal_density']:.4f}")
        print(f"   Densidad f₀: {metrics['density']['frequency_density']:.4f}")
        print()
        
        filepath = self.save_metrics(metrics)
        
        return 0


def main():
    parser = argparse.ArgumentParser(
        description="Metrics Collector - Recolector de Métricas QCAL"
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
    parser.add_argument(
        "--detailed",
        action="store_true",
        help="Generar reporte detallado"
    )
    parser.add_argument(
        "--output",
        type=str,
        help="Archivo de salida para métricas"
    )
    
    args = parser.parse_args()
    
    collector = MetricsCollector(
        frequency=args.frequency,
        optimized=args.optimized,
        detailed=args.detailed
    )
    
    return collector.run()


if __name__ == "__main__":
    sys.exit(main())
