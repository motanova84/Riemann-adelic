#!/usr/bin/env python3
"""
TRACK SORRY PROGRESS - Rastreador de Progreso de Eliminación de Sorries
Monitorea el progreso de eliminación de sorries y valida coherencia Ψ = 1.000

Autor: José Manuel Mota Burruezo (JMMB Ψ✧)
Fecha: 18 febrero 2026
DOI: 10.5281/zenodo.17379721
"""

import json
import sys
from pathlib import Path
from datetime import datetime
from collections import defaultdict
import argparse


class SorryProgressTracker:
    """Rastreador de progreso de eliminación de sorries."""
    
    def __init__(self, repo_root):
        self.repo_root = Path(repo_root)
        self.formalization_dir = self.repo_root / 'formalization' / 'lean'
        self.progress_file = self.repo_root / '.sorry_progress.json'
        self.history = []
        
        # Cargar historial
        self.load_history()
    
    def log(self, message, level="INFO"):
        """Log mensaje a consola."""
        timestamp = datetime.now().strftime('%H:%M:%S')
        print(f"[{timestamp}] [{level}] {message}")
    
    def load_history(self):
        """Carga historial de progreso."""
        if self.progress_file.exists():
            try:
                with open(self.progress_file, 'r') as f:
                    data = json.load(f)
                    self.history = data.get('history', [])
            except Exception as e:
                self.log(f"⚠️  Error cargando historial: {e}", level="WARN")
    
    def save_history(self):
        """Guarda historial de progreso."""
        try:
            data = {
                'history': self.history,
                'last_update': datetime.now().isoformat()
            }
            with open(self.progress_file, 'w') as f:
                json.dump(data, f, indent=2)
        except Exception as e:
            self.log(f"⚠️  Error guardando historial: {e}", level="WARN")
    
    def count_sorries(self):
        """Cuenta sorries en archivos Lean."""
        stats = {
            'total': 0,
            'by_file': {},
            'by_category': defaultdict(int),
            'files_with_sorries': 0,
            'files_clean': 0
        }
        
        if not self.formalization_dir.exists():
            self.log(f"⚠️  Directorio no encontrado: {self.formalization_dir}", level="WARN")
            return stats
        
        for lean_file in self.formalization_dir.rglob('*.lean'):
            try:
                with open(lean_file, 'r', encoding='utf-8') as f:
                    lines = f.readlines()
                
                file_sorry_count = 0
                for line_num, line in enumerate(lines, 1):
                    if 'sorry' in line and not line.strip().startswith('--'):
                        file_sorry_count += 1
                        stats['total'] += 1
                        
                        # Categorizar
                        category = self.categorize_line(line)
                        stats['by_category'][category] += 1
                
                if file_sorry_count > 0:
                    stats['by_file'][str(lean_file.relative_to(self.repo_root))] = file_sorry_count
                    stats['files_with_sorries'] += 1
                else:
                    stats['files_clean'] += 1
                    
            except Exception as e:
                self.log(f"⚠️  Error leyendo {lean_file}: {e}", level="WARN")
        
        return stats
    
    def categorize_line(self, line):
        """Categoriza un sorry por su contexto."""
        line_lower = line.lower()
        
        if any(kw in line_lower for kw in ['qcal', 'coherence', 'ψ', 'f₀']):
            return 'qcal'
        elif any(kw in line_lower for kw in ['spectrum', 'eigenvalue', 'h_ψ', 'h_psi']):
            return 'spectral'
        elif any(kw in line_lower for kw in ['bijection', 'correspondence', 'equiv']):
            return 'correspondence'
        elif any(kw in line_lower for kw in ['trivial', 'rfl', 'exact']):
            return 'trivial'
        else:
            return 'other'
    
    def validate_coherence(self):
        """Valida coherencia QCAL Ψ = 1.000."""
        coherence_file = self.repo_root / 'data' / 'coherence_validation.json'
        
        if not coherence_file.exists():
            self.log("⚠️  Archivo de coherencia no encontrado", level="WARN")
            return None
        
        try:
            with open(coherence_file, 'r') as f:
                data = json.load(f)
                psi = data.get('psi', data.get('Ψ', None))
                
                if psi is not None:
                    # Verificar que Ψ ≈ 1.000 (con tolerancia)
                    tolerance = 0.001
                    is_coherent = abs(float(psi) - 1.000) < tolerance
                    return {
                        'psi': float(psi),
                        'coherent': is_coherent,
                        'tolerance': tolerance
                    }
        except Exception as e:
            self.log(f"⚠️  Error validando coherencia: {e}", level="WARN")
        
        return None
    
    def calculate_progress_rate(self):
        """Calcula la tasa de progreso basada en el historial."""
        if len(self.history) < 2:
            return None
        
        # Comparar últimas 2 entradas
        recent = self.history[-1]
        previous = self.history[-2]
        
        delta = previous['total'] - recent['total']
        time_diff = datetime.fromisoformat(recent['timestamp']) - \
                   datetime.fromisoformat(previous['timestamp'])
        
        hours = time_diff.total_seconds() / 3600
        
        return {
            'sorries_eliminated': delta,
            'time_hours': hours,
            'rate_per_hour': delta / hours if hours > 0 else 0
        }
    
    def estimate_completion(self, current_total):
        """Estima tiempo hasta 0 sorries."""
        progress_rate = self.calculate_progress_rate()
        
        if not progress_rate or progress_rate['rate_per_hour'] <= 0:
            return None
        
        hours_remaining = current_total / progress_rate['rate_per_hour']
        
        return {
            'sorries_remaining': current_total,
            'estimated_hours': hours_remaining,
            'estimated_days': hours_remaining / 24
        }
    
    def generate_progress_report(self):
        """Genera reporte completo de progreso."""
        self.log("📊 Generando reporte de progreso...")
        
        # Contar sorries actuales
        stats = self.count_sorries()
        
        # Validar coherencia
        coherence = self.validate_coherence()
        
        # Crear entrada de historial
        entry = {
            'timestamp': datetime.now().isoformat(),
            'total': stats['total'],
            'by_category': dict(stats['by_category']),
            'files_with_sorries': stats['files_with_sorries'],
            'files_clean': stats['files_clean'],
            'coherence': coherence
        }
        
        self.history.append(entry)
        
        # Calcular progreso
        progress_rate = self.calculate_progress_rate()
        completion_estimate = self.estimate_completion(stats['total'])
        
        # Generar reporte
        report = {
            'timestamp': datetime.now().isoformat(),
            'current_stats': stats,
            'coherence': coherence,
            'progress_rate': progress_rate,
            'completion_estimate': completion_estimate,
            'history_entries': len(self.history)
        }
        
        # Guardar reporte
        report_file = self.repo_root / 'data' / 'sorry_progress_report.json'
        report_file.parent.mkdir(parents=True, exist_ok=True)
        
        with open(report_file, 'w') as f:
            json.dump(report, f, indent=2)
        
        # Guardar historial
        self.save_history()
        
        # Mostrar resumen en consola
        self.print_summary(stats, coherence, progress_rate, completion_estimate)
        
        return report
    
    def print_summary(self, stats, coherence, progress_rate, completion_estimate):
        """Imprime resumen en consola."""
        print("\n" + "="*60)
        print("📊 REPORTE DE PROGRESO - ELIMINACIÓN DE SORRIES")
        print("="*60)
        
        print(f"\n📈 ESTADO ACTUAL:")
        print(f"   Total de sorries: {stats['total']}")
        print(f"   Archivos con sorries: {stats['files_with_sorries']}")
        print(f"   Archivos limpios: {stats['files_clean']}")
        
        if stats['by_category']:
            print(f"\n📋 POR CATEGORÍA:")
            for category, count in sorted(stats['by_category'].items(), key=lambda x: -x[1]):
                print(f"   {category}: {count}")
        
        if coherence:
            print(f"\n🌀 COHERENCIA QCAL:")
            print(f"   Ψ = {coherence['psi']:.6f}")
            status = "✅ COHERENTE" if coherence['coherent'] else "⚠️ INCOHERENTE"
            print(f"   Estado: {status}")
        else:
            print(f"\n⚠️  COHERENCIA: No disponible")
        
        if progress_rate:
            print(f"\n⚡ TASA DE PROGRESO:")
            print(f"   Sorries eliminados: {progress_rate['sorries_eliminated']}")
            print(f"   Tiempo transcurrido: {progress_rate['time_hours']:.2f} horas")
            print(f"   Tasa: {progress_rate['rate_per_hour']:.2f} sorries/hora")
        
        if completion_estimate:
            print(f"\n🎯 ESTIMACIÓN DE COMPLETITUD:")
            print(f"   Sorries restantes: {completion_estimate['sorries_remaining']}")
            print(f"   Tiempo estimado: {completion_estimate['estimated_hours']:.1f} horas")
            print(f"                    ({completion_estimate['estimated_days']:.1f} días)")
        
        # Top 5 archivos con más sorries
        if stats['by_file']:
            print(f"\n📁 TOP 5 ARCHIVOS CON MÁS SORRIES:")
            top_files = sorted(stats['by_file'].items(), key=lambda x: -x[1])[:5]
            for filepath, count in top_files:
                print(f"   {count:3d} - {filepath}")
        
        print("\n" + "="*60)
    
    def export_dashboard_data(self):
        """Exporta datos para dashboard visual."""
        dashboard_data = {
            'timestamp': datetime.now().isoformat(),
            'total_sorries': self.history[-1]['total'] if self.history else 0,
            'history': self.history[-10:],  # Últimas 10 entradas
            'coherence_status': self.history[-1].get('coherence') if self.history else None
        }
        
        dashboard_file = self.repo_root / 'data' / 'sorry_dashboard.json'
        dashboard_file.parent.mkdir(parents=True, exist_ok=True)
        
        with open(dashboard_file, 'w') as f:
            json.dump(dashboard_data, f, indent=2)
        
        self.log(f"📊 Dashboard data exportado: {dashboard_file}")


def main():
    """Punto de entrada principal."""
    parser = argparse.ArgumentParser(
        description='Track Sorry Progress - Rastreador de progreso de sorries'
    )
    parser.add_argument('--repo-root', type=str, default='.',
                        help='Raíz del repositorio')
    parser.add_argument('--export-dashboard', action='store_true',
                        help='Exportar datos para dashboard')
    
    args = parser.parse_args()
    
    tracker = SorryProgressTracker(repo_root=args.repo_root)
    
    try:
        tracker.generate_progress_report()
        
        if args.export_dashboard:
            tracker.export_dashboard_data()
        
        return 0
    except Exception as e:
        tracker.log(f"❌ Error fatal: {e}", level="ERROR")
        import traceback
        traceback.print_exc()
        return 1


if __name__ == "__main__":
    sys.exit(main())
