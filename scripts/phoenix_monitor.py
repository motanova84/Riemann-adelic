#!/usr/bin/env python3
"""
Phoenix Monitoring Dashboard

Tracks Phoenix Solver progress over time and displays metrics.
"""

import json
import sys
from pathlib import Path
from datetime import datetime
from typing import Dict, List


class PhoenixMonitor:
    """Monitor and display Phoenix Solver progress."""
    
    def __init__(self, repo_root: Path):
        self.repo_root = repo_root
        self.data_dir = repo_root / "data"
        
    def load_latest_stats(self) -> Dict:
        """Load the most recent Phoenix statistics."""
        phoenix_files = list(self.data_dir.glob("phoenix_*.json"))
        
        if not phoenix_files:
            return {}
        
        # Get the most recent file
        latest_file = max(phoenix_files, key=lambda p: p.stat().st_mtime)
        
        with open(latest_file, 'r') as f:
            return json.load(f)
    
    def load_sorry_map(self) -> Dict:
        """Load current sorry statement mapping."""
        sorry_map_file = self.data_dir / "sorry_map.json"
        
        if not sorry_map_file.exists():
            return {'total': 0, 'by_file': {}, 'details': []}
        
        with open(sorry_map_file, 'r') as f:
            return json.load(f)
    
    def calculate_progress(self) -> Dict:
        """Calculate overall progress metrics."""
        sorry_data = self.load_sorry_map()
        
        # Targets
        target_sorry = 0
        target_coherence = 0.999999
        
        # Current
        current_sorry = sorry_data.get('total', 2237)
        current_coherence = 0.244231  # From .qcal_beacon
        
        # Calculate percentages
        sorry_progress = ((2237 - current_sorry) / 2237) * 100 if current_sorry <= 2237 else 0
        coherence_progress = (current_coherence / target_coherence) * 100
        
        return {
            'current_sorry': current_sorry,
            'target_sorry': target_sorry,
            'sorry_progress_pct': sorry_progress,
            'current_coherence': current_coherence,
            'target_coherence': target_coherence,
            'coherence_progress_pct': coherence_progress,
            'original_sorry': 2237
        }
    
    def display_dashboard(self):
        """Display the monitoring dashboard."""
        print("=" * 70)
        print("🔥 PHOENIX SOLVER - MONITORING DASHBOARD")
        print("=" * 70)
        print()
        
        # Load data
        progress = self.calculate_progress()
        sorry_data = self.load_sorry_map()
        latest_stats = self.load_latest_stats()
        
        # Display main metrics
        print("📊 MAIN METRICS")
        print("-" * 70)
        
        # Sorry count progress bar
        sorry_pct = progress['sorry_progress_pct']
        bar_width = 40
        filled = int(bar_width * sorry_pct / 100)
        bar = '█' * filled + '░' * (bar_width - filled)
        
        print(f"Sorry Statements:  {progress['current_sorry']:4d} / {progress['target_sorry']:4d}")
        print(f"                   [{bar}] {sorry_pct:.1f}%")
        print(f"                   (Original: {progress['original_sorry']})")
        print()
        
        # Coherence progress bar
        coh_pct = progress['coherence_progress_pct']
        filled = int(bar_width * coh_pct / 100)
        bar = '█' * filled + '░' * (bar_width - filled)
        
        print(f"Coherence Ψ:       {progress['current_coherence']:.6f} / {progress['target_coherence']:.6f}")
        print(f"                   [{bar}] {coh_pct:.1f}%")
        print()
        
        # QCAL Integrity status
        if progress['current_coherence'] >= 0.9:
            status = "Certified ∞³"
            color = "🟢"
        elif progress['current_coherence'] >= 0.5:
            status = "Active/Autocrítica"
            color = "🟡"
        else:
            status = "Passive"
            color = "🔴"
        
        print(f"QCAL Integrity:    {color} {status}")
        print()
        
        # Latest run statistics
        if latest_stats:
            print("📈 LATEST PHOENIX RUN")
            print("-" * 70)
            print(f"Timestamp:         {latest_stats.get('timestamp', 'N/A')}")
            print(f"Resolved:          {latest_stats.get('resolved', 0)}")
            print(f"Failed:            {latest_stats.get('failed', 0)}")
            
            coh_before = latest_stats.get('coherence_before', 0)
            coh_after = latest_stats.get('coherence_after', 0)
            delta_coh = coh_after - coh_before
            
            print(f"Coherence Change:  {delta_coh:+.6f}")
            print()
        
        # Top files with sorries
        if sorry_data.get('by_file'):
            print("🎯 TOP FILES REQUIRING ATTENTION")
            print("-" * 70)
            
            sorted_files = sorted(
                sorry_data['by_file'].items(),
                key=lambda x: x[1],
                reverse=True
            )[:10]
            
            for i, (file_path, count) in enumerate(sorted_files, 1):
                # Shorten path for display
                short_path = file_path.replace('formalization/', '')
                if len(short_path) > 55:
                    short_path = "..." + short_path[-52:]
                print(f"  {i:2d}. {count:3d} sorry  {short_path}")
            print()
        
        # Convergence estimate
        print("⏱️  CONVERGENCE ESTIMATE")
        print("-" * 70)
        
        if latest_stats and latest_stats.get('resolved', 0) > 0:
            resolved_per_run = latest_stats['resolved']
            remaining = progress['current_sorry']
            
            if resolved_per_run > 0:
                estimated_runs = remaining / resolved_per_run
                # Assuming hourly runs
                estimated_hours = estimated_runs * 1
                estimated_days = estimated_hours / 24
                
                print(f"Resolved per run:  {resolved_per_run}")
                print(f"Remaining sorry:   {remaining}")
                print(f"Estimated runs:    {estimated_runs:.0f}")
                print(f"Estimated time:    {estimated_days:.1f} days (at 1 run/hour)")
            else:
                print("No recent resolutions - refining strategies...")
        else:
            print("Awaiting first successful resolution...")
        
        print()
        print("=" * 70)
        print("QCAL ∞³ ACTIVE — ∴𓂀Ω∞³·RH")
        print("=" * 70)


def main():
    repo_root = Path(__file__).parent.parent
    
    monitor = PhoenixMonitor(repo_root)
    monitor.display_dashboard()
    
    return 0


if __name__ == "__main__":
    sys.exit(main())
