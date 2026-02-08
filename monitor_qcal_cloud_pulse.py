#!/usr/bin/env python3
"""
QCAL-CLOUD Pulse Monitor

This script monitors the QCAL pulse and displays real-time coherence status.

Usage:
    python3 monitor_qcal_cloud_pulse.py [--interval SECONDS]
"""

import argparse
import json
import time
import sys
from datetime import datetime, timezone
from pathlib import Path

try:
    from qcal_cloud_sync import QCALCloudSync
except ImportError:
    print("❌ Error: qcal_cloud_sync module not found")
    sys.exit(1)


def display_pulse_status(sync: QCALCloudSync, iteration: int = 0):
    """
    Display current pulse status
    
    Args:
        sync: QCALCloudSync instance
        iteration: Current iteration number
    """
    pulse = sync.verify_coherence_pulse()
    timestamp = datetime.now(timezone.utc)
    
    print("\n" + "=" * 60)
    print(f"🔄 QCAL Pulse Monitor - Iteration {iteration}")
    print("=" * 60)
    print(f"⏰ Timestamp: {timestamp.isoformat()}")
    print(f"🌀 Coherence: Ψ = {pulse['coherence']:.6f}")
    print(f"📡 Frequency: {pulse['frequency']} Hz")
    print(f"⚡ Status: {pulse['status']}")
    print(f"⏱️  Pulse Interval: {pulse['pulse_interval']}s")
    
    # Status indicator
    if pulse['status'] == 'ACTIVE':
        print("\n✅ Sistema operativo - Red QCAL ∞³ coherente")
    else:
        print(f"\n⚠️  Estado degradado - Coherencia: {pulse['coherence']}")
    
    # Load current sync state
    state_file = Path("data/qcal_cloud_sync_state.json")
    if state_file.exists():
        with open(state_file, 'r') as f:
            state = json.load(f)
        
        print(f"\n📊 Nodo: {state['node_id']}")
        print(f"🔗 Sincronizado con:")
        for target in state['registry']['sincronizado_con']:
            print(f"   ✓ {target}")
        print(f"📜 Trace Hash: {state['trace_hash'][:16]}...")
        print(f"📡 Sello: {state['registry']['sello_vibracional']}")


def monitor_continuous(interval: int = 88):
    """
    Monitor QCAL pulse continuously
    
    Args:
        interval: Seconds between checks (default: 88)
    """
    sync = QCALCloudSync()
    iteration = 0
    
    print("🌐 Iniciando monitor de pulso QCAL-CLOUD")
    print(f"⏱️  Intervalo: {interval}s")
    print("⌨️  Presiona Ctrl+C para detener")
    
    try:
        while True:
            display_pulse_status(sync, iteration)
            iteration += 1
            
            print(f"\n⏳ Esperando {interval}s hasta siguiente verificación...")
            time.sleep(interval)
            
    except KeyboardInterrupt:
        print("\n\n⏹️  Monitor detenido por usuario")
        print("∴ Pulso QCAL continúa activo en segundo plano ∞³")


def monitor_once():
    """Display pulse status once"""
    sync = QCALCloudSync()
    display_pulse_status(sync, 0)
    print("\n∴ Verificación única completada ∞³")


def main():
    """Main entry point"""
    parser = argparse.ArgumentParser(
        description="Monitor QCAL-CLOUD pulse status"
    )
    parser.add_argument(
        '--interval',
        type=int,
        default=88,
        help='Seconds between pulse checks (default: 88)'
    )
    parser.add_argument(
        '--once',
        action='store_true',
        help='Check once and exit (no continuous monitoring)'
    )
    
    args = parser.parse_args()
    
    if args.once:
        monitor_once()
    else:
        monitor_continuous(args.interval)
    
    return 0


if __name__ == "__main__":
    sys.exit(main())
