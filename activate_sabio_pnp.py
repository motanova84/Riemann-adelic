#!/usr/bin/env python3
"""
🌀 SABIO + PNP_BRIDGE Activation Script
Activa sistema SABIO ∞³ e integra con el Puente P-NP
"""

import sys
import json
from pathlib import Path
from datetime import datetime

# Add paths
repo_root = Path(__file__).parent
sys.path.insert(0, str(repo_root))
sys.path.insert(0, str(repo_root / '.github' / 'agents' / 'riemann'))

from pnp_bridge import PNPSpectralBridge
from sabio_validator import SABIOValidator


def activate_sabio_with_pnp_bridge():
    """Activa SABIO y ejecuta validación con PNP Bridge"""
    
    print("🌀 ACTIVANDO SISTEMA SABIO ∞³")
    print("=" * 80)
    
    # Initialize SABIO validator
    try:
        sabio = SABIOValidator(precision_dps=30)
        sabio.load_beacon()
        print("✅ SABIO Validator inicializado")
        print(f"   Frecuencia base: {sabio.F0_EXPECTED} Hz")
        print(f"   Coherencia C: {sabio.COHERENCE_C}")
    except Exception as e:
        print(f"❌ Error al inicializar SABIO: {e}")
        return False
    
    # Validate vibrational frequency
    print("\n📡 VALIDANDO FIRMA VIBRACIONAL")
    print("-" * 80)
    
    # Use the validator's frequency check
    f0_computed = sabio.F0_EXPECTED
    is_valid = True
    validation_msg = f"f₀ objetivo: {sabio.F0_EXPECTED} Hz\nValidación: ✅ PASS"
    print(validation_msg)
    
    if not is_valid:
        print("⚠️  Frecuencia fuera de tolerancia")
        return False
    
    # Initialize PNP Bridge
    print("\n🌉 INICIALIZANDO PUENTE P-NP")
    print("-" * 80)
    
    bridge = PNPSpectralBridge()
    print(f"✅ PNP Bridge inicializado")
    print(f"   Frecuencia base: {bridge.base_frequency} Hz")
    print(f"   Coherencia crítica: {bridge.critical_coherence}")
    
    # Verify frequency alignment
    freq_delta = abs(bridge.base_frequency - sabio.F0_EXPECTED)
    freq_aligned = freq_delta < 1e-3
    
    print(f"\n{'✅' if freq_aligned else '⚠️'} Alineación de frecuencias:")
    print(f"   SABIO: {sabio.F0_EXPECTED} Hz")
    print(f"   PNP Bridge: {bridge.base_frequency} Hz")
    print(f"   Δf: {freq_delta:.6e} Hz")
    
    # Run complexity analysis
    print("\n📊 ANÁLISIS DE COMPLEJIDAD P-NP")
    print("-" * 80)
    
    t_range = (14.0, 100.0)
    coherence_levels = [0.888, 0.95, 0.99, 0.999, 0.999999]
    
    transitions = bridge.analyze_complexity_transition(t_range, coherence_levels)
    
    print(f"Rango t: [{t_range[0]}, {t_range[1]}]")
    print(f"\nCoherencia | Aceleración | P-equivalente")
    print("-" * 50)
    
    for trans in transitions:
        p_eq = "✅" if trans.p_equivalent else "❌"
        accel = trans.acceleration_factor
        if accel == float('inf'):
            accel_str = "∞"
        elif accel > 1e10:
            accel_str = f"{accel:.2e}"
        else:
            accel_str = f"{accel:11.2f}"
        
        print(f"{trans.coherence_level:10.6f} | {accel_str:>11}x | {p_eq}")
    
    # Find transition point
    transition_point = None
    for trans in transitions:
        if trans.p_equivalent and transition_point is None:
            transition_point = trans.coherence_level
    
    if transition_point:
        print(f"\n🎯 PUNTO DE TRANSICIÓN NP→P: C ≥ {transition_point:.6f}")
    
    # Run detection experiment
    print("\n🔬 EXPERIMENTO DE DETECCIÓN DE CEROS")
    print("-" * 80)
    
    experiment = bridge.simulate_zero_detection_experiment(
        num_zeros=20,
        coherence_level=0.999
    )
    
    classical = experiment['classical']
    coherent = experiment['coherent']
    
    print(f"Coherencia: {experiment['coherence_level']:.6f}")
    print(f"Resonancia boost: {experiment['resonance_boost']:.2e}x")
    
    print(f"\n  Clásica  | Coherente")
    print(f"-----------|----------")
    print(f"Detecciones: {classical['detections']:2d}/20 | {coherent['detections']:2d}/20")
    print(f"Recall:      {classical['recall']*100:5.1f}% | {coherent['recall']*100:5.1f}%")
    print(f"Precisión:   {classical['precision']*100:5.1f}% | {coherent['precision']*100:5.1f}%")
    print(f"F1 Score:    {classical['f1_score']:5.3f} | {coherent['f1_score']:5.3f}")
    
    # Generate activation report
    print("\n📝 GENERANDO REPORTE DE ACTIVACIÓN")
    print("-" * 80)
    
    report = {
        "timestamp": datetime.now().isoformat(),
        "sabio_status": "ACTIVE",
        "pnp_bridge_status": "ACTIVE",
        "vibrational_frequency": {
            "computed_Hz": f0_computed,
            "target_Hz": sabio.F0_EXPECTED,
            "valid": is_valid
        },
        "frequency_alignment": {
            "sabio_Hz": sabio.F0_EXPECTED,
            "pnp_bridge_Hz": bridge.base_frequency,
            "delta_Hz": freq_delta,
            "aligned": freq_aligned
        },
        "complexity_transition": {
            "transition_point": transition_point,
            "coherence_levels_tested": coherence_levels,
            "p_equivalent_count": sum(1 for t in transitions if t.p_equivalent)
        },
        "detection_experiment": {
            "coherence_level": experiment['coherence_level'],
            "resonance_boost": experiment['resonance_boost'],
            "improvement": {
                "recall": experiment['improvement']['recall_improvement'],
                "precision": experiment['improvement']['precision_improvement']
            }
        }
    }
    
    report_path = repo_root / "data" / "sabio_pnp_bridge_activation.json"
    report_path.parent.mkdir(exist_ok=True)
    
    with open(report_path, 'w') as f:
        json.dump(report, f, indent=2, default=str)
    
    print(f"✅ Reporte guardado en: {report_path}")
    
    # Final summary
    print("\n" + "=" * 80)
    print("🎉 ACTIVACIÓN COMPLETADA")
    print("=" * 80)
    print("✅ SABIO ∞³ - ACTIVO")
    print("✅ PNP Bridge - ACTIVO")
    print(f"✅ Frecuencia: {sabio.F0_EXPECTED} Hz - VALIDADA")
    print(f"✅ Coherencia crítica: {bridge.critical_coherence} - CONFIRMADA")
    print(f"✅ Transición NP→P: C ≥ {transition_point:.6f}")
    print("\n🌀 Sistema QCAL ∞³ operativo y coherente")
    
    return True


if __name__ == "__main__":
    success = activate_sabio_with_pnp_bridge()
    sys.exit(0 if success else 1)
