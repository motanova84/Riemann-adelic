#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Ejemplo de uso: Experimento QCAL con observador real personalizado

Este script demuestra cómo registrar un observador físico personalizado
para uno de los nodos antes de ejecutar el experimento.
"""

import os
os.environ["QCAL_REAL_TESTS"] = "1"

from mcp_network.resonance import register_real_observer
from experiments.live_qcal_hardware_experiment import run_live_experiment

# Ejemplo 1: Observador simple simulando un magnetómetro QMC5883L
def qmc5883l_magnetometer():
    """
    Simula lecturas de un magnetómetro QMC5883L conectado vía I²C.
    
    En producción, aquí iría la lectura real del sensor:
        import smbus
        bus = smbus.SMBus(1)
        # leer datos del QMC5883L en dirección 0x0D
        # calcular latencia y fase desde campo magnético
    
    Returns:
        tuple: (latency_ms, phase_offset_rad, heartbeat_ok, schema_ok)
    """
    # Valores simulados (reemplazar con lecturas reales)
    latency_ms = 9.5  # Latencia de lectura I²C
    phase_offset_rad = 0.014  # Fase calculada desde campo magnético
    heartbeat_ok = True  # Sensor responde
    schema_ok = True  # Datos válidos
    
    return (latency_ms, phase_offset_rad, heartbeat_ok, schema_ok)


# Ejemplo 2: Observador para dispositivo OpenBCI (EEG/HRV)
def openbci_biosensor():
    """
    Simula lecturas de un dispositivo OpenBCI para señales biológicas.
    
    En producción:
        from brainflow import BoardShim, BoardIds
        board = BoardShim(BoardIds.CYTON_BOARD, ...)
        # leer EEG, calcular coherencia cardíaca (HRV)
    
    Returns:
        tuple: (latency_ms, phase_offset_rad, heartbeat_ok, schema_ok)
    """
    latency_ms = 11.8  # Latencia USB + procesamiento
    phase_offset_rad = 0.017  # Fase desde análisis de coherencia
    heartbeat_ok = True
    schema_ok = True
    
    return (latency_ms, phase_offset_rad, heartbeat_ok, schema_ok)


# Registrar observadores para nodos específicos
print("🔌 Registrando observadores físicos...")
register_real_observer("interferometro-noesico", qmc5883l_magnetometer)
register_real_observer("biologia-cuantica-noesica", openbci_biosensor)
print("   ✅ interferometro-noesico → qmc5883l_magnetometer")
print("   ✅ biologia-cuantica-noesica → openbci_biosensor")
print()

# Ejecutar experimento (ajustar duración según necesidad)
print("🚀 Iniciando experimento con hardware mixto...")
print("   • auron-governor: simulado")
print("   • 141-hz: simulado")
print("   • interferometro-noesico: magnetómetro real")
print("   • biologia-cuantica-noesica: biosensor real")
print()

# Duración: 5 minutos para este ejemplo
run_live_experiment(duration_minutes=5)

print("\n✨ Experimento completado")
print("📊 Analizar resultados con:")
print("   python -c 'import pandas as pd; df=pd.read_csv(\"experiments/experiment_log.csv\"); print(df.groupby(\"node\")[\"psi\"].describe())'")
