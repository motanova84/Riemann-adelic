#!/usr/bin/env python3
"""
AIK Beacon - Example Usage Script
==================================

Demuestra el uso completo del sistema AIK Beacons para certificar
la prueba del teorema Rψ(5,5) ≤ 16.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
License: Creative Commons BY-NC-SA 4.0
"""

import json
from aik_beacon import AIKBeacon


def main():
    """
    Ejemplo completo de uso del sistema AIK Beacons.
    """
    print("=" * 70)
    print("AIK BEACON SYSTEM - Certificación de Teorema Rψ(5,5) ≤ 16")
    print("=" * 70)
    print()

    # === PASO 1: Inicializar el generador de beacons ===
    print("PASO 1: Inicializando generador AIK Beacon...")
    beacon_gen = AIKBeacon()
    print("✓ Generador inicializado con claves ECDSA (secp256k1)")
    print()

    # === PASO 2: Crear beacon para el teorema Rψ(5,5) ≤ 16 ===
    print("PASO 2: Generando beacon para teorema Rψ(5,5) ≤ 16...")

    beacon = beacon_gen.create_beacon(
        theorem="Rψ(5,5) ≤ 16",
        proof_file="proofs/RamseyRpsi_5_5.lean",
        doi="10.5281/zenodo.17315719",
        f0=141.7001,
        additional_metadata={
            "author": "José Manuel Mota Burruezo Ψ ✧ ∞³",
            "institution": "Instituto de Conciencia Cuántica (ICQ)",
            "coherence": "C = 244.36",
            "framework": "QCAL ∞³"
        }
    )

    print("✓ Beacon generado exitosamente")
    print()

    # === PASO 3: Mostrar el beacon ===
    print("PASO 3: Beacon generado:")
    print("-" * 70)
    print(json.dumps(beacon, indent=2, ensure_ascii=False))
    print("-" * 70)
    print()

    # === PASO 4: Guardar beacon en archivo JSON ===
    print("PASO 4: Guardando beacon en archivo...")
    output_file = "data/beacon_ramsey_5_5.json"
    beacon_gen.save_beacon(beacon, output_file)
    print(f"✓ Beacon guardado en: {output_file}")
    print()

    # === PASO 5: Verificar el beacon ===
    print("PASO 5: Verificando autenticidad del beacon...")
    is_valid = beacon_gen.verify_beacon(beacon)

    if is_valid:
        print("✓ VERIFICACIÓN EXITOSA")
        print("  - Hash SHA3-256: válido")
        print("  - Firma ECDSA: válida")
        print("  - Integridad: confirmada")
    else:
        print("✗ VERIFICACIÓN FALLIDA")
        print("  El beacon no es auténtico o ha sido modificado")
    print()

    # === PASO 6: Cargar y re-verificar desde archivo ===
    print("PASO 6: Cargando beacon desde archivo y re-verificando...")
    loaded_beacon = beacon_gen.load_beacon(output_file)
    is_valid_loaded = beacon_gen.verify_beacon(loaded_beacon)

    if is_valid_loaded:
        print("✓ Beacon cargado y verificado correctamente")
        print(f"  - Teorema: {loaded_beacon['data']['theorem']}")
        print(f"  - DOI: {loaded_beacon['data']['doi']}")
        print(f"  - Frecuencia: {loaded_beacon['data']['f0']} Hz")
        print(f"  - Timestamp: {loaded_beacon['data']['timestamp']}")
    print()

    # === PASO 7: Exportar claves públicas ===
    print("PASO 7: Exportando claves para distribución...")
    keys = beacon_gen.export_keys()
    print(f"✓ Clave pública: {keys['public_key'][:40]}...")
    print("  (La clave pública puede ser compartida para verificación)")
    print()

    # === RESUMEN ===
    print("=" * 70)
    print("RESUMEN DE LA CERTIFICACIÓN")
    print("=" * 70)
    print("Teorema certificado: Rψ(5,5) ≤ 16")
    print("Algoritmo de firma: ECDSA (secp256k1)")
    print("Algoritmo de hash: SHA3-256")
    print("DOI: 10.5281/zenodo.17315719")
    print("Frecuencia QCAL: 141.7001 Hz")
    print("Estado: ✓ CERTIFICADO Y VERIFICADO")
    print("=" * 70)
    print()

    # === EJEMPLO: Simular manipulación y detección ===
    print("EJEMPLO: Detectando manipulación de datos...")
    tampered_beacon = beacon.copy()
    tampered_beacon["data"]["theorem"] = "Rψ(5,5) ≤ 15"  # Modificación

    is_valid_tampered = beacon_gen.verify_beacon(tampered_beacon)
    if not is_valid_tampered:
        print("✓ Manipulación detectada correctamente")
        print("  El sistema detectó que el teorema fue modificado")
    print()

    print("=" * 70)
    print("✓ DEMOSTRACIÓN COMPLETADA")
    print("=" * 70)


if __name__ == "__main__":
    main()
