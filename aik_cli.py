#!/usr/bin/env python3
"""
AIK Beacon CLI - Command Line Interface
========================================

Herramienta de línea de comandos para generar y verificar beacons AIK.

Usage:
    # Generar beacon
    python aik_cli.py create --theorem "Rψ(5,5) ≤ 16" --proof proofs/RamseyRpsi_5_5.lean \\
                             --doi "10.5281/zenodo.17315719" --output beacon.json

    # Verificar beacon
    python aik_cli.py verify --beacon beacon.json

    # Ver información de un beacon
    python aik_cli.py info --beacon beacon.json

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
"""

import argparse
import json
import sys
from aik_beacon import AIKBeacon


def cmd_create(args):
    """Comando para crear un nuevo beacon."""
    try:
        beacon = AIKBeacon()

        # Construir metadatos adicionales si se proporcionan
        additional = {}
        if args.author:
            additional["author"] = args.author
        if args.institution:
            additional["institution"] = args.institution
        if args.coherence:
            additional["coherence"] = args.coherence
        if args.framework:
            additional["framework"] = args.framework

        # Crear el beacon
        b = beacon.create_beacon(
            theorem=args.theorem,
            proof_file=args.proof,
            doi=args.doi,
            f0=args.frequency,
            additional_metadata=additional if additional else None
        )

        # Guardar el beacon
        beacon.save_beacon(b, args.output)

        # Mostrar resumen
        print("✓ Beacon creado exitosamente")
        print(f"  Teorema: {args.theorem}")
        print(f"  DOI: {args.doi}")
        print(f"  Frecuencia: {args.frequency} Hz")
        print(f"  Archivo: {args.output}")
        print(f"  Hash: {b['hash'][:16]}...")

        if args.verbose:
            print("\nBeacon completo:")
            print(json.dumps(b, indent=2, ensure_ascii=False))

    except Exception as e:
        print(f"✗ Error al crear beacon: {e}", file=sys.stderr)
        sys.exit(1)


def cmd_verify(args):
    """Comando para verificar un beacon existente."""
    try:
        beacon = AIKBeacon()
        b = beacon.load_beacon(args.beacon)

        is_valid = beacon.verify_beacon(b)

        if is_valid:
            print("✓ Beacon VÁLIDO")
            print("  - Hash SHA3-256: ✓ válido")
            print("  - Firma ECDSA: ✓ válida")
            print("  - Integridad: ✓ confirmada")

            if args.verbose:
                print("\nDetalles:")
                print(f"  Teorema: {b['data']['theorem']}")
                print(f"  DOI: {b['data']['doi']}")
                print(f"  Frecuencia: {b['data']['f0']} Hz")
                print(f"  Timestamp: {b['data']['timestamp']}")
        else:
            print("✗ Beacon INVÁLIDO")
            print("  El beacon ha sido modificado o es corrupto")
            sys.exit(1)

    except FileNotFoundError:
        print(f"✗ Error: Archivo no encontrado: {args.beacon}", file=sys.stderr)
        sys.exit(1)
    except Exception as e:
        print(f"✗ Error al verificar beacon: {e}", file=sys.stderr)
        sys.exit(1)


def cmd_info(args):
    """Comando para mostrar información de un beacon."""
    try:
        beacon = AIKBeacon()
        b = beacon.load_beacon(args.beacon)

        print("=" * 70)
        print("INFORMACIÓN DEL BEACON")
        print("=" * 70)
        print(f"Teorema: {b['data']['theorem']}")
        print(f"DOI: {b['data']['doi']}")
        print(f"Frecuencia QCAL: {b['data']['f0']} Hz")
        print(f"Timestamp: {b['data']['timestamp']}")
        print(f"Hash prueba: {b['data']['proof_hash']}")
        print(f"Hash beacon: {b['hash']}")

        if "additional" in b["data"]:
            print("\nMetadatos adicionales:")
            for key, value in b["data"]["additional"].items():
                print(f"  {key}: {value}")

        print("\nFirma criptográfica:")
        print(f"  Firma: {b['signature'][:40]}...")
        print(f"  Clave pública: {b['public_key'][:40]}...")

        # Verificar automáticamente
        is_valid = beacon.verify_beacon(b)
        print(f"\nEstado: {'✓ VÁLIDO' if is_valid else '✗ INVÁLIDO'}")
        print("=" * 70)

    except FileNotFoundError:
        print(f"✗ Error: Archivo no encontrado: {args.beacon}", file=sys.stderr)
        sys.exit(1)
    except Exception as e:
        print(f"✗ Error al leer beacon: {e}", file=sys.stderr)
        sys.exit(1)


def main():
    """Función principal del CLI."""
    parser = argparse.ArgumentParser(
        description="AIK Beacon CLI - Herramienta de certificación matemática",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Ejemplos:
  # Crear beacon
  %(prog)s create --theorem "Rψ(5,5) ≤ 16" --proof proofs/proof.lean \\
                   --doi "10.5281/zenodo.17315719" --output beacon.json

  # Verificar beacon
  %(prog)s verify --beacon beacon.json

  # Ver información
  %(prog)s info --beacon beacon.json
        """
    )

    subparsers = parser.add_subparsers(dest="command", help="Comando a ejecutar")

    # Comando: create
    parser_create = subparsers.add_parser("create", help="Crear un nuevo beacon")
    parser_create.add_argument("--theorem", required=True, help="Enunciado del teorema")
    parser_create.add_argument("--proof", required=True, help="Archivo de prueba formal")
    parser_create.add_argument("--doi", required=True, help="Digital Object Identifier")
    parser_create.add_argument("--output", required=True, help="Archivo de salida JSON")
    parser_create.add_argument("--frequency", type=float, default=141.7001,
                               help="Frecuencia QCAL (default: 141.7001 Hz)")
    parser_create.add_argument("--author", help="Autor del teorema")
    parser_create.add_argument("--institution", help="Institución")
    parser_create.add_argument("--coherence", help="Constante de coherencia")
    parser_create.add_argument("--framework", help="Framework utilizado")
    parser_create.add_argument("-v", "--verbose", action="store_true",
                               help="Mostrar información detallada")

    # Comando: verify
    parser_verify = subparsers.add_parser("verify", help="Verificar un beacon")
    parser_verify.add_argument("--beacon", required=True, help="Archivo beacon JSON")
    parser_verify.add_argument("-v", "--verbose", action="store_true",
                               help="Mostrar información detallada")

    # Comando: info
    parser_info = subparsers.add_parser("info", help="Mostrar información de un beacon")
    parser_info.add_argument("--beacon", required=True, help="Archivo beacon JSON")

    args = parser.parse_args()

    if not args.command:
        parser.print_help()
        sys.exit(1)

    # Ejecutar comando correspondiente
    if args.command == "create":
        cmd_create(args)
    elif args.command == "verify":
        cmd_verify(args)
    elif args.command == "info":
        cmd_info(args)


if __name__ == "__main__":
    main()
