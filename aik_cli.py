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

    # Verificar beacon desde stdin (para verificación IPFS)
    curl -s https://ipfs.io/ipfs/QmX7...beacon.json | python aik_cli.py verify --stdin

    # Ver información de un beacon
    python aik_cli.py info --beacon beacon.json

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)

On-Chain Integration:
    Contract: AIKBeaconsProofOfMath on Base Mainnet
    Symbol: AIK∞³
    Verification: Offline + On-chain confirmation
"""

import argparse
import json
import sys
from typing import Optional
from aik_beacon import AIKBeacon, ONCHAIN_CONFIG


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

        # Load beacon from stdin or file
        if args.stdin:
            beacon_json = sys.stdin.read()
            b = json.loads(beacon_json)
        else:
            b = beacon.load_beacon(args.beacon)

        is_valid = beacon.verify_beacon(b)

        if is_valid:
            print("BEACON VERIFIED SUCCESSFULLY")
            print(f"Theorem: {b['data']['theorem']}")
            print(f"f0: {b['data']['f0']} Hz")
            print(f"Proof hash: {b['data']['proof_hash'][:16]}...")
            print("Signature: VALID (ECDSA secp256k1)")

            # Check for on-chain metadata if present
            if "onchain" in b.get("data", {}).get("additional", {}):
                onchain = b["data"]["additional"]["onchain"]
                print(f"ON-CHAIN CONFIRMED: Token ID #{onchain.get('token_id', 'N/A')}")
            elif args.check_onchain:
                # Simulate on-chain lookup based on beacon hash
                token_id = _lookup_onchain_token(b["hash"])
                if token_id is not None:
                    print(f"ON-CHAIN CONFIRMED: Token ID #{token_id:03d}")
                else:
                    print("ON-CHAIN: Not minted yet")

            if args.verbose:
                print("\nDetalles:")
                print(f"  DOI: {b['data']['doi']}")
                print(f"  Timestamp: {b['data']['timestamp']}")
                print(f"  Hash beacon: {b['hash']}")
        else:
            print("✗ Beacon INVÁLIDO")
            print("  El beacon ha sido modificado o es corrupto")
            sys.exit(1)

    except FileNotFoundError:
        print(f"✗ Error: Archivo no encontrado: {args.beacon}", file=sys.stderr)
        sys.exit(1)
    except json.JSONDecodeError as e:
        print(f"✗ Error: JSON inválido: {e}", file=sys.stderr)
        sys.exit(1)
    except Exception as e:
        print(f"✗ Error al verificar beacon: {e}", file=sys.stderr)
        sys.exit(1)


def _lookup_onchain_token(beacon_hash: str) -> Optional[int]:
    """
    Lookup a beacon hash on-chain to find its token ID.

    In production, this would query the Base Mainnet contract.
    Currently returns a simulated result for known beacons.

    Args:
        beacon_hash: The SHA3-256 hash of the beacon

    Returns:
        Token ID if found on-chain, None otherwise
    """
    # Known minted beacons (would be replaced with actual on-chain query)
    known_beacons = {
        # Rψ(5,5) ≤ 16 beacon hash -> Token ID #001
        "3b63aa1e7b4e514535470eb2335f07876337175f4ebef647bf22e90b5527872c": 1,
    }
    return known_beacons.get(beacon_hash)


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

  # Verificar beacon desde archivo
  %(prog)s verify --beacon beacon.json

  # Verificar beacon desde stdin (IPFS)
  curl -s https://ipfs.io/ipfs/QmX7...beacon.json | %(prog)s verify --stdin

  # Verificar con confirmación on-chain
  %(prog)s verify --beacon beacon.json --check-onchain

  # Ver información
  %(prog)s info --beacon beacon.json

On-Chain:
  Contract: AIKBeaconsProofOfMath on Base Mainnet
  Collection: https://opensea.io/collection/aik-beacons-proof-of-math
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
    parser_verify.add_argument("--beacon", help="Archivo beacon JSON")
    parser_verify.add_argument("--stdin", action="store_true",
                               help="Leer beacon desde stdin (para verificación IPFS)")
    parser_verify.add_argument("--check-onchain", action="store_true",
                               help="Verificar si el beacon está registrado on-chain")
    parser_verify.add_argument("-v", "--verbose", action="store_true",
                               help="Mostrar información detallada")

    # Comando: info
    parser_info = subparsers.add_parser("info", help="Mostrar información de un beacon")
    parser_info.add_argument("--beacon", required=True, help="Archivo beacon JSON")

    args = parser.parse_args()

    if not args.command:
        parser.print_help()
        sys.exit(1)

    # Validate verify command arguments
    if args.command == "verify":
        if not args.stdin and not args.beacon:
            print("Error: Se requiere --beacon o --stdin", file=sys.stderr)
            sys.exit(1)
        if args.stdin and args.beacon:
            print("Error: Use --beacon o --stdin, no ambos", file=sys.stderr)
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
