"""
AIK Beacons (Authentic Immutable Knowledge)
============================================

Sistema de certificación matemática usando:
- Firma: ECDSA (secp256k1) via cryptography library
- Hash: SHA3-256
- Timestamp: UTC ISO8601
- Frecuencia base: f0 = 141.7001 Hz (QCAL ∞³)

Formato de Beacon:
    B = {H, σ, timestamp, DOI, f0=141.7001}

Donde:
    H = SHA3-256(Teorema + Prueba + Metadatos)
    σ = ECDSA_Sign(SK, Data, SHA3-256)

Verificación:
    ECDSA_Verify(PK, Data, σ, SHA3-256) == true

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
License: Creative Commons BY-NC-SA 4.0
"""

from cryptography.hazmat.primitives.asymmetric import ec
from cryptography.hazmat.primitives import hashes, serialization
from cryptography.exceptions import InvalidSignature
import hashlib
import json
from datetime import datetime, timezone
from typing import Dict, Any, Optional
import os


class AIKBeacon:
    """
    Authentic Immutable Knowledge Beacon Generator and Verifier.

    Genera beacons criptográficos para certificar teoremas matemáticos
    y sus pruebas formales usando ECDSA + SHA3-256.

    Attributes:
        sk (ec.EllipticCurvePrivateKey): Clave privada ECDSA (secp256k1)
        pk (ec.EllipticCurvePublicKey): Clave pública ECDSA (secp256k1)
    """

    def __init__(self, private_key: Optional[bytes] = None):
        """
        Inicializa el generador de beacons.

        Args:
            private_key: Clave privada ECDSA en formato bytes (entero de 32 bytes big-endian).
                        Si no se proporciona, se genera una nueva clave.
        """
        if private_key:
            private_value = int.from_bytes(private_key, 'big')
            self.sk = ec.derive_private_key(private_value, ec.SECP256K1())
        else:
            self.sk = ec.generate_private_key(ec.SECP256K1())
        self.pk = self.sk.public_key()

    def create_beacon(
        self,
        theorem: str,
        proof_file: str,
        doi: str,
        f0: float = 141.7001,
        additional_metadata: Optional[Dict[str, Any]] = None
    ) -> Dict[str, Any]:
        """
        Crea un beacon criptográfico para un teorema y su prueba.

        Args:
            theorem: Enunciado del teorema (ej: "Rψ(5,5) ≤ 16")
            proof_file: Ruta al archivo de prueba formal (Lean, Coq, etc.)
            doi: Digital Object Identifier del trabajo (Zenodo, arXiv, etc.)
            f0: Frecuencia fundamental QCAL (default: 141.7001 Hz)
            additional_metadata: Metadatos adicionales opcionales

        Returns:
            Diccionario con el beacon completo:
            {
                "data": {metadatos del teorema},
                "hash": hash SHA3-256 en hexadecimal,
                "signature": firma ECDSA en hexadecimal,
                "public_key": clave pública en hexadecimal
            }

        Raises:
            FileNotFoundError: Si el archivo de prueba no existe
            ValueError: Si algún parámetro es inválido
        """
        if not os.path.exists(proof_file):
            raise FileNotFoundError(f"Proof file not found: {proof_file}")

        if not theorem or not doi:
            raise ValueError("Theorem and DOI are required")

        # Construir metadatos del beacon
        metadata = {
            "theorem": theorem,
            "proof_hash": self.file_hash(proof_file),
            "doi": doi,
            "f0": f0,
            "timestamp": datetime.now(timezone.utc).isoformat().replace('+00:00', 'Z')
        }

        # Añadir metadatos adicionales si existen
        if additional_metadata:
            metadata["additional"] = additional_metadata

        # Serializar y hashear los datos
        data = json.dumps(metadata, sort_keys=True).encode()
        hash_val = hashlib.sha3_256(data).digest()

        # Firmar los datos con ECDSA + SHA3-256
        signature = self.sk.sign(data, ec.ECDSA(hashes.SHA3_256()))

        # Construir el beacon completo
        beacon = {
            "data": metadata,
            "hash": hash_val.hex(),
            "signature": signature.hex(),
            "public_key": self._export_public_key()
        }

        return beacon

    def verify_beacon(self, beacon: Dict[str, Any]) -> bool:
        """
        Verifica la autenticidad e integridad de un beacon.

        Args:
            beacon: Beacon a verificar (diccionario con data, hash, signature, public_key)

        Returns:
            True si el beacon es válido, False en caso contrario

        Raises:
            ValueError: Si el formato del beacon es inválido
        """
        try:
            # Validar estructura del beacon
            required_keys = ["data", "hash", "signature", "public_key"]
            if not all(key in beacon for key in required_keys):
                raise ValueError(f"Beacon must contain: {required_keys}")

            # Reconstruir el hash de los datos
            data = json.dumps(beacon["data"], sort_keys=True).encode()
            hash_val = hashlib.sha3_256(data).digest()

            # Verificar que el hash coincide
            if hash_val.hex() != beacon["hash"]:
                return False

            # Recuperar la clave pública
            vk = self._import_public_key(beacon["public_key"])

            # Verificar la firma ECDSA
            signature = bytes.fromhex(beacon["signature"])
            try:
                vk.verify(signature, data, ec.ECDSA(hashes.SHA3_256()))
                return True
            except InvalidSignature:
                return False

        except Exception as e:
            # En caso de error en la verificación, el beacon es inválido
            print(f"Verification error: {e}")
            return False

    def file_hash(self, path: str) -> str:
        """
        Calcula el hash SHA3-256 de un archivo.

        Args:
            path: Ruta al archivo

        Returns:
            Hash SHA3-256 en formato hexadecimal

        Raises:
            FileNotFoundError: Si el archivo no existe
        """
        if not os.path.exists(path):
            raise FileNotFoundError(f"File not found: {path}")

        with open(path, "rb") as f:
            return hashlib.sha3_256(f.read()).hexdigest()

    def save_beacon(self, beacon: Dict[str, Any], output_path: str) -> None:
        """
        Guarda un beacon en formato JSON.

        Args:
            beacon: Beacon a guardar
            output_path: Ruta del archivo de salida
        """
        with open(output_path, "w", encoding="utf-8") as f:
            json.dump(beacon, f, indent=2, ensure_ascii=False)

    def load_beacon(self, input_path: str) -> Dict[str, Any]:
        """
        Carga un beacon desde un archivo JSON.

        Args:
            input_path: Ruta del archivo de beacon

        Returns:
            Diccionario con el beacon

        Raises:
            FileNotFoundError: Si el archivo no existe
            json.JSONDecodeError: Si el formato JSON es inválido
        """
        if not os.path.exists(input_path):
            raise FileNotFoundError(f"Beacon file not found: {input_path}")

        with open(input_path, "r", encoding="utf-8") as f:
            return json.load(f)

    def _export_public_key(self) -> str:
        """
        Exporta la clave pública como 64 bytes sin comprimir (x+y, sin prefijo 04).

        Returns:
            Clave pública en formato hexadecimal (64 bytes)
        """
        raw = self.pk.public_bytes(
            serialization.Encoding.X962,
            serialization.PublicFormat.UncompressedPoint
        )
        return raw[1:].hex()  # strip the 04 uncompressed-point prefix

    def _import_public_key(self, hex_key: str) -> ec.EllipticCurvePublicKey:
        """
        Importa una clave pública desde 64 bytes sin comprimir en formato hex.

        Args:
            hex_key: Clave pública en formato hexadecimal (64 bytes, sin prefijo 04)

        Returns:
            EllipticCurvePublicKey
        """
        raw = bytes.fromhex(hex_key)
        return ec.EllipticCurvePublicKey.from_encoded_point(ec.SECP256K1(), b'\x04' + raw)

    def export_keys(self) -> Dict[str, str]:
        """
        Exporta las claves públicas y privadas en formato hexadecimal.

        Returns:
            Diccionario con 'private_key' y 'public_key' en hex
        """
        private_value = self.sk.private_numbers().private_value
        return {
            "private_key": private_value.to_bytes(32, 'big').hex(),
            "public_key": self._export_public_key()
        }

    def prepare_onchain_data(self, beacon: Dict[str, Any], ipfs_cid: str) -> Dict[str, Any]:
        """
        Prepare beacon data for on-chain minting.

        Args:
            beacon: The beacon to prepare for on-chain
            ipfs_cid: The IPFS CID where the beacon JSON is stored

        Returns:
            Dictionary with data ready for smart contract minting
        """
        return {
            "theorem": beacon["data"]["theorem"],
            "proof_cid": ipfs_cid,  # IPFS CID of proof file
            "beacon_cid": ipfs_cid,  # IPFS CID of beacon JSON
            "beacon_hash": bytes.fromhex(beacon["hash"]),
            "signature": bytes.fromhex(beacon["signature"]),
            "public_key": beacon["public_key"],
        }


# On-chain contract configuration
ONCHAIN_CONFIG = {
    "network": "Base Mainnet",
    "chain_id": 8453,
    "contract_name": "AIKBeaconsProofOfMath",
    "symbol": "AIK∞³",
    "f0_millihertz": 141700100,  # 141.7001 Hz in millihertz
    "opensea_collection": "https://opensea.io/collection/aik-beacons-proof-of-math",
}


if __name__ == "__main__":
    # Ejemplo de uso: Generación de beacon para Rψ(5,5) ≤ 16
    print("=" * 60)
    print("AIK BEACON SYSTEM - DEMO")
    print("=" * 60)

    # Crear instancia del generador de beacons
    beacon_generator = AIKBeacon()

    # Crear un archivo de prueba de ejemplo si no existe
    proof_file = "proof_example.lean"
    if not os.path.exists(proof_file):
        with open(proof_file, "w") as f:
            f.write("-- Proof placeholder for Rψ(5,5) ≤ 16\n")
        print(f"\n✓ Created example proof file: {proof_file}")

    # Generar beacon para el teorema Rψ(5,5) ≤ 16
    beacon = beacon_generator.create_beacon(
        theorem="Rψ(5,5) ≤ 16",
        proof_file=proof_file,
        doi="10.5281/zenodo.17315719",
        f0=141.7001
    )

    print("\n" + "=" * 60)
    print("BEACON GENERADO:")
    print("=" * 60)
    print(json.dumps(beacon, indent=2))

    # Verificar el beacon
    print("\n" + "=" * 60)
    print("VERIFICACIÓN:")
    print("=" * 60)
    is_valid = beacon_generator.verify_beacon(beacon)
    print(f"✓ Beacon válido: {is_valid}")

    # Exportar claves
    print("\n" + "=" * 60)
    print("CLAVES EXPORTADAS:")
    print("=" * 60)
    keys = beacon_generator.export_keys()
    print(f"Private key (primeros 20 chars): {keys['private_key'][:20]}...")
    print(f"Public key (primeros 20 chars): {keys['public_key'][:20]}...")

    # Limpiar archivo de ejemplo
    if os.path.exists(proof_file):
        os.remove(proof_file)
        print("\n✓ Cleaned up example proof file")

    print("\n" + "=" * 60)
    print("✓ DEMO COMPLETADO")
    print("=" * 60)
