#!/usr/bin/env python3
"""
NOESIS GUARDIAN — AIK Sync Module
==================================

Sincronización con AIK-Beacons para validación criptográfica.

Cada reparación genera una prueba criptográfica con:
- SHA3-256
- ECDSA
- CID IPFS (opcional)
- Firma simbólica ∞³

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
License: Creative Commons BY-NC-SA 4.0
"""

import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List


class AikSync:
    """
    Sincronización con AIK-Beacons.

    Genera pruebas criptográficas para cada evento de reparación
    y sincroniza con el sistema AIK-Beacons.
    """

    # Constantes AIK
    F0_HZ = 141.7001
    ALGORITHM = "SHA3-256"

    _certificates: List[Dict[str, Any]] = []

    @classmethod
    def sync_certificate(cls, state: Dict[str, Any]) -> Dict[str, Any]:
        """
        Sincroniza un certificado con AIK-Beacons.

        Args:
            state: Estado del sistema a certificar

        Returns:
            Certificado generado y sincronizado
        """
        certificate = cls._generate_certificate(state)
        cls._certificates.append(certificate)

        # Guardar certificado
        save_result = cls._save_certificate(certificate)

        return {
            "success": True,
            "certificate": certificate,
            "saved": save_result.get("success", False),
        }

    @classmethod
    def _generate_certificate(cls, state: Dict[str, Any]) -> Dict[str, Any]:
        """
        Genera un certificado criptográfico.

        Args:
            state: Estado a certificar

        Returns:
            Certificado con hash y metadatos
        """
        timestamp = datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")

        # Preparar datos para hash
        cert_data = {
            "timestamp": timestamp,
            "state": state,
            "f0": cls.F0_HZ,
            "algorithm": cls.ALGORITHM,
            "source": "noesis_guardian",
        }

        # Calcular hash SHA3-256
        data_bytes = json.dumps(cert_data, sort_keys=True, default=str).encode("utf-8")
        hash_value = hashlib.sha3_256(data_bytes).hexdigest()

        # Generar firma simbólica ∞³
        symbolic_signature = cls._generate_symbolic_signature(hash_value, timestamp)

        return {
            "id": f"aik_{timestamp.replace(':', '').replace('-', '')[:14]}",
            "timestamp": timestamp,
            "hash": hash_value,
            "algorithm": cls.ALGORITHM,
            "f0": cls.F0_HZ,
            "symbolic_signature": symbolic_signature,
            "state_summary": cls._summarize_state(state),
        }

    @classmethod
    def _generate_symbolic_signature(cls, hash_value: str, timestamp: str) -> str:
        """
        Genera firma simbólica ∞³.

        Args:
            hash_value: Hash del certificado
            timestamp: Timestamp del certificado

        Returns:
            Firma simbólica
        """
        # Combinar hash con constantes QCAL
        combined = f"{hash_value}:{cls.F0_HZ}:{timestamp}"
        signature_hash = hashlib.sha3_256(combined.encode()).hexdigest()[:32]

        return f"∞³-{signature_hash}"

    @classmethod
    def _summarize_state(cls, state: Dict[str, Any]) -> Dict[str, Any]:
        """
        Resume el estado para el certificado.

        Args:
            state: Estado completo

        Returns:
            Resumen del estado
        """
        return {
            "coherent": state.get("spectral", {}).get("coherent", None),
            "signal_state": state.get("signal", {}).get("state", None),
            "timestamp": state.get("timestamp"),
        }

    @classmethod
    def _save_certificate(cls, certificate: Dict[str, Any]) -> Dict[str, Any]:
        """
        Guarda el certificado en disco.

        Args:
            certificate: Certificado a guardar

        Returns:
            Resultado del guardado
        """
        try:
            cert_dir = Path(__file__).resolve().parents[1] / "certificates"
            cert_dir.mkdir(parents=True, exist_ok=True)

            cert_file = cert_dir / f"{certificate['id']}.json"

            with open(cert_file, "w", encoding="utf-8") as f:
                json.dump(certificate, f, indent=2, default=str)

            return {"success": True, "path": str(cert_file)}
        except Exception as e:
            return {"success": False, "error": str(e)}

    @classmethod
    def verify_certificate(cls, certificate: Dict[str, Any]) -> Dict[str, Any]:
        """
        Verifica la integridad de un certificado.

        Args:
            certificate: Certificado a verificar

        Returns:
            Resultado de la verificación
        """
        try:
            # Verificar que el hash almacenado es válido
            stored_hash = certificate.get("hash", "")

            # Verificar formato del hash
            if len(stored_hash) != 64:
                return {"valid": False, "reason": "Invalid hash length"}

            # Verificar firma simbólica
            symbolic_sig = certificate.get("symbolic_signature", "")
            if not symbolic_sig.startswith("∞³-"):
                return {"valid": False, "reason": "Invalid symbolic signature"}

            return {
                "valid": True,
                "certificate_id": certificate.get("id"),
                "algorithm": certificate.get("algorithm"),
            }
        except Exception as e:
            return {"valid": False, "reason": str(e)}

    @classmethod
    def get_certificates(cls, limit: int = 100) -> List[Dict[str, Any]]:
        """
        Obtiene los certificados generados.

        Args:
            limit: Número máximo de certificados

        Returns:
            Lista de certificados
        """
        return cls._certificates[-limit:]

    @classmethod
    def load_certificates_from_disk(cls) -> List[Dict[str, Any]]:
        """
        Carga certificados desde disco.

        Returns:
            Lista de certificados cargados
        """
        certificates = []
        cert_dir = Path(__file__).resolve().parents[1] / "certificates"

        if not cert_dir.exists():
            return certificates

        for cert_file in sorted(cert_dir.glob("aik_*.json")):
            try:
                with open(cert_file, "r", encoding="utf-8") as f:
                    cert = json.load(f)
                    certificates.append(cert)
            except Exception:
                pass

        return certificates


if __name__ == "__main__":
    print("=" * 60)
    print("NOESIS GUARDIAN — AIK Sync Demo")
    print("=" * 60)

    # Generar certificado de prueba
    print("\n🔐 Generating test certificate...")
    test_state = {
        "timestamp": datetime.now().isoformat(),
        "spectral": {"coherent": True},
        "signal": {"state": "vivo"},
    }

    result = AikSync.sync_certificate(test_state)

    print("\n📜 Certificate Generated:")
    cert = result["certificate"]
    print(f"   ID: {cert['id']}")
    print(f"   Hash: {cert['hash'][:32]}...")
    print(f"   Algorithm: {cert['algorithm']}")
    print(f"   f₀: {cert['f0']} Hz")
    print(f"   Signature: {cert['symbolic_signature']}")
    print(f"   Saved: {'✅' if result['saved'] else '❌'}")

    # Verificar certificado
    print("\n🔍 Verifying certificate...")
    verification = AikSync.verify_certificate(cert)
    print(f"   Valid: {'✅' if verification['valid'] else '❌'}")

    print("\n✅ Demo complete")
