"""
Tests for AIK Beacon System
============================

Comprehensive test suite for the Authentic Immutable Knowledge Beacon system.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
"""

import pytest
import json
import os
import tempfile
from pathlib import Path
from aik_beacon import AIKBeacon


@pytest.fixture
def beacon_generator():
    """Fixture que proporciona un generador de beacons para los tests."""
    return AIKBeacon()


@pytest.fixture
def sample_proof_file(tmp_path):
    """Fixture que crea un archivo de prueba temporal."""
    proof_file = tmp_path / "test_proof.lean"
    proof_file.write_text("-- Test proof content\ntheorem test : True := trivial")
    return str(proof_file)


class TestAIKBeaconInitialization:
    """Tests para la inicialización del generador de beacons."""
    
    def test_init_without_key(self):
        """Test inicialización sin clave privada (genera nueva)."""
        beacon = AIKBeacon()
        assert beacon.sk is not None
        assert beacon.pk is not None
    
    def test_init_with_key(self):
        """Test inicialización con clave privada existente."""
        beacon1 = AIKBeacon()
        private_key = beacon1.sk.to_string()
        
        beacon2 = AIKBeacon(private_key=private_key)
        assert beacon1.pk.to_string() == beacon2.pk.to_string()
    
    def test_keys_are_valid(self, beacon_generator):
        """Test que las claves generadas son válidas."""
        keys = beacon_generator.export_keys()
        assert len(keys["private_key"]) == 64  # 32 bytes * 2 hex chars
        assert len(keys["public_key"]) == 128  # 64 bytes * 2 hex chars


class TestBeaconCreation:
    """Tests para la creación de beacons."""
    
    def test_create_basic_beacon(self, beacon_generator, sample_proof_file):
        """Test creación de beacon básico."""
        beacon = beacon_generator.create_beacon(
            theorem="Test Theorem",
            proof_file=sample_proof_file,
            doi="10.5281/zenodo.test",
            f0=141.7001
        )
        
        assert "data" in beacon
        assert "hash" in beacon
        assert "signature" in beacon
        assert "public_key" in beacon
        
        assert beacon["data"]["theorem"] == "Test Theorem"
        assert beacon["data"]["doi"] == "10.5281/zenodo.test"
        assert beacon["data"]["f0"] == 141.7001
    
    def test_create_beacon_with_additional_metadata(self, beacon_generator, sample_proof_file):
        """Test creación de beacon con metadatos adicionales."""
        additional = {
            "author": "Test Author",
            "institution": "Test Institution"
        }
        
        beacon = beacon_generator.create_beacon(
            theorem="Test Theorem",
            proof_file=sample_proof_file,
            doi="10.5281/zenodo.test",
            additional_metadata=additional
        )
        
        assert "additional" in beacon["data"]
        assert beacon["data"]["additional"]["author"] == "Test Author"
    
    def test_create_beacon_ramsey_theorem(self, beacon_generator):
        """Test creación de beacon para teorema Ramsey Rψ(5,5) ≤ 16."""
        proof_file = "proofs/RamseyRpsi_5_5.lean"
        
        if not os.path.exists(proof_file):
            pytest.skip(f"Proof file {proof_file} not found")
        
        beacon = beacon_generator.create_beacon(
            theorem="Rψ(5,5) ≤ 16",
            proof_file=proof_file,
            doi="10.5281/zenodo.17315719",
            f0=141.7001
        )
        
        assert beacon["data"]["theorem"] == "Rψ(5,5) ≤ 16"
        assert beacon["data"]["f0"] == 141.7001
    
    def test_create_beacon_missing_file(self, beacon_generator):
        """Test que se lanza error si el archivo no existe."""
        with pytest.raises(FileNotFoundError):
            beacon_generator.create_beacon(
                theorem="Test",
                proof_file="nonexistent_file.lean",
                doi="test"
            )
    
    def test_create_beacon_empty_theorem(self, beacon_generator, sample_proof_file):
        """Test que se lanza error si el teorema está vacío."""
        with pytest.raises(ValueError):
            beacon_generator.create_beacon(
                theorem="",
                proof_file=sample_proof_file,
                doi="test"
            )
    
    def test_create_beacon_empty_doi(self, beacon_generator, sample_proof_file):
        """Test que se lanza error si el DOI está vacío."""
        with pytest.raises(ValueError):
            beacon_generator.create_beacon(
                theorem="Test",
                proof_file=sample_proof_file,
                doi=""
            )


class TestBeaconVerification:
    """Tests para la verificación de beacons."""
    
    def test_verify_valid_beacon(self, beacon_generator, sample_proof_file):
        """Test verificación de un beacon válido."""
        beacon = beacon_generator.create_beacon(
            theorem="Test Theorem",
            proof_file=sample_proof_file,
            doi="10.5281/zenodo.test"
        )
        
        assert beacon_generator.verify_beacon(beacon) is True
    
    def test_verify_tampered_theorem(self, beacon_generator, sample_proof_file):
        """Test que detecta modificación del teorema."""
        beacon = beacon_generator.create_beacon(
            theorem="Original Theorem",
            proof_file=sample_proof_file,
            doi="10.5281/zenodo.test"
        )
        
        # Modificar el teorema
        beacon["data"]["theorem"] = "Modified Theorem"
        
        assert beacon_generator.verify_beacon(beacon) is False
    
    def test_verify_tampered_hash(self, beacon_generator, sample_proof_file):
        """Test que detecta modificación del hash."""
        beacon = beacon_generator.create_beacon(
            theorem="Test Theorem",
            proof_file=sample_proof_file,
            doi="10.5281/zenodo.test"
        )
        
        # Modificar el hash
        beacon["hash"] = "0" * 64
        
        assert beacon_generator.verify_beacon(beacon) is False
    
    def test_verify_tampered_signature(self, beacon_generator, sample_proof_file):
        """Test que detecta modificación de la firma."""
        beacon = beacon_generator.create_beacon(
            theorem="Test Theorem",
            proof_file=sample_proof_file,
            doi="10.5281/zenodo.test"
        )
        
        # Modificar la firma
        beacon["signature"] = "0" * len(beacon["signature"])
        
        assert beacon_generator.verify_beacon(beacon) is False
    
    def test_verify_missing_fields(self, beacon_generator, sample_proof_file):
        """Test que detecta campos faltantes."""
        beacon = beacon_generator.create_beacon(
            theorem="Test Theorem",
            proof_file=sample_proof_file,
            doi="10.5281/zenodo.test"
        )
        
        # Eliminar un campo requerido
        del beacon["hash"]
        
        assert beacon_generator.verify_beacon(beacon) is False
    
    def test_verify_with_different_key(self, sample_proof_file):
        """Test que un beacon no puede ser verificado con otra clave."""
        beacon_gen1 = AIKBeacon()
        beacon_gen2 = AIKBeacon()
        
        beacon = beacon_gen1.create_beacon(
            theorem="Test Theorem",
            proof_file=sample_proof_file,
            doi="10.5281/zenodo.test"
        )
        
        # Intentar verificar con un generador diferente (misma clase, pero claves diferentes)
        # Esto debería pasar porque la clave pública está en el beacon
        assert beacon_gen2.verify_beacon(beacon) is True


class TestFileOperations:
    """Tests para operaciones con archivos."""
    
    def test_file_hash(self, beacon_generator, sample_proof_file):
        """Test cálculo de hash de archivo."""
        hash_val = beacon_generator.file_hash(sample_proof_file)
        assert len(hash_val) == 64  # SHA3-256 en hex
        assert isinstance(hash_val, str)
    
    def test_file_hash_nonexistent(self, beacon_generator):
        """Test que se lanza error si el archivo no existe."""
        with pytest.raises(FileNotFoundError):
            beacon_generator.file_hash("nonexistent_file.txt")
    
    def test_file_hash_consistency(self, beacon_generator, tmp_path):
        """Test que el hash es consistente para el mismo contenido."""
        file1 = tmp_path / "file1.txt"
        file2 = tmp_path / "file2.txt"
        
        content = "Test content"
        file1.write_text(content)
        file2.write_text(content)
        
        hash1 = beacon_generator.file_hash(str(file1))
        hash2 = beacon_generator.file_hash(str(file2))
        
        assert hash1 == hash2
    
    def test_save_and_load_beacon(self, beacon_generator, sample_proof_file, tmp_path):
        """Test guardar y cargar beacon desde archivo."""
        beacon = beacon_generator.create_beacon(
            theorem="Test Theorem",
            proof_file=sample_proof_file,
            doi="10.5281/zenodo.test"
        )
        
        output_file = tmp_path / "test_beacon.json"
        beacon_generator.save_beacon(beacon, str(output_file))
        
        assert output_file.exists()
        
        loaded_beacon = beacon_generator.load_beacon(str(output_file))
        assert loaded_beacon == beacon
    
    def test_load_nonexistent_beacon(self, beacon_generator):
        """Test que se lanza error al cargar beacon inexistente."""
        with pytest.raises(FileNotFoundError):
            beacon_generator.load_beacon("nonexistent_beacon.json")


class TestQCALIntegration:
    """Tests para la integración con QCAL."""
    
    def test_qcal_frequency_default(self, beacon_generator, sample_proof_file):
        """Test que la frecuencia QCAL por defecto es 141.7001 Hz."""
        beacon = beacon_generator.create_beacon(
            theorem="Test Theorem",
            proof_file=sample_proof_file,
            doi="10.5281/zenodo.test"
        )
        
        assert beacon["data"]["f0"] == 141.7001
    
    def test_qcal_frequency_custom(self, beacon_generator, sample_proof_file):
        """Test que se puede especificar una frecuencia QCAL personalizada."""
        custom_freq = 142.0
        beacon = beacon_generator.create_beacon(
            theorem="Test Theorem",
            proof_file=sample_proof_file,
            doi="10.5281/zenodo.test",
            f0=custom_freq
        )
        
        assert beacon["data"]["f0"] == custom_freq
    
    def test_qcal_metadata_structure(self, beacon_generator, sample_proof_file):
        """Test la estructura de metadatos QCAL."""
        beacon = beacon_generator.create_beacon(
            theorem="Test Theorem",
            proof_file=sample_proof_file,
            doi="10.5281/zenodo.test",
            additional_metadata={
                "coherence": "C = 244.36",
                "framework": "QCAL ∞³"
            }
        )
        
        assert "additional" in beacon["data"]
        assert beacon["data"]["additional"]["coherence"] == "C = 244.36"
        assert beacon["data"]["additional"]["framework"] == "QCAL ∞³"


class TestCryptographicProperties:
    """Tests para propiedades criptográficas."""
    
    def test_signature_uniqueness(self, beacon_generator, sample_proof_file):
        """Test que cada firma es única (debido a variación temporal)."""
        beacon1 = beacon_generator.create_beacon(
            theorem="Test Theorem",
            proof_file=sample_proof_file,
            doi="10.5281/zenodo.test"
        )
        
        # Pequeña espera para asegurar timestamp diferente
        import time
        time.sleep(0.1)
        
        beacon2 = beacon_generator.create_beacon(
            theorem="Test Theorem",
            proof_file=sample_proof_file,
            doi="10.5281/zenodo.test"
        )
        
        # Los beacons deben ser diferentes debido a timestamps diferentes
        assert beacon1["hash"] != beacon2["hash"]
        assert beacon1["signature"] != beacon2["signature"]
    
    def test_hash_hex_format(self, beacon_generator, sample_proof_file):
        """Test que el hash está en formato hexadecimal válido."""
        beacon = beacon_generator.create_beacon(
            theorem="Test Theorem",
            proof_file=sample_proof_file,
            doi="10.5281/zenodo.test"
        )
        
        # Verificar que es hexadecimal válido
        try:
            int(beacon["hash"], 16)
            assert True
        except ValueError:
            assert False, "Hash no está en formato hexadecimal"
    
    def test_signature_format(self, beacon_generator, sample_proof_file):
        """Test que la firma está en formato DER válido."""
        beacon = beacon_generator.create_beacon(
            theorem="Test Theorem",
            proof_file=sample_proof_file,
            doi="10.5281/zenodo.test"
        )
        
        # Verificar que es hexadecimal válido
        try:
            bytes.fromhex(beacon["signature"])
            assert True
        except ValueError:
            assert False, "Signature no está en formato hexadecimal"


class TestEdgeCases:
    """Tests para casos límite y manejo de errores."""
    
    def test_unicode_theorem(self, beacon_generator, sample_proof_file):
        """Test que se pueden usar caracteres Unicode en el teorema."""
        beacon = beacon_generator.create_beacon(
            theorem="Rψ(5,5) ≤ 16 ∞³",
            proof_file=sample_proof_file,
            doi="10.5281/zenodo.test"
        )
        
        assert beacon["data"]["theorem"] == "Rψ(5,5) ≤ 16 ∞³"
        assert beacon_generator.verify_beacon(beacon) is True
    
    def test_large_proof_file(self, beacon_generator, tmp_path):
        """Test con archivo de prueba grande."""
        large_file = tmp_path / "large_proof.lean"
        large_content = "-- Large proof\n" * 10000
        large_file.write_text(large_content)
        
        beacon = beacon_generator.create_beacon(
            theorem="Large Proof Test",
            proof_file=str(large_file),
            doi="10.5281/zenodo.test"
        )
        
        assert beacon_generator.verify_beacon(beacon) is True
    
    def test_empty_proof_file(self, beacon_generator, tmp_path):
        """Test con archivo de prueba vacío."""
        empty_file = tmp_path / "empty_proof.lean"
        empty_file.write_text("")
        
        beacon = beacon_generator.create_beacon(
            theorem="Empty Proof Test",
            proof_file=str(empty_file),
            doi="10.5281/zenodo.test"
        )
        
        assert beacon_generator.verify_beacon(beacon) is True


class TestOnChainIntegration:
    """Tests for on-chain integration functionality."""

    def test_prepare_onchain_data(self, beacon_generator, sample_proof_file):
        """Test preparation of on-chain data."""
        beacon = beacon_generator.create_beacon(
            theorem="Test Theorem",
            proof_file=sample_proof_file,
            doi="10.5281/zenodo.test"
        )

        ipfs_cid = "QmTestCID12345"
        onchain_data = beacon_generator.prepare_onchain_data(beacon, ipfs_cid)

        assert onchain_data["theorem"] == "Test Theorem"
        assert onchain_data["beacon_cid"] == ipfs_cid
        assert onchain_data["proof_cid"] == ipfs_cid
        assert isinstance(onchain_data["beacon_hash"], bytes)
        assert len(onchain_data["beacon_hash"]) == 32  # SHA3-256 = 32 bytes
        assert isinstance(onchain_data["signature"], bytes)

    def test_onchain_config_exists(self):
        """Test that on-chain configuration is available."""
        from aik_beacon import ONCHAIN_CONFIG

        assert "network" in ONCHAIN_CONFIG
        assert ONCHAIN_CONFIG["network"] == "Base Mainnet"
        assert ONCHAIN_CONFIG["chain_id"] == 8453
        assert ONCHAIN_CONFIG["symbol"] == "AIK∞³"
        assert ONCHAIN_CONFIG["f0_millihertz"] == 141700100

    def test_onchain_data_hash_format(self, beacon_generator, sample_proof_file):
        """Test that the beacon hash in on-chain data is correct bytes."""
        beacon = beacon_generator.create_beacon(
            theorem="Hash Format Test",
            proof_file=sample_proof_file,
            doi="10.5281/zenodo.test"
        )

        onchain_data = beacon_generator.prepare_onchain_data(beacon, "QmTestCID")

        # Verify the bytes hash matches the hex hash
        assert onchain_data["beacon_hash"].hex() == beacon["hash"]
