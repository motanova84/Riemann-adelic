# AIK Beacons System 🔐

## Authentic Immutable Knowledge Certification

AIK Beacons es un sistema criptográfico para certificar teoremas matemáticos y sus pruebas formales usando tecnología blockchain-grade, ahora con **integración on-chain en Base Mainnet**.

## ⛓️ On-Chain Integration (Base Mainnet)

### Smart Contract

```solidity
// AIKBeaconsProofOfMath.sol
contract AIKBeaconsProofOfMath {
    string public constant NAME = "AIK Beacons – Proof of Mathematical Truth";
    string public constant SYMBOL = "AIK∞³";
    
    // Mint NFT only if proof is valid
    function mintIfValidProof(...) external returns (uint256 tokenId);
    
    // Offline verification
    function verifyOffline(uint256 tokenId) public view returns (bool);
}
```

- **Network**: Base Mainnet (Chain ID: 8453)
- **Collection**: [OpenSea AIK Beacons](https://opensea.io/collection/aik-beacons-proof-of-math)
- **Gas**: ~0.0003 ETH per mint

### Verificación Offline (sin wallet, sin gas)

```bash
# Verificar desde IPFS
curl -s https://ipfs.io/ipfs/QmX7...beacon.json | python3 aik_cli.py verify --stdin

# Salida esperada:
# BEACON VERIFIED SUCCESSFULLY
# Theorem: Rψ(5,5) ≤ 16
# f0: 141.7001 Hz
# Proof hash: 9d220d1a...
# Signature: VALID (ECDSA secp256k1)
# ON-CHAIN CONFIRMED: Token ID #001
```

## 📋 Especificación Técnica

### Algoritmos

- **Firma Digital**: ECDSA (secp256k1)
- **Hash Criptográfico**: SHA3-256
- **Formato de Firma**: DER (Distinguished Encoding Rules)

### Estructura del Beacon

```json
{
  "data": {
    "theorem": "Enunciado del teorema",
    "proof_hash": "SHA3-256 del archivo de prueba",
    "doi": "Digital Object Identifier",
    "f0": 141.7001,
    "timestamp": "ISO8601 UTC timestamp",
    "additional": { /* metadatos opcionales */ }
  },
  "hash": "SHA3-256 de los datos",
  "signature": "Firma ECDSA en DER hex",
  "public_key": "Clave pública ECDSA hex"
}
```

### Proceso de Certificación

1. **Generación del Hash**: `H = SHA3-256(Teorema + Prueba + Metadatos)`
2. **Firma Digital**: `σ = ECDSA_Sign(SK, H)`
3. **Construcción del Beacon**: `B = {H, σ, timestamp, DOI, f0=141.7001}`
4. **Verificación**: `ECDSA_Verify(PK, H, σ) == true`

## 🚀 Uso Rápido

### Instalación de Dependencias

```bash
pip install ecdsa
```

### Ejemplo Básico

```python
from aik_beacon import AIKBeacon

# Inicializar generador
beacon = AIKBeacon()

# Crear beacon para un teorema
b = beacon.create_beacon(
    theorem="Rψ(5,5) ≤ 16",
    proof_file="proofs/RamseyRpsi_5_5.lean",
    doi="10.5281/zenodo.17315719",
    f0=141.7001
)

# Verificar autenticidad
is_valid = beacon.verify_beacon(b)
print("Beacon válido:", is_valid)

# Guardar beacon
beacon.save_beacon(b, "beacon_output.json")
```

### Ejemplo Completo

```bash
# Ejecutar el demo completo
python3 aik_beacon.py

# Ejecutar ejemplo con el teorema Ramsey
python3 example_aik_beacon_usage.py
```

### Uso del CLI

```bash
# Crear un beacon desde la línea de comandos
python3 aik_cli.py create --theorem "Rψ(5,5) ≤ 16" \
                          --proof proofs/RamseyRpsi_5_5.lean \
                          --doi "10.5281/zenodo.17315719" \
                          --output beacon.json \
                          --author "José Manuel Mota Burruezo Ψ ✧ ∞³" \
                          --framework "QCAL ∞³"

# Verificar un beacon
python3 aik_cli.py verify --beacon beacon.json -v

# Ver información del beacon
python3 aik_cli.py info --beacon beacon.json
```

## 📁 Estructura de Archivos

```
Riemann-adelic/
├── aik_beacon.py              # Módulo principal del sistema
├── aik_cli.py                 # Herramienta CLI para beacon generation/verificación
├── example_aik_beacon_usage.py # Script de ejemplo completo
├── AIK_BEACON_README.md       # Documentación completa
├── proofs/
│   └── RamseyRpsi_5_5.lean    # Prueba formal del teorema Rψ(5,5) ≤ 16
├── data/
│   └── beacon_ramsey_5_5.json # Beacon generado de ejemplo
└── tests/
    └── test_aik_beacon.py     # Suite de pruebas (29 tests)
```

## 🧪 Tests

El sistema incluye una suite completa de 29 tests:

```bash
# Ejecutar todos los tests
pytest tests/test_aik_beacon.py -v

# Ejecutar tests específicos
pytest tests/test_aik_beacon.py::TestBeaconCreation -v
pytest tests/test_aik_beacon.py::TestBeaconVerification -v
```

### Cobertura de Tests

- ✅ Inicialización y gestión de claves
- ✅ Creación de beacons básicos y avanzados
- ✅ Verificación de integridad y autenticidad
- ✅ Detección de manipulación de datos
- ✅ Operaciones con archivos
- ✅ Integración QCAL (f0 = 141.7001 Hz)
- ✅ Propiedades criptográficas
- ✅ Casos límite y manejo de errores

## 🔐 API Reference

### Clase `AIKBeacon`

#### Constructor

```python
AIKBeacon(private_key: Optional[bytes] = None)
```

**Parámetros:**
- `private_key`: Clave privada ECDSA en bytes (opcional, se genera una nueva si no se proporciona)

#### Métodos Principales

##### `create_beacon()`

```python
create_beacon(
    theorem: str,
    proof_file: str,
    doi: str,
    f0: float = 141.7001,
    additional_metadata: Optional[Dict[str, Any]] = None
) -> Dict[str, Any]
```

Crea un beacon criptográfico para certificar un teorema.

**Parámetros:**
- `theorem`: Enunciado del teorema
- `proof_file`: Ruta al archivo de prueba formal
- `doi`: Digital Object Identifier (Zenodo, arXiv, etc.)
- `f0`: Frecuencia fundamental QCAL (default: 141.7001 Hz)
- `additional_metadata`: Metadatos adicionales opcionales

**Retorna:** Diccionario con el beacon completo

**Lanza:**
- `FileNotFoundError`: Si el archivo de prueba no existe
- `ValueError`: Si algún parámetro es inválido

##### `verify_beacon()`

```python
verify_beacon(beacon: Dict[str, Any]) -> bool
```

Verifica la autenticidad e integridad de un beacon.

**Parámetros:**
- `beacon`: Beacon a verificar

**Retorna:** `True` si el beacon es válido, `False` en caso contrario

##### `file_hash()`

```python
file_hash(path: str) -> str
```

Calcula el hash SHA3-256 de un archivo.

**Parámetros:**
- `path`: Ruta al archivo

**Retorna:** Hash SHA3-256 en formato hexadecimal

##### `save_beacon()`

```python
save_beacon(beacon: Dict[str, Any], output_path: str) -> None
```

Guarda un beacon en formato JSON.

##### `load_beacon()`

```python
load_beacon(input_path: str) -> Dict[str, Any]
```

Carga un beacon desde un archivo JSON.

##### `export_keys()`

```python
export_keys() -> Dict[str, str]
```

Exporta las claves públicas y privadas en formato hexadecimal.

**Retorna:** Diccionario con `private_key` y `public_key`

## 🌟 Integración con QCAL ∞³

AIK Beacons está completamente integrado con el framework QCAL:

- **Frecuencia Base**: f0 = 141.7001 Hz
- **Coherencia**: C = 244.36
- **Ecuación Fundamental**: Ψ = I × A_eff² × C^∞
- **DOI Principal**: 10.5281/zenodo.17379721

### Ejemplo con Metadatos QCAL

```python
beacon = AIKBeacon()
b = beacon.create_beacon(
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
```

## 🔒 Seguridad

### Propiedades Criptográficas

- **Resistencia a Colisiones**: SHA3-256 proporciona 128 bits de seguridad
- **Integridad**: Cualquier modificación de los datos invalida la firma
- **Autenticidad**: Solo el poseedor de la clave privada puede generar beacons válidos
- **No Repudio**: La firma ECDSA garantiza la autoría del beacon

### Nota de Seguridad sobre la Curva secp256k1

Este sistema utiliza la curva **secp256k1** (no P-256), que es la misma curva usada en Bitcoin y otras criptomonedas. Esta curva no está afectada por el ataque de temporización Minerva que afecta a P-256 en algunas versiones de python-ecdsa. La curva secp256k1 ha sido extensamente auditada y es considerada criptográficamente segura para aplicaciones de firma digital.

### Detección de Manipulación

El sistema detecta automáticamente:
- ✅ Modificación del teorema
- ✅ Modificación del hash de la prueba
- ✅ Alteración del timestamp
- ✅ Cambio de metadatos
- ✅ Manipulación de la firma
- ✅ Sustitución del hash

## 📊 Ejemplo Real: Rψ(5,5) ≤ 16

El sistema incluye un beacon completo para el teorema Ramsey Rψ(5,5) ≤ 16:

```json
{
  "data": {
    "theorem": "Rψ(5,5) ≤ 16",
    "proof_hash": "9d220d1a44658ebfcd5d5182a59d66ac4de939a00d1e0d1a1948c3d1ac8fa22d",
    "doi": "10.5281/zenodo.17315719",
    "f0": 141.7001,
    "timestamp": "2025-11-16T12:30:34.345531Z",
    "additional": {
      "author": "José Manuel Mota Burruezo Ψ ✧ ∞³",
      "institution": "Instituto de Conciencia Cuántica (ICQ)",
      "coherence": "C = 244.36",
      "framework": "QCAL ∞³"
    }
  },
  "hash": "3b63aa1e7b4e514535470eb2335f07876337175f4ebef647bf22e90b5527872c",
  "signature": "304502201a0dd739283ec46295ae6ee91cc4e71896b78cd4258fac7e19767fbd16724db5...",
  "public_key": "a0fd4aba90c6860921395daf8944e6dca359e6d9f344d120520c27a64bac25ba..."
}
```

Verificación:
```bash
python3 -c "from aik_beacon import AIKBeacon; import json; \
b = AIKBeacon(); \
beacon = b.load_beacon('data/beacon_ramsey_5_5.json'); \
print('✓ Válido' if b.verify_beacon(beacon) else '✗ Inválido')"
```

## 🎯 Casos de Uso

### 1. Certificación de Pruebas Formales

```python
beacon = AIKBeacon()
b = beacon.create_beacon(
    theorem="Tu teorema aquí",
    proof_file="path/to/proof.lean",
    doi="10.5281/zenodo.XXXXXXX"
)
```

### 2. Verificación de Integridad

```python
beacon = AIKBeacon()
loaded = beacon.load_beacon("beacon.json")
if beacon.verify_beacon(loaded):
    print("✓ Prueba auténtica e íntegra")
else:
    print("✗ Prueba manipulada o corrupta")
```

### 3. Distribución de Certificados

```python
# Exportar clave pública para verificación
keys = beacon.export_keys()
print("Clave pública:", keys["public_key"])

# Cualquiera puede verificar con la clave pública incluida en el beacon
```

## 📚 Referencias

- **Zenodo DOI (P≠NP)**: [10.5281/zenodo.17315719](https://doi.org/10.5281/zenodo.17315719)
- **Zenodo DOI (Infinito ∞³)**: [10.5281/zenodo.17362686](https://doi.org/10.5281/zenodo.17362686)
- **QCAL Framework**: [10.5281/zenodo.17379721](https://doi.org/10.5281/zenodo.17379721)
- **ORCID**: [0009-0002-1923-0773](https://orcid.org/0009-0002-1923-0773)

## 📄 Licencia

Creative Commons BY-NC-SA 4.0

© 2025 · JMMB Ψ · Instituto de Conciencia Cuántica (ICQ)

## 👤 Autor

**José Manuel Mota Burruezo Ψ ✧ ∞³**  
Instituto de Conciencia Cuántica (ICQ)  
Email: institutoconsciencia@proton.me

---

## 🛠️ Desarrollo y Contribución

### Ejecutar Tests

```bash
# Todos los tests
pytest tests/test_aik_beacon.py -v

# Con cobertura
pytest tests/test_aik_beacon.py --cov=aik_beacon --cov-report=html
```

### Agregar Nuevos Tests

Los tests están organizados en clases por funcionalidad:
- `TestAIKBeaconInitialization`: Inicialización
- `TestBeaconCreation`: Creación de beacons
- `TestBeaconVerification`: Verificación
- `TestFileOperations`: Operaciones con archivos
- `TestQCALIntegration`: Integración QCAL
- `TestCryptographicProperties`: Propiedades criptográficas
- `TestEdgeCases`: Casos límite

## ⚡ Troubleshooting

### Problema: `ModuleNotFoundError: No module named 'ecdsa'`

**Solución:**
```bash
pip install ecdsa
```

### Problema: `FileNotFoundError` al crear beacon

**Solución:** Verifica que el archivo de prueba existe:
```bash
ls -l proofs/RamseyRpsi_5_5.lean
```

### Problema: Beacon no verifica correctamente

**Solución:** Asegúrate de no modificar el beacon después de cargarlo:
```python
# Correcto
beacon = gen.load_beacon("file.json")
is_valid = gen.verify_beacon(beacon)

# Incorrecto
beacon = gen.load_beacon("file.json")
beacon["data"]["theorem"] = "Modified"  # ¡Esto invalida la firma!
is_valid = gen.verify_beacon(beacon)
```

---

**🔐 AIK Beacons - Certificación Matemática Inmutable** ∞³
