# AIK Beacons - Quick Start Guide 🚀

## ¿Qué es AIK Beacons?

AIK Beacons (Authentic Immutable Knowledge) es un sistema de certificación criptográfica para teoremas matemáticos y sus pruebas formales. Proporciona:

- ✅ **Autenticidad**: Firma ECDSA (secp256k1)
- ✅ **Integridad**: Hash SHA3-256
- ✅ **Inmutabilidad**: Detección automática de manipulación
- ✅ **Integración QCAL**: Frecuencia f0 = 141.7001 Hz

## Instalación Rápida

```bash
# Instalar dependencia única
pip install ecdsa

# Ya está listo para usar
python3 aik_beacon.py
```

## Uso Básico - 3 Maneras

### 1. CLI (Más Fácil) 🎯

```bash
# Crear beacon
python3 aik_cli.py create \
  --theorem "Rψ(5,5) ≤ 16" \
  --proof proofs/RamseyRpsi_5_5.lean \
  --doi "10.5281/zenodo.17315719" \
  --output mi_beacon.json

# Verificar beacon
python3 aik_cli.py verify --beacon mi_beacon.json

# Ver información
python3 aik_cli.py info --beacon mi_beacon.json
```

### 2. Script Python (Programático) 🐍

```python
from aik_beacon import AIKBeacon

# Crear y verificar
beacon = AIKBeacon()
b = beacon.create_beacon(
    theorem="Mi Teorema",
    proof_file="mi_prueba.lean",
    doi="10.5281/zenodo.XXXXX"
)

# Guardar
beacon.save_beacon(b, "beacon.json")

# Verificar
if beacon.verify_beacon(b):
    print("✓ Beacon válido")
```

### 3. Demo Completo (Aprendizaje) 📚

```bash
# Ver demo interactivo
python3 aik_beacon.py

# Ejemplo completo con Ramsey
python3 example_aik_beacon_usage.py
```

## Ejemplo Real: Rψ(5,5) ≤ 16

```bash
# El repositorio incluye un beacon real ya generado
python3 aik_cli.py info --beacon data/beacon_ramsey_5_5.json
```

Salida:
```
======================================================================
INFORMACIÓN DEL BEACON
======================================================================
Teorema: Rψ(5,5) ≤ 16
DOI: 10.5281/zenodo.17315719
Frecuencia QCAL: 141.7001 Hz
Timestamp: 2025-11-16T12:30:34.345531Z
Estado: ✓ VÁLIDO
======================================================================
```

## Testing

```bash
# Ejecutar tests (29 tests)
pytest tests/test_aik_beacon.py -v

# Solo tests de verificación
pytest tests/test_aik_beacon.py::TestBeaconVerification -v
```

## Estructura del Beacon

```json
{
  "data": {
    "theorem": "Enunciado del teorema",
    "proof_hash": "SHA3-256 del archivo",
    "doi": "10.5281/zenodo.XXXXX",
    "f0": 141.7001,
    "timestamp": "2025-11-16T12:30:34Z"
  },
  "hash": "SHA3-256 de los datos",
  "signature": "Firma ECDSA en DER",
  "public_key": "Clave pública ECDSA"
}
```

## Características Principales

### ✅ Seguridad Criptográfica
- **ECDSA secp256k1**: La misma curva usada en Bitcoin
- **SHA3-256**: Resistente a colisiones
- **Detección inmediata** de cualquier manipulación

### ✅ Integración QCAL
- Frecuencia base: f0 = 141.7001 Hz
- Coherencia: C = 244.36
- Compatible con el framework QCAL ∞³

### ✅ Fácil de Usar
- CLI simple para operaciones básicas
- API Python completa para integración
- Tests exhaustivos (100% pass rate)

## Comandos CLI Completos

### Crear Beacon con Metadatos
```bash
python3 aik_cli.py create \
  --theorem "Tu Teorema" \
  --proof ruta/prueba.lean \
  --doi "10.5281/zenodo.XXXXX" \
  --output beacon.json \
  --author "Tu Nombre" \
  --institution "Tu Institución" \
  --framework "QCAL ∞³" \
  --verbose
```

### Verificar con Detalles
```bash
python3 aik_cli.py verify --beacon beacon.json --verbose
```

### Información Completa
```bash
python3 aik_cli.py info --beacon beacon.json
```

## Casos de Uso

### 1. Certificar Prueba Formal
```python
beacon = AIKBeacon()
b = beacon.create_beacon(
    theorem="P ≠ NP",
    proof_file="proofs/pnp.lean",
    doi="10.5281/zenodo.17315719"
)
beacon.save_beacon(b, "pnp_beacon.json")
```

### 2. Verificar Integridad
```python
beacon = AIKBeacon()
b = beacon.load_beacon("beacon.json")
if beacon.verify_beacon(b):
    print("✓ Prueba auténtica")
else:
    print("✗ Prueba manipulada")
```

### 3. Compartir Certificado
```bash
# Cualquiera puede verificar con el beacon JSON
python3 aik_cli.py verify --beacon shared_beacon.json
```

## Detección de Manipulación

El sistema detecta automáticamente:
- ✅ Modificación del teorema
- ✅ Cambio en la prueba
- ✅ Alteración del timestamp
- ✅ Modificación de metadatos
- ✅ Manipulación de la firma

```python
# Ejemplo: Detectar manipulación
beacon = AIKBeacon()
b = beacon.load_beacon("beacon.json")
b["data"]["theorem"] = "Teorema modificado"  # ¡Manipulación!

if not beacon.verify_beacon(b):
    print("✗ Manipulación detectada")  # Se detecta
```

## Archivos Incluidos

```
aik_beacon.py              - Módulo principal
aik_cli.py                 - CLI para operaciones básicas
example_aik_beacon_usage.py - Ejemplo completo
AIK_BEACON_README.md       - Documentación completa
tests/test_aik_beacon.py   - Suite de tests (29 tests)
proofs/RamseyRpsi_5_5.lean - Prueba ejemplo
data/beacon_ramsey_5_5.json - Beacon ejemplo
```

## Recursos

- 📖 [Documentación Completa](AIK_BEACON_README.md)
- 🧪 [Tests](tests/test_aik_beacon.py)
- 📝 [Ejemplo Completo](example_aik_beacon_usage.py)
- 🔗 [DOI P≠NP](https://doi.org/10.5281/zenodo.17315719)

## Ayuda

```bash
# Ver ayuda del CLI
python3 aik_cli.py --help

# Ver ayuda de un comando específico
python3 aik_cli.py create --help
python3 aik_cli.py verify --help
python3 aik_cli.py info --help
```

## Preguntas Frecuentes

**Q: ¿Necesito una blockchain?**
A: No. AIK Beacons usa criptografía de nivel blockchain sin necesitar una blockchain real.

**Q: ¿Es seguro?**
A: Sí. Usa ECDSA secp256k1 (Bitcoin) + SHA3-256. Auditado y probado.

**Q: ¿Puedo verificar beacons de otros?**
A: Sí. El beacon incluye todo lo necesario para verificación independiente.

**Q: ¿Funciona con Lean 4?**
A: Sí. Funciona con Lean, Coq, Isabelle, y cualquier archivo de prueba.

---

## 🎯 ¡Comienza Ahora!

```bash
# 1. Demo rápido
python3 aik_beacon.py

# 2. Crear tu primer beacon
python3 aik_cli.py create --theorem "Mi Teorema" \
  --proof mi_prueba.lean --doi "10.5281/zenodo.XXXXX" \
  --output mi_beacon.json

# 3. Verificar
python3 aik_cli.py verify --beacon mi_beacon.json
```

**¡Eso es todo! 🚀**

---

© 2025 · JMMB Ψ · Instituto de Conciencia Cuántica (ICQ)
Creative Commons BY-NC-SA 4.0
