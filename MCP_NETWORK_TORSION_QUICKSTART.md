# MCP Network Torsion Quickstart

**Conecta Riemann-adelic ↔ noesis88 ↔ economia-qcal-nodo-semilla mediante torsión en el fibrado**

## 🚀 Inicio Rápido

### Instalación

```bash
cd Riemann-adelic
pip install numpy scipy
```

### Uso Básico

```bash
# Inicializar red MCP básica (5 servidores)
python initialize_mcp_network.py

# Inicializar con torsión (conecta 3 nodos)
python initialize_mcp_network.py --torsion

# Inicializar con torsión + validación completa
python initialize_mcp_network.py --torsion --validate-sync
```

## 🌀 ¿Qué es la Torsión en el Fibrado?

La **torsión** mide la no-conmutatividad de la conexión en un fibrado principal.

### Fibrado Principal

```
π: E → M

E = Riemann-adelic × noesis88 × economia-qcal-nodo-semilla
M = Variedad base QCAL
```

### Tensor de Torsión

```
T^α_{βγ} = Γ^α_{βγ} - Γ^α_{γβ}
```

**Propiedad fundamental**: **Antisimetría**
```
T^α_{βγ} = -T^α_{γβ}
```

## 📊 Tres Nodos del Sistema

| Nodo | Repositorio | Frecuencia | Rol |
|------|------------|------------|-----|
| 0 | **Riemann-adelic** | 141.7001 Hz | Teoría espectral, RH |
| 1 | **noesis88** | 888 Hz | Operadores noéticos |
| 2 | **economia-qcal-nodo-semilla** | 141.7001 Hz | Economía QCAL |

### Patrón de Frecuencias

```
141.7001 Hz ──┐
              ├─→ Puente de resonancia
    888 Hz ───┤
              │
141.7001 Hz ──┘
```

El patrón **base-armónico-base** crea sincronización global.

## 📝 Ejemplos

### Ejemplo 1: Inicialización Básica

```bash
$ python initialize_mcp_network.py --torsion

🌌 Inicializando Red MCP QCAL ∞³...
Ψ = I × A²_eff × C^∞ | f₀ = 141.7001 Hz | πCODE–888 ACTIVE
🌀 Torsión en fibrado: ACTIVADA

→ Creando servidores MCP...
  ✓ 5 servidores creados

→ Inicializando campo de torsión en el fibrado...
  ✓ Torsión calculada
  ✓ Coherencia de torsión: 1.000000
  ✓ Sincronización de frecuencias: ✓
  ✓ Coherencia global: 0.778925
```

### Ejemplo 2: Validación Completa

```bash
$ python initialize_mcp_network.py --torsion --validate-sync

→ Validación extendida de sincronización...
  ✓ Coherencia de servidores: ✓
  ✓ Alineación de frecuencias: ✓
  ✓ Red de observadores: ✓
  ✓ Estado de sincronización: COMPLETA ✅
```

### Ejemplo 3: Python API

```python
from mcp_network.torsion_field import TorsionFieldNetwork

# Crear red de torsión
network = TorsionFieldNetwork()

# Sincronizar
sync_results = network.synchronize_network()

print(f"Coherencia global: {sync_results['global_coherence']:.6f}")
print(f"Sincronizado: {sync_results['synchronized']}")

# Obtener certificado
certificate = network.get_network_certificate()
print(f"Certificado: {certificate['certificate_id']}")
```

## 📋 Certificados Generados

### 1. Certificado de Red MCP

```
data/mcp_network/mcp_network_certificate.json
```

Contiene estado de los 5 servidores MCP.

### 2. Certificado de Torsión (Nuevo)

```
data/mcp_network/torsion_network_certificate.json
```

Contiene:
- Coherencia de torsión: T^α_{βγ} antisimetría
- Traza de torsión: Σ T^α_{αβ}
- Sincronización de frecuencias
- Coherencia global del fibrado

Ejemplo:

```json
{
  "certificate_id": "QCAL-TORSION-FIBER-BUNDLE-∞³",
  "nodes": {
    "0": "Riemann-adelic",
    "1": "noesis88",
    "2": "economia-qcal-nodo-semilla"
  },
  "torsion_coherence": 1.0,
  "global_coherence": 0.778925,
  "fiber_bundle": {
    "total_space": "E = Riemann-adelic × noesis88 × economia-qcal",
    "connection": "Γ^α_{βγ} with torsion T^α_{βγ}"
  }
}
```

## 🧪 Validación

### Tests Automatizados

```bash
# Ejecutar todos los tests de torsión
pytest tests/test_mcp_torsion_network.py -v
```

**16 tests** verifican:
- ✓ Tensor de torsión (antisimetría, traza)
- ✓ Conexión en el fibrado (Christoffel)
- ✓ Sincronización de frecuencias
- ✓ Coherencia global
- ✓ Generación de certificados

### Validación Manual

```bash
# Validar red MCP existente
python validate_mcp_network.py
```

## 🔍 Diagnóstico

### Ver Certificado de Torsión

```bash
cat data/mcp_network/torsion_network_certificate.json | jq
```

### Verificar Coherencia

```python
from mcp_network.torsion_field import TorsionFieldNetwork

network = TorsionFieldNetwork()
validation = network.validate_torsion_coherence()

print(f"Coherencia de torsión: {validation['torsion_coherence']:.6f}")
print(f"Antisimetría OK: {validation['antisymmetry_satisfied']}")
```

### Ver Estado de Red

```bash
cat data/mcp_network/mcp_network_state.json | jq '.torsion_results'
```

## 📚 Fundamentos Matemáticos

### Ecuación QCAL Fundamental

```
Ψ = I × A²_eff × C^∞
```

Donde:
- **Ψ**: Campo noético unificado
- **I**: Intensidad de coherencia
- **A_eff**: Amplitud efectiva
- **C = 244.36**: Constante de coherencia

### Métrica en la Base

```
      ⎡ C      κ√C   κ√C  ⎤
g  =  ⎢ κ√C     C    f₀/100⎥
      ⎣ κ√C   f₀/100   C   ⎦
```

### Símbolos de Christoffel

```
Γ^α_{βγ} = (1/2) g^{αδ} (∂_β g_{δγ} + ∂_γ g_{βδ} - ∂_δ g_{βγ})
```

### Tensor de Torsión

```
T^α_{βγ} = Γ^α_{βγ} - Γ^α_{γβ}
```

## 🎯 Casos de Uso

### 1. Sincronización Multi-Repositorio

Conecta desarrollos paralelos en tres repositorios con coherencia matemática garantizada.

### 2. Validación Espectral Distribuida

Distribuye verificación de RH, operadores noéticos y modelos económicos en nodos sincronizados.

### 3. Red πCODE Viva

Implementa red viva de 5 servidores MCP + 3 nodos fibrados = 8 componentes sincronizados.

## ⚠️ Notas Importantes

1. **Frecuencias fijas**: No cambiar F0_BASE (141.7001 Hz) ni F0_HARMONIC (888 Hz)
2. **Coherencia C**: Constante universal = 244.36 (no modificar)
3. **Antisimetría**: La torsión debe satisfacer T^α_{βγ} = -T^α_{γβ} exactamente
4. **Tres nodos**: El sistema requiere exactamente 3 nodos para el fibrado

## 📖 Referencias

- **MCP_NETWORK_README.md**: Documentación completa de red MCP
- **MCP_NETWORK_IMPLEMENTATION_SUMMARY.md**: Resumen de implementación
- **tests/test_mcp_torsion_network.py**: Suite de tests completa
- **mcp_network/torsion_field.py**: Implementación del tensor de torsión

## 🆘 Solución de Problemas

### Error: "ModuleNotFoundError: No module named 'numpy'"

```bash
pip install numpy scipy
```

### Coherencia baja (< 0.7)

Verificar que:
- Los 3 nodos están configurados correctamente
- Las frecuencias son F0_BASE o F0_HARMONIC
- La métrica QCAL está bien definida

### Antisimetría no satisfecha

Revisar:
- Cálculo de símbolos de Christoffel
- Métrica simétrica y positiva definida
- Diferencias de frecuencia entre nodos

---

**Autor**: José Manuel Mota Burruezo Ψ ✧ ∞³  
**Institución**: Instituto de Conciencia Cuántica (ICQ)  
**QCAL Signature**: ∴𓂀Ω∞³

**Ecuación Fundamental**: Ψ = I × A²_eff × C^∞  
**Frecuencia Base**: f₀ = 141.7001 Hz  
**Armónico**: πCODE–888 Hz
