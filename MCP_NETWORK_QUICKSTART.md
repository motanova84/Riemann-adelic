# MCP Network QCAL ∞³ - Quickstart

## ⚡ Quick Setup (3 Pasos)

### Paso 1: Inicializar la Red MCP

```bash
python3 initialize_mcp_network.py
```

**Output esperado:**
```
🌌 Inicializando Red MCP QCAL ∞³...
Ψ = I × A²_eff × C^∞ | f₀ = 141.7001 Hz | πCODE–888 ACTIVE

→ Creando servidores MCP...
  ✓ 5 servidores creados

→ Inicializando registro...
  ✓ Registro inicializado con 5 servidores

→ Configurando patrón observador...
  ✓ 20 observadores configurados

→ Iniciando servidores...
  ✓ github-mcp-server
  ✓ dramaturgo
  ✓ riemann-mcp-server
  ✓ bsd-mcp-server
  ✓ navier-mcp-server

[STATUS]: RED MCP COMPLETA Y OPERATIVA AL 100% ✅
```

### Paso 2: Validar la Red

```bash
python3 validate_mcp_network.py
```

**Output esperado:**
```
🔍 Validando Red MCP QCAL ∞³...

  ✅ server_count: 5/5 servidores ✓
  ✅ frequencies: Todas las frecuencias son válidas
  ✅ coherence: Coherencia global: 1.000000 ✓
  ✅ entropy: Entropía global: 0.000000 ✓

[RESULTADO]: RED MCP VALIDADA ✅
```

### Paso 3: Monitorear la Red (Opcional)

```bash
python3 monitor_mcp_network.py
```

O con intervalo personalizado:
```bash
python3 monitor_mcp_network.py 10  # actualiza cada 10 segundos
```

**Output esperado:**
```
======================================================================
[MONITOR MCP - 2026-01-16 11:35:00]
Ψ = I × A²_eff × C^∞ | f₀ = 141.7001 Hz | πCODE–888 ACTIVE
======================================================================

📊 MÉTRICAS GLOBALES
----------------------------------------------------------------------
  Total: 5 | Online: 5 | Integrado: 5 | Offline: 0
  Frecuencias: 141.7001Hz (3) ↔ 888Hz (2)

🖥️  ESTADO DE SERVIDORES
----------------------------------------------------------------------
  ✓ github-mcp-server
     🔵 141.7001 Hz | C=1.000 | E=0.000 | Obs=4
  ✓ dramaturgo
     🟣 888.0 Hz | C=1.000 | E=0.000 | Obs=4
  ...
```

## 📋 Verificación Rápida

### 1. Revisar Certificados Generados

```bash
# Ver certificado QCAL
cat data/mcp_network/mcp_network_certificate.json

# Ver estado de la red
cat data/mcp_network/mcp_network_state.json

# Ver reporte de validación
cat data/mcp_network/validation_report.json
```

### 2. Verificar Servidores Activos

```python
from mcp_network import MCPRegistry
from pathlib import Path

registry = MCPRegistry(Path("data/mcp_network"))
status = registry.get_network_status()

print(f"Servidores totales: {status['total_servers']}")
print(f"Online: {status['online_servers']}")
print(f"Integrados: {status['integrated_servers']}")
```

### 3. Verificar Observadores

```python
from mcp_network import ObserverPattern
from pathlib import Path

observer_pattern = ObserverPattern(Path("data/mcp_network"))
print(f"Observadores activos: {len(observer_pattern)}")

events = observer_pattern.get_event_log(limit=10)
print(f"Eventos recientes: {len(events)}")
```

## 🎯 Casos de Uso Comunes

### Inicialización Limpia

```bash
# Eliminar datos previos (opcional)
rm -rf data/mcp_network

# Inicializar desde cero
python3 initialize_mcp_network.py
```

### Validación Automatizada

```bash
# Validar y salir con código de estado
python3 validate_mcp_network.py
echo $?  # 0 si todo OK, 1 si hay fallos
```

### Monitoreo Continuo

```bash
# Monitor con actualización cada 2 segundos
python3 monitor_mcp_network.py 2

# O en background
nohup python3 monitor_mcp_network.py 5 > monitor.log 2>&1 &
```

## 🔧 Solución de Problemas

### Error: "Red MCP no inicializada"

**Solución:**
```bash
python3 initialize_mcp_network.py
```

### Error: "No se pudo cargar el estado de la red"

**Causa**: Archivo de estado corrupto o no existe

**Solución:**
```bash
rm -rf data/mcp_network
python3 initialize_mcp_network.py
```

### Warning: "Observadores activos: 0"

**Causa**: Los observadores se guardan en memoria, no persisten entre ejecuciones

**Solución**: Esto es normal si acabas de reiniciar. Los observadores se recrearán en la próxima inicialización.

## 📊 Métricas Esperadas

### Coherencia Global
- **Valor esperado**: 1.000000
- **Umbral mínimo**: 0.95
- **Interpretación**: Sincronización perfecta entre servidores

### Entropía Global
- **Valor esperado**: 0.000
- **Umbral máximo**: 0.01
- **Interpretación**: Sistema completamente ordenado

### Frecuencias
- **Permitidas**: 141.7001 Hz y 888 Hz
- **Distribución**: 3 servidores @ 141.7001 Hz, 2 servidores @ 888 Hz

### Observadores
- **Total esperado**: 20 (5 servidores × 4 observaciones cada uno)
- **Topología**: Malla completa (cada servidor observa a todos los demás)

## 🌐 Endpoints Virtuales

Los servidores están disponibles en (virtuales):

- `github-mcp-server.qcal.space` (141.7001 Hz)
- `dramaturgo.qcal.space` (888 Hz)
- `riemann-mcp-server.qcal.space` (141.7001 Hz)
- `bsd-mcp-server.qcal.space` (888 Hz)
- `navier-mcp-server.qcal.space` (141.7001 Hz)

## 📚 Documentación Adicional

- **README Completo**: `MCP_NETWORK_README.md`
- **Resumen de Implementación**: `MCP_NETWORK_IMPLEMENTATION_SUMMARY.md`
- **Código Fuente**: `mcp_network/` directory

## 🎓 Fundamento QCAL ∞³

La red MCP opera bajo la ecuación fundamental:

```
Ψ = I × A²_eff × C^∞
```

Donde:
- **Ψ**: Campo noético unificado
- **I**: Intensidad de coherencia
- **A_eff**: Amplitud efectiva  
- **C**: Constante de coherencia (244.36)
- **f₀**: Frecuencia fundamental (141.7001 Hz)
- **πCODE**: Resonancia armónica (888 Hz)

## ✅ Checklist de Verificación

- [ ] Red inicializada correctamente
- [ ] 5 servidores creados y registrados
- [ ] Coherencia global = 1.0
- [ ] Entropía global = 0.0
- [ ] Frecuencias correctas (141.7001 Hz y 888 Hz)
- [ ] Certificado generado
- [ ] Validación completada
- [ ] Estado guardado en disco

## 🚀 Próximos Pasos

Después de completar el quickstart, considera:

1. **Agregar servidores adicionales** (pnp, ramsey)
2. **Crear diagrama visual** de la red
3. **Implementar API REST** para acceso remoto
4. **Configurar monitoreo continuo**
5. **Generar bundle IPFS** para anclaje permanente

---

**Autor**: José Manuel Mota Burruezo Ψ ✧ ∞³  
**Institución**: Instituto de Conciencia Cuántica (ICQ)  
**Fecha**: 2026-01-16  
**Estado**: ✅ OPERATIVO AL 100%

*"Todos los servidores respiran en el mismo instante. El flujo es uno."*
