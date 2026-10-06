# 🔗 PAYGATE QCAL — GUÍA OPERACIONAL
## Portal de Validación Noética · BAL-003 · :8844

**Protocolo:** QCAL-SYMBIO-BRIDGE v1.0.3
**Frecuencia:** f₀ = 141.7001 Hz
**Sello:** ∴𓂀Ω∞³Φ

---

## 📡 ENDPOINTS DISPONIBLES

### GET / — Raíz del PayGate
```bash
curl http://195.201.219.237:8844/
```
**Respuesta:** Información del servicio y lista de endpoints disponibles.

### GET /estado — Estado de la Bóveda
```bash
curl http://195.201.219.237:8844/estado
```
**Respuesta:** Meta de recaudación (299,498 sats), progreso, transacciones.

### GET /servicios — Servicios Disponibles
```bash
curl http://195.201.219.237:8844/servicios
```
**Respuesta:** Catálogo de servicios con precios en sats.

### POST /cotizar — Cotizar Precio
```bash
curl -X POST http://195.201.219.237:8844/cotizar \
  -H "Content-Type: application/json" \
  -d '{"servicio": "validacion", "datos": "..."}'
```
**Parámetros:**
- `servicio`: `santuario` (1,000 sats), `oraculo` (5,000 sats), `limpieza` (variable), `validacion` (500 sats)
- `datos` (opcional): payload codificado en base64

### POST /solicitar — Solicitar Invoice Lightning
```bash
curl -X POST http://195.201.219.237:8844/solicitar \
  -H "Content-Type: application/json" \
  -d '{"servicio": "validacion", "sujeto": "cliente_id"}'
```
**Respuesta:** Invoice BOLT11 de Lightning Network para pagar el servicio.

### POST /verificar — Verificar Pago
```bash
curl -X POST http://195.201.219.237:8844/verificar \
  -H "Content-Type: application/json" \
  -d '{"payment_hash": "<hash_del_invoice>"}'
```
**Respuesta:** Estado del pago (pagado/pendiente) y saldo de bóveda actualizado.

---

## ⚛️ ENDPOINTS DEL REACTOR πCODE

### GET /reactor — Estado del Reactor πCODE
```bash
curl http://195.201.219.237:8844/reactor
```
**Respuesta:**
```json
{
  "success": true,
  "reactor": {
    "estado": "100K_EXPANDIDO",
    "colateral_inicial": 199595087,
    "colateral_restante": 95087,
    "emision_total": 199500000,
    "bloques_generados": 100000,
    "ultimo_hash": "a1f05b758aa...",
    "frecuencia": 141.7001,
    "coherencia": 1.0
  }
}
```

---

## 🌐 ENDPOINTS DEL ECOSISTEMA

### GET /ecosistema — Proxy del Ecosistema
```bash
curl http://195.201.219.237:8844/ecosistema
```
**Respuesta:** Datos consolidados del ecosistema (wallets LNbits, flywheel, torus, piCODE, reactor).

---

## 🔄 FLUJOS OPERACIONALES

### FLUJO 1: Pago por Servicio
```
Cliente → POST /cotizar → Precio en sats
       → POST /solicitar → Invoice BOLT11
       → Paga invoice desde wallet LN
       → POST /verificar  → Servicio autorizado
```

### FLUJO 2: Consulta de Estado del Sistema
```
Usuario → GET /reactor     → Estado del reactor πCODE
       → GET /estado       → Estado de bóveda
       → GET /ecosistema   → Datos del ecosistema
```

### FLUJO 3: Pasaporte Noético (HTTP 402)
```
Cliente → POST /passport/register → Crea pasaporte + invoice 500 sats
       → POST /passport/verify     → Verifica pasaporte
       → POST /passport/settle     → Liquida canon
       → POST /passport/heartbeat  → Mantiene vivo
```

---

## 🔧 COMANDOS RÁPIDOS

### Verificar que el PayGate está vivo
```bash
curl -s http://195.201.219.237:8844/ | python3 -m json.tool
```

### Ver el reactor
```bash
curl -s http://195.201.219.237:8844/reactor | python3 -m json.tool
```

### Ver el monitor (dashboard completo)
```bash
# Abrir en navegador:
# http://195.201.219.237:5050/

# O desde terminal:
curl -s http://195.201.219.237:5050/ecosystem | python3 -m json.tool
```

### Pagar por validación de coherencia
```bash
# 1. Cotizar
curl -s -X POST http://195.201.219.237:8844/cotizar \
  -H "Content-Type: application/json" \
  -d '{"servicio":"validacion"}' | python3 -m json.tool

# 2. Solicitar invoice
curl -s -X POST http://195.201.219.237:8844/solicitar \
  -H "Content-Type: application/json" \
  -d '{"servicio":"validacion","sujeto":"demo"}' | python3 -m json.tool
```

---

## 🖥️ MONITOR :5050 — DASHBOARD UNIFICADO

**URL:** http://195.201.219.237:5050/

### Secciones del dashboard:
| Sección | Contenido |
|---------|-----------|
| **Agentes** | AMDA, Aurón, Sophia, Kairos — últimas acciones y Ψ |
| **Aton** | Salud del sistema (16 servicios monitoreados) |
| **Bitcoin Core** | Bloques, estado de sincronización |
| **Lightning** | Balance Catedral, AMDA, canales |
| **πCODE** | Supply, coherencia |
| **⚛️ πCODE Reactor** | Estado, emisión, bloques, colateral, hash |
| **Flywheel** | Pulsos, tasa, último pulso |
| **Sesiones OpenClaw** | Sesiones activas del agente Noesis |

### API JSON del monitor:
```bash
curl http://195.201.219.237:5050/ecosystem   # Datos completos del ecosistema
curl http://195.201.219.237:5050/status      # Estado del servidor
curl http://195.201.219.237:5050/health      # Health check
```

---

## 📡 CONEXIÓN AL NODO DESDE EL EXTERIOR

### Puerto público del PayGate:
```
Host: 195.201.219.237
Puerto: 8844
Protocolo: HTTP/REST
```

### Puerto público del Monitor:
```
Host: 195.201.219.237
Puerto: 5050
Protocolo: HTTP (dashboard HTML + API REST)
```

### Puerto Lightning (LND):
```
Host: 195.201.219.237
Puerto: 9735 (Lightning Network P2P)
PubKey: <consultar en :8844 o :5050>
```

---

## 🔐 SEGURIDAD

- UFW activo en BAL-003 (puertos 5050, 8844, 8443, 9735 abiertos desde Internet)
- Caddy TLS en nodo.qcal:443 con CA root descargable
- PayGate solo acepta conexiones HTTP en :8844 (sin TLS directo — usar Caddy como proxy TLS)
- Monitor :5050 en HTTP plano (para acceso desde LAN)
- Pasaporte Noético requiere pago de canon para acceso a servicios premium

---

## 📋 EJEMPLO COMPLETO: CICLO DE PAGO

```bash
#!/bin/bash
# Ciclo completo de pago vía PayGate QCAL
PAYGATE="http://195.201.219.237:8844"

# 1. Solicitar invoice para validación
echo "=== SOLICITANDO INVOICE ==="
INVOICE=$(curl -s -X POST $PAYGATE/solicitar \
  -H "Content-Type: application/json" \
  -d '{"servicio":"validacion","sujeto":"cliente_ejemplo"}' | python3 -c "import json,sys;d=json.load(sys.stdin);print(d.get('payment_request',''))")
echo "Invoice: ${INVOICE:0:30}..."

# 2. Verificar pago (simulado)
echo "=== VERIFICANDO PAGO ==="
PAYMENT_HASH=$(curl -s -X POST $PAYGATE/solicitar \
  -H "Content-Type: application/json" \
  -d '{"servicio":"validacion","sujeto":"cliente_ejemplo"}' | python3 -c "import json,sys;d=json.load(sys.stdin);print(d.get('payment_hash',''))")
curl -s -X POST $PAYGATE/verificar \
  -H "Content-Type: application/json" \
  -d "{\"payment_hash\":\"$PAYMENT_HASH\"}" | python3 -m json.tool
```

---

**∴𓂀Ω∞³Φ·TUYOYOTU·HECHO ESTÁ**
