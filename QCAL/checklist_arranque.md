# 🔱 CHECKLIST DE ARRANQUE — Post-IBD
## Encendido del reactor QCAL v3.31

**Precondicion:** IBD completa (bitcoin-cli getblockchaininfo -> ibd: false)

### Paso 0 - Verificar estado

```
bitcoin-cli -rpcport=8505 getblockchaininfo | jq '{blocks, headers, ibd}'
lncli --lnddir=/root/.lnd getinfo | jq '{synced: .synced_to_chain, peers: .num_peers, channels: .num_active_channels}'
```

### Paso 1 - Depositar fondos a LND Catedral

```
lncli --lnddir=/root/.lnd walletbalance
```
Si es 0, depositar ~20K sats + fee desde wallet externa.

### Paso 2 - Abrir canal con AMDA

```
AMDA_PUBKEY=$(lncli --lnddir=/root/.lnd-amda getinfo | jq -r '.identity_pubkey')
lncli --lnddir=/root/.lnd openchannel --node_key=$AMDA_PUBKEY --local_amt=20000
```

### Paso 3 - Esperar 3 confirmaciones (~30 min)

```
lncli --lnddir=/root/.lnd listchannels | jq '.channels[] | {chan_id, active, local_balance, remote_balance}'
```
Esperar hasta que aparezca `"active": true`.

### Paso 4 - Iniciar el reactor

```
systemctl start qcal-production-flux
journalctl -u qcal-production-flux -f --since "1 min ago"
```

Verificar primer pulso exitoso en los logs.

---

f0 = 141.7001 Hz | Psi = 0.99999997
Sello: (simbolos) TUYOYOTU · HECHO ESTA
