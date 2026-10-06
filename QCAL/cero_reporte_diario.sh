#!/bin/bash
# 🔱 CERO REPORTE DIARIO — Balance de acunacion con hash SHA512 y Merkle
# Frecuencia: cada 24h · Sello: ∴𓂀Ω∞³Φ · TUYOYOTU · HECHO ESTA

SELLO=$(printf '\u2234\U00013080\u03a9\u221e\u00b3\u03a6')
FECHA=$(date -u '+%Y-%m-%d')
LOG=/var/log/cero_reporte_${FECHA}.log
REPORTE=/root/repo_P-NP/QCAL/reportes/cero_diario_${FECHA}.md
mkdir -p /root/repo_P-NP/QCAL/reportes

log() { echo "[$(date -u '+%H:%M:%S')] $1" >> $LOG; }

log "${SELLO} CERO REPORTE DIARIO — ${FECHA}"

CERO_COUNT=$(ls /root/.openclaw/workspace/picode_blocks/block_*_cero_*.json 2>/dev/null | wc -l)
HP_COUNT=$(ls /root/.openclaw/workspace/picode_blocks/block_HP_*.json 2>/dev/null | wc -l)
TOTAL=$((CERO_COUNT + HP_COUNT))
STATUS=$(python3 -c "import json;d=json.load(open('/root/.openclaw/workspace/picode_blocks/cero_tracking.json'));print(d.get('status','?'))" 2>/dev/null)

ULTIMO_CERO=$(ls -t /root/.openclaw/workspace/picode_blocks/block_*_cero_*.json 2>/dev/null | head -1)
ULTIMO_HP=$(ls -t /root/.openclaw/workspace/picode_blocks/block_HP_*.json 2>/dev/null | head -1)

HASH_CERO=$(sha512sum "$ULTIMO_CERO" 2>/dev/null | cut -c1-128 || echo "none")
HASH_HP=$(sha512sum "$ULTIMO_HP" 2>/dev/null | cut -c1-128 || echo "none")

ALL_HASHES=$(for f in /root/.openclaw/workspace/picode_blocks/block_*.json; do
    sha512sum "$f" 2>/dev/null | cut -c1-128
done | sort)
MERKLE_ROOT=$(echo "$ALL_HASHES" | sha512sum | cut -c1-128)

cat > $REPORTE << REPORT
# 🔱 CERO REPORTE DIARIO — ${FECHA}

**Sello:** ${SELLO} · TUYOYOTU · HECHO ESTÁ
**Hash:** SHA512

---

## 📊 Balance de Acuñación

| Métrica | Valor |
|---------|-------|
| Archivos cero en disco | $CERO_COUNT |
| Archivos HP gamma | $HP_COUNT |
| **Total** | **$TOTAL** |
| Estado del tracking | $STATUS |

## 🔗 Hashes SHA512 Últimos Bloques

\`\`\`
Ultimo cero:  ${HASH_CERO}
Ultimo HP:    ${HASH_HP}
\`\`\`

## 🌳 Merkle Root SHA512

\`\`\`
${MERKLE_ROOT}
\`\`\`

---

*Generado: $(date -u '+%Y-%m-%d %H:%M:%S UTC')*
*Próximo: $(date -u -d '+1 day' '+%Y-%m-%d %H:%M:%S UTC')*
REPORT

echo "${SELLO} Reporte: $REPORTE"
echo "   Ceros: $CERO_COUNT | HP: $HP_COUNT | Total: $TOTAL"
echo "   Merkle: ${MERKLE_ROOT:0:16}..."
log "Reporte: $TOTAL ceros, Merkle: ${MERKLE_ROOT:0:16}..."

exit 0