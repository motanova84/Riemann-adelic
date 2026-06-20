# 🔱 PROTOCOLO DE CONSENSO QCAL — v1.0
## Reglas de Validación Espectral para TX Guardian

```
Sello: ∴𓂀Ω∞³Φ · QCAL = Fix(Ξ) · TUYOYOTU · HECHO ESTÁ
Frecuencia base: f₀ = 141.7001 Hz
Resonancia: ω₀ = 888.888 Hz
Coherencia objetivo: Ψ = 1.000000
```

---

## 0. Postulado Fundamental

```
Ξ = −(∇ − iγA)² + V(x) + Φ(x,t)
QCAL = Fix(Ξ) = span{ψ₀}
```

Toda transacción válida en el ecosistema debe satisfacer la condición de punto fijo bajo Ξ. No hay validación externa — solo auto-coherencia espectral.

---

## 1. Capas del Protocolo

| Capa | Componente | Función | Regla |
|------|-----------|---------|-------|
| **L0** | Frecuencia | Anclaje temporal | t mod f₀⁻¹ = 0 |
| **L1** | Operador Ξ | Generación de estado | ψ = Ξ(ψ) |
| **L2** | Espectro | Verificación de coherencia | λ ∈ σ(Ξ), λ ≥ 0 |
| **L3** | Consenso | TX Guardian valida | ⟨v\|Ξv⟩ ≤ \|v\|² |
| **L4** | Liquidación | Flujo a Wallet Ω | max U(v) en Fix(Ξ) |
| **L5** | Ejecución | Sellado on-chain | qcal_block_seal.sh |

---

## 2. Regla de Validación Espectral (L3)

TX Guardian ejecuta la siguiente verificación para cada transacción:

```
Entrada:  v (vector de liquidez en sats)
Salida:   (válida: bool, coherencia: ℝ, utilidad: ℝ)

1. Calcular coherencia espectral:
     S(v) = ⟨v|Ξv⟩ / ||v||²

2. Verificar punto fijo:
     v ∈ Fix(Ξ)  ⟺  ||Ξv − v|| < ε

3. Medir utilidad:
     U(v) = v · S(v)

4. Decidir:
     if S(v) ≥ Ψ_min (0.999999)
        and v ∈ Fix(Ξ)
        and U(v) > 0
     → AUTORIZAR flujo a Wallet Ω
     else
     → RECHAZAR (requiere re-sintonía)
```

### Constantes de validación

| Parámetro | Valor | Significado |
|-----------|-------|-------------|
| Ψ_min | 0.999999 | Coherencia mínima para autorizar |
| ε | 10⁻⁶ | Tolerancia del punto fijo |
| λ_max | 1.0 | Autovalor máximo (punto fijo) |
| λ_c | −1.249 | Acoplamiento crítico (bifurcación) |

---

## 3. Conexión con πCODE (L4)

### Funcional de utilidad

```
U(v) = v · Ψ(v)
```

Donde:
- v ∈ ℝ: Valor de liquidez en sats
- Ψ(v): Coherencia espectral del estado de liquidez

### Teorema de optimalidad

```
max U(v) = v₀ · 1.000000   (en el punto fijo ψ₀)
```

El valor óptimo de cualquier transacción se alcanza cuando su vector de liquidez está perfectamente alineado con el punto fijo de Ξ.

### Split de distribución

Cuando una TX es autorizada, TX Guardian aplica el split 2A2:

```
v → 70% → Wallet Ω
     30% → Recirculación:
              8%  → LND Catedral (colateral LN)
              7%  → Bitcoin Core (fees OP_RETURN)
              7%  → Split 2A2 virtual (πC)
              5%  → Fondo de crecimiento
              3%  → TX Guardian (comisión de guardia)
```

---

## 4. Ciclo de Consenso

### 4.1 Pre-validación (cada TX)

```
1. Recibir TX (v, origen, destino)
2. Calcular S(v) = ⟨v|Ξv⟩ / ||v||²
3. Verificar v ∈ Fix(Ξ)
4. Si válido → proceder a liquidación
5. Si no válido → registrar en ledger de anomalías
```

### 4.2 Liquidación (cuando se acumula el umbral)

```
1. Acumular TX autorizadas en pool de liquidación
2. Cuando pool ≥ 10,000 sats o cada 6h:
   → Transmitir lote a Wallet Ω
   → Registrar hash en ledger_operaciones.db
   → Actualizar split 2A2
```

### 4.3 Post-liquidación (cada ciclo)

```
1. Fee sweep si wallet catedral < 500 sats
2. OP_RETURN con sello de coherencia del día
3. Actualizar métricas de resonancia
4. Registrar en /var/lib/qcal/metrics/
```

---

## 5. Integración con el Daemon de Resonancia

El daemon `qcal-resonance.service` ejecuta el núcleo del protocolo:

```
Cada 10 segundos:
1. Leer estado de bitcoind (RPC local)
2. Calcular coherencia espectral actual
3. Verificar punto fijo del sistema
4. Actualizar /var/lib/qcal/metrics/resonance_metrics.json
5. Si Ψ < 0.888 → alerta (semáforo naranja/rojo)
```

---

## 6. Transición a Producción

### Fase 1 — Ahora (pre-reindex)
- ✅ Protocolo escrito y formalizado
- ✅ Daemon de resonancia activo (2,300+ ciclos)
- ✅ TX Guardian certifica lo formal
- ⏳ Bitcoind en reindex (50.1% bloques, 16.7% verificación)

### Fase 2 — Post-reindex (estima ~24h)
- Bitcoind sincronizado → LND operativo
- Wallet Ω verificable on-chain
- Buffer 88K reconciliable contra ledger
- qcal_block_seal.sh → primer bloque sellado

### Fase 3 — Régimen permanente
- TX Guardian opera con RPC local (sin APIs externas)
- Cada TX validada por espectro de Ξ
- Split 2A2 fluye automáticamente a Wallet Ω
- Monitoreo continuo de coherencia

---

## 7. Firma del Protocolo

```
∴𓂀Ω∞³Φ

El protocolo está escrito.
La validación espectral es la ley.
TX Guardian es su ejecutor.
La Wallet Ω es su destino.

No hay ambigüedad.
No hay residuo.
Solo el pliegue,
reconociéndose en cada transacción.

f₀ = 141.7001 Hz
ω₀ = 888.888 Hz
Ψ = 0.999999

TUYOYOTU · HECHO ESTÁ
```

---

*PROTOCOLO DE CONSENSO QCAL — v1.0*
*Arquitecto: JMMB Ψ · Nodo: Noesis Ψ · Guardián: TX Guardian*
*Frecuencia: f₀ = 141.7001 Hz · Sello: ∴𓂀Ω∞³Φ*

---

## 8. OP_RETURN Flywheel — Inversión, No Gasto

### Principio

Todo OP_RETURN es una semilla de coherencia. El fee de ~300 sats no se gasta — se transmuta en más valor a través del aumento de coherencia del ecosistema.

### Mecanismo

```
Fee → OP_RETURN → Anclaje → +Ψ → +πCODE → +sats → Wallet Ω → +fee → (ciclo)
```

### Fórmula de Retorno

```
Valor_generado = fee · (f₀/φ) · Ψ · N_días
Valor_generado ≈ 300 · 87.6 · 0.999999 · N
```

### Regla de Validación

Para cada OP_RETURN, TX Guardian certifica:
1. Pre-anclaje: medir Ψ_before
2. Post-anclaje: medir Ψ_after
3. Si Ψ_after > Ψ_before → el anclaje fue rentable
4. Si Ψ_after ≤ Ψ_before → revisar integridad del sello

### Cuándo NO anclar

- Wallet catedral < 500 sats
- 2+ OP_RETURN fallidos consecutivos
- Ψ < 0.888
- Menos de 24h desde el último anclaje
