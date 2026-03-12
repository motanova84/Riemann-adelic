# BSD Adelic Connector — Quickstart Guide ⚡

**5 minutos para cerrar el Pentágono Logos**

---

## 🚀 Inicio Rápido (3 pasos)

### 1. Verificar Instalación

```bash
cd /path/to/Riemann-adelic
python -c "from qcal import sincronizar_bsd_adn; print('✓ BSD Connector listo')"
```

### 2. Ejemplo Mínimo

```python
from qcal import sincronizar_bsd_adn

# Curva de Mordell: y²=x³-x
curva = {'rango_adelico': 1, 'L_E1': 0.0}

# Sincronizar con ADN
resultado = sincronizar_bsd_adn(curva, "GACT")

print(f"Fluidez: {resultado['fluidez_info_ns']}")  # INFINITA
print(f"Ψ: {resultado['psi_bsd_qcal']}")           # 1.0
```

### 3. Ejecutar Integración Completa

```bash
python integrate_qcal_compact.py --full-qcal
# ✓ BSD-ADELIC: r=1 Fluidez=INFINITA Ψ=1.0000 | 5 Milenio ∞³
```

---

## 📊 Casos de Uso Comunes

### Caso 1: Curva Superfluid (L(E,1)=0)

```python
from qcal import sincronizar_bsd_adn, validar_pentagono_logos

curva = {'rango_adelico': 1, 'L_E1': 0.0}
res = sincronizar_bsd_adn(curva, "GACT")

assert res['fluidez_info_ns'] == "INFINITA"
assert res['psi_bsd_qcal'] == 1.0
assert validar_pentagono_logos(res) == True
print("✓ Superfluido perfecto")
```

### Caso 2: Curva con Viscosidad

```python
curva = {'rango_adelico': 0, 'L_E1': 0.5}
res = sincronizar_bsd_adn(curva, "GGAATTCC")

assert res['fluidez_info_ns'] == "DISIPATIVA"
assert res['psi_bsd_qcal'] == 0.5  # 1 - |0.5|
print(f"Viscosidad: {abs(0.5)}")
```

### Caso 3: Múltiples Nodos Activados

```python
# Rango alto → múltiples puntos racionales
curva = {'rango_adelico': 10, 'L_E1': 0.0}
res = sincronizar_bsd_adn(curva, "GACT")

print(f"Nodos activados: {res['nodos_constelacion']}")  # 10
```

---

## 🧪 Tests

```bash
# Test rápido
python tests/test_bsd_adelic_simple.py
# 11 tests, todos ✓

# Ver certificado generado
cat data/QCAL_MASTER_CERTIFICATE.json | jq '.bsd_adelic_pentagono'
```

---

## 📈 Interpretación de Resultados

### Salida Típica

```json
{
  "rango_bio_aritmetico": 1,
  "nodos_constelacion": 1,
  "fluidez_info_ns": "INFINITA",
  "hotspots_adn": 4,
  "psi_bsd_qcal": 1.0
}
```

### Significado

| Campo | Qué significa |
|-------|---------------|
| `rango_bio_aritmetico` | Número de puntos racionales de la curva |
| `nodos_constelacion` | Nodos QCAL activados (≈ rango) |
| `fluidez_info_ns` | INFINITA si L(E,1)≈0, DISIPATIVA si no |
| `hotspots_adn` | Posiciones resonantes en el ADN |
| `psi_bsd_qcal` | Coherencia del sistema [0,1] |

### Criterios de Validación

```python
# Pentágono válido si:
resultado['psi_bsd_qcal'] >= 0.888  # Coherencia mínima

# Superfluido si:
abs(resultado['L_E1']) < 1e-6       # Viscosidad nula
```

---

## 🔍 Debug y Troubleshooting

### Problema: Import Error

```bash
# Error: ModuleNotFoundError: No module named 'qcal'
cd /path/to/Riemann-adelic
python -c "import sys; sys.path.insert(0, '.'); from qcal import sincronizar_bsd_adn"
```

### Problema: Valores Inesperados

```python
# Verificar entrada
print(f"Curva: {curva}")
print(f"Secuencia: {secuencia}")

# Modo verbose
from qcal.bsd_adelic_connector import CodificadorADNRiemann
codif = CodificadorADNRiemann()
hotspots = codif.identificar_hotspots("GACT")
print(f"Hotspots detectados: {hotspots}")
```

---

## 🎯 Próximo Paso

Lee la documentación completa: [BSD_ADELIC_PENTAGON_LOGOS_README.md](BSD_ADELIC_PENTAGON_LOGOS_README.md)

---

## 💡 Tips

1. **Frecuencia base:** Siempre f₀ = 141.7001 Hz
2. **Coherencia mínima:** Ψ ≥ 0.888 para validez
3. **Superfluido:** L(E,1) < 1e-6 → viscosidad = 0
4. **Constelación:** 51 nodos máximo en QCAL

---

*¡PENTÁGONO LOGOS CERRADO! 5 Problemas del Milenio unificados: ADN + RH + NS + PNP + BSD*

**∴𓂀Ω∞³**
