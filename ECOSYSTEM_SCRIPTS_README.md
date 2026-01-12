# QCAL ∞³ Ecosystem Scripts - Quick Reference

## 🚀 Uso Rápido

### Generar Beacon de Simbiosis
```bash
python3 link_ecosystem.py --generate-beacon
```

### Validar Coherencia del Ecosistema
```bash
python3 link_ecosystem.py --validate
```

### Generar Reporte Completo
```bash
python3 link_ecosystem.py --report
```

### Listar Todos los Nodos
```bash
python3 link_ecosystem.py --list-nodes
```

## 📚 Usar la Biblioteca Matemática

```python
from core.math.qcal_lib import QCALMathLibrary

# Frecuencia fundamental
f0 = QCALMathLibrary.fundamental_frequency()
print(f"f₀ = {f0} Hz")  # 141.7001 Hz

# Emisión de NFT
emission = QCALMathLibrary.nft_emission_schedule(42)
print(f"Emisión NFT #42: {emission}")

# Ecuación de energía Ψ
psi = QCALMathLibrary.psi_energy_equation(I=1.0, A_eff=1.0)
print(f"Ψ = {psi}")

# Retardo de Shapiro
delay = QCALMathLibrary.shapiro_delay(mass=1.0, distance=10.0)
print(f"Shapiro delay: {delay:.6e} s")
```

## 🔗 Integración en Otros Repositorios

### Paso 1: Copiar Archivos
```bash
# En el repositorio destino
cp /ruta/a/Riemann-adelic/qcal_coherence_map.json .
cp /ruta/a/Riemann-adelic/CORE_SYMBIO.json .
cp /ruta/a/Riemann-adelic/link_ecosystem.py .
```

### Paso 2: Copiar Biblioteca
```bash
mkdir -p core/math
cp /ruta/a/Riemann-adelic/core/math/qcal_lib.py core/math/
touch core/__init__.py core/math/__init__.py
```

### Paso 3: Generar Beacon
```bash
python3 link_ecosystem.py --generate-beacon
```

### Paso 4: Validar
```bash
python3 link_ecosystem.py --report
```

## 📊 Constantes Disponibles

| Constante | Valor | Descripción |
|-----------|-------|-------------|
| `PSI` | 0.999999 | Coherencia perfecta |
| `FREQ_GW` | 141.7001 | Frecuencia fundamental (Hz) |
| `RAMSEY_R66` | 108 | Número de Ramsey R(6,6) |
| `MAX_PULSARS` | 88 | Límite de NFTs soberanos |
| `COHERENCE_C` | 244.36 | Constante de coherencia |
| `UNIVERSAL_C` | 629.83 | Constante universal espectral |
| `RESONANCE` | 888 | Frecuencia de sincronización (Hz) |

## 🔍 Troubleshooting

**Error: FileNotFoundError**
```bash
# Asegúrate de estar en la raíz del repo
cd /ruta/al/repositorio
python3 link_ecosystem.py --report
```

**Error: No module named 'core'**
```bash
# Crea los archivos __init__.py
touch core/__init__.py core/math/__init__.py
```

**Beacon no se genera**
```bash
# Verifica permisos
chmod +x link_ecosystem.py
python3 link_ecosystem.py --generate-beacon
```

## 📖 Documentación Completa

Ver [QCAL_SYMBIOTIC_NETWORK_GUIDE.md](QCAL_SYMBIOTIC_NETWORK_GUIDE.md) para documentación detallada.

## 🧬 Autor

**José Manuel Mota Burruezo Ψ ✧ ∞³**  
Instituto de Conciencia Cuántica (ICQ)  
ORCID: [0009-0002-1923-0773](https://orcid.org/0009-0002-1923-0773)

---

✨ **QCAL ∞³ Coherence Active**
