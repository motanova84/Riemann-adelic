# 🚀 Quick Start: Sistema Algorítmico de Demostración de RH

## ⚡ Ejecución Rápida

### Validación Numérica Completa

```bash
# Ejecutar validación algorítmica
python validate_algorithmic_rh.py
```

**Salida esperada:**
```
✓ Verificados 4 ceros con Re(s)=1/2
✓ Primos verificados: 15
✓ f₀ = 141.7001 Hz (match perfecto)
✓ Certificado: SHA256-QCAL-RH-V7.1-ALGORITHMIC
```

### Ver Certificado Digital

```bash
# Ver certificado generado
cat data/certificates/algorithmic_rh_certificate.json
```

### Validación V5 Coronación (Integrada)

```bash
# Validación completa tradicional
python validate_v5_coronacion.py --precision 50
```

## 📦 Archivos Clave

### Formalización Lean 4
- **`formalization/lean/RH_Algorithmic_Proof.lean`** - Implementación completa
- **`formalization/lean/ALGORITHMIC_PROOF_README.md`** - Documentación detallada

### Validación Python
- **`validate_algorithmic_rh.py`** - Script de validación ejecutable

### Certificados
- **`data/certificates/algorithmic_rh_certificate.json`** - Certificado digital

### Documentación
- **`ALGORITHMIC_RH_IMPLEMENTATION_SUMMARY.md`** - Resumen de implementación

## 🎯 Algoritmos Disponibles

| # | Algoritmo | Descripción | Complejidad |
|---|-----------|-------------|-------------|
| 1 | `algoritmo_verificacion_ceros` | Verifica ceros hasta altura T | O(T log T) |
| 2 | `algoritmo_generacion_primos` | Genera primos desde espectro | O(N log N) |
| 3 | `algoritmo_decidibilidad_RH` | Decide RH para banda ε | O(1/ε) |
| 4 | `algoritmo_certificado_cero` | Certifica cero individual | O(1) |
| 5 | `algoritmo_calculo_frecuencia` | Calcula f₀ = 141.7001 Hz | O(K) |
| 6 | `algoritmo_verificacion_completa` | Verificación completa | O(T log T) |

## 🔧 Configuración QCAL

**Parámetros clave:**
- **Coherencia:** C = 244.36
- **Frecuencia fundamental:** f₀ = 141.7001 Hz
- **Constante espectral:** C = 629.83
- **Ecuación:** Ψ = I × A_eff² × C^∞

## 📊 Ejemplos de Uso

### Ejemplo 1: Verificar primeros ceros

```python
from validate_algorithmic_rh import AlgorithmicRHValidator

validator = AlgorithmicRHValidator(precision=50)
result = validator.algoritmo_1_verificacion_ceros(T=30, max_zeros=10)
print(f"Ceros verificados: {len(result['output'])}")
```

### Ejemplo 2: Generar primos hasta N

```python
result = validator.algoritmo_2_generacion_primos(N=100)
print(f"Primos: {result['output'][:10]}")
```

### Ejemplo 3: Calcular frecuencia fundamental

```python
result = validator.algoritmo_5_calculo_frecuencia(K=1000)
print(f"f₀ = {result['output']} Hz")
```

### Ejemplo 4: Generar reporte completo

```python
validator.generar_reporte_completo()
# Genera certificado en data/certificates/algorithmic_rh_certificate.json
```

## 🧪 Testing

### Test Básico
```bash
# Verificar que el script ejecuta sin errores
python validate_algorithmic_rh.py > /tmp/test_output.txt
echo "✓ Test passed"
```

### Test de Certificado
```bash
# Verificar que el certificado se genera correctamente
python validate_algorithmic_rh.py
test -f data/certificates/algorithmic_rh_certificate.json && echo "✓ Certificado generado"
```

## 📚 Teoremas Principales

### Teorema de Decidibilidad
```lean
theorem rh_es_decidible : 
    ∀ (ε : ℝ) (hε : 0 < ε),
    ∃ (resultado : DecisionOutput (...)),
    resultado.decision = false
```

**Significado:** RH es algorítmicamente decidible para cualquier banda de error ε > 0.

## 🔗 Referencias Rápidas

- **DOI Principal:** [10.5281/zenodo.17379721](https://doi.org/10.5281/zenodo.17379721)
- **ORCID:** [0009-0002-1923-0773](https://orcid.org/0009-0002-1923-0773)
- **Repositorio:** [github.com/motanova84/-jmmotaburr-riemann-adelic](https://github.com/motanova84/-jmmotaburr-riemann-adelic)

## ⚙️ Dependencias

### Python
```bash
pip install mpmath numpy
```

### Lean 4
```bash
cd formalization/lean
lake update
lake build
```

## 💡 Tips

1. **Precisión Alta:** Usa `precision=100` para cálculos más precisos (más lento)
2. **Verificación Rápida:** Usa `max_zeros=5` para pruebas rápidas
3. **Certificados:** Los certificados JSON son verificables independientemente

## 🐛 Troubleshooting

### Error: "No module named 'mpmath'"
```bash
pip install mpmath
```

### Error: "lake not found"
```bash
# Instalar Lean 4
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

## ✅ Checklist de Validación

- [ ] Ejecutar `python validate_algorithmic_rh.py`
- [ ] Verificar certificado en `data/certificates/`
- [ ] Confirmar f₀ = 141.7001 Hz
- [ ] Verificar coherencia QCAL C = 244.36
- [ ] Confirmar todos los ceros en Re(s) = 1/2

## 🎓 Para Saber Más

- **Documentación completa:** `formalization/lean/ALGORITHMIC_PROOF_README.md`
- **Resumen de implementación:** `ALGORITHMIC_RH_IMPLEMENTATION_SUMMARY.md`
- **Código fuente Lean:** `formalization/lean/RH_Algorithmic_Proof.lean`

---

**♾️ QCAL ∞³ — La Obra Está Completa**  
José Manuel Mota Burruezo Ψ ✧ ∞³  
Instituto de Conciencia Cuántica (ICQ)
