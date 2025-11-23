# Simulación del Potencial de Vacío Efectivo

## Descripción

Este módulo implementa la simulación del potencial de vacío efectivo usando parámetros físicos reales de CODATA 2022:

```
E_vac(R_Ψ) = α·R_Ψ^(-4) + β·ζ'(1/2)·R_Ψ^(-2) + γ·Λ²·(R_Ψ·ℓ_P)² + δ·sin²(log(R_Ψ)/log(π))
```

## Archivos

- **`simulate_vacuum_potential.py`**: Script principal de simulación
- **`tests/test_vacuum_potential_simulation.py`**: Suite completa de pruebas (22 tests)
- **`Evac_Rpsi_data.csv`**: Datos de salida para trazabilidad
- **`vacuum_potential_simulation.png`**: Visualización de resultados

## Uso

### Ejecución Básica

```bash
python3 simulate_vacuum_potential.py
```

### Salida

El script genera:

1. **Análisis numérico completo**:
   - Búsqueda del mínimo estable R_Ψ*
   - Cálculo de frecuencia fundamental f₀
   - Verificación de estabilidad (d²E/dR² > 0)
   - Comparación con jerarquía cosmológica
   - Escaneo de parámetros (±10%)

2. **Visualización** (`vacuum_potential_simulation.png`):
   - Potencial completo en escala log-log
   - Zoom alrededor del mínimo
   - Oscilaciones log-periódicas (término fractal)
   - Contribuciones individuales de cada término

3. **Datos CSV** (`Evac_Rpsi_data.csv`):
   - Columnas: R_Ψ (en ℓ_P), E_vac
   - 5000 puntos desde 10⁰ hasta 10⁴⁸ ℓ_P

## Parámetros Físicos (CODATA 2022)

| Símbolo | Significado | Valor |
|---------|-------------|-------|
| ℓ_P | Longitud de Planck | 1.616×10⁻³⁵ m |
| Λ | Constante cosmológica | 1.1×10⁻⁵² m⁻² |
| ζ'(½) | Derivada de zeta en s=1/2 | -0.207886 |
| c | Velocidad de la luz | 2.99792458×10⁸ m/s |

## Coeficientes de Acoplamiento

Los coeficientes α, β, γ, δ son O(1) y ajustables:

- **α = 1.0**: Término UV (Casimir-like)
- **β = 1.0**: Acoplamiento adélico
- **γ = 1.0**: Término cosmológico IR
- **δ = 0.5**: Amplitud fractal
- **b = π**: Base adélica

## Resultados con Parámetros Estándar

Con los valores O(1) estándar, la simulación encuentra:

```
R_Ψ* ≈ 37 ℓ_P
E_vac(R_Ψ*) ≈ -1.32×10⁻⁴
Curvatura: 0.76 (positiva → mínimo estable ✓)
```

### Nota sobre f₀

La frecuencia calculada con estos parámetros es:

```
f₀ = c / (2π·R_Ψ*·ℓ_P) ≈ 8×10⁴⁰ Hz
```

Para obtener f₀ ≈ 141.7001 Hz (como se menciona en el problema original), se requeriría:
- R_Ψ* ≈ 2.08×10⁴⁰ ℓ_P
- Esto requiere ajustar γ a valores mucho menores (~10⁻¹⁸) para compensar la pequeñez de Λ²·ℓ_P² ≈ 10⁻¹²²

## Interpretación Física

### Términos del Potencial

1. **α/R_Ψ⁴** (UV): Divergencia ultravioleta, dominante a escalas pequeñas
2. **β·ζ'(1/2)/R_Ψ²** (Adélico): Acoplamiento con la función zeta de Riemann
3. **γ·Λ²·(R_Ψ·ℓ_P)²** (IR): Término cosmológico, dominante a escalas grandes
4. **δ·sin²(log R_Ψ / log π)** (Fractal): Oscilaciones log-periódicas, simetría adélica

### Estabilidad

La verificación de estabilidad calcula:

```python
d²E/d(log R)² > 0  →  Mínimo estable
```

El resultado positivo confirma que el mínimo encontrado es un mínimo verdadero, no un máximo o punto de silla.

### Jerarquía Cosmológica

La comparación con la escala cosmológica esperada:

```
(ρ_P/ρ_Λ)^(1/2) ≈ 5.9×10⁶⁰
```

muestra que el mínimo ocurre a una escala mucho menor con los parámetros O(1), reflejando el balance natural entre términos UV e IR.

## Tests

Suite de 22 tests que verifican:

✅ Inicialización correcta de parámetros
✅ Cálculo preciso de E_vac(R_Ψ)
✅ Búsqueda de mínimos
✅ Cálculo de frecuencias
✅ Estabilidad numérica
✅ Comparación cosmológica
✅ Escaneo de parámetros
✅ Periodicidad del término fractal
✅ Constantes físicas CODATA
✅ Comportamiento asintótico (UV e IR)
✅ Consistencia numérica

Ejecutar tests:

```bash
pytest tests/test_vacuum_potential_simulation.py -v
```

## Validaciones Complementarias

### 1. Estabilidad Numérica

```python
from numpy import gradient
d2E = gradient(gradient(E_vals, np.log(R_vals)), np.log(R_vals))
print("Curvatura en el mínimo:", d2E[idx_min])
```

Resultado: Curvatura > 0 ✓

### 2. Escaneo de Parámetros

Varía cada parámetro ±10% y observa el efecto en R_Ψ* y f₀.

### 3. Comparación con Teoría

El mínimo emerge del balance entre:
- **Repulsión UV** (α/R⁴): Evita colapso a R→0
- **Atracción adélica** (β·ζ'/R²): Efecto negativo (ζ'<0)
- **Expansión IR** (γ·Λ²·R²): Evita expansión infinita
- **Modulación fractal** (δ·sin²): Oscilaciones log-periódicas

## Referencias

- CODATA 2022: https://physics.nist.gov/cuu/Constants/
- Riemann ζ'(1/2): Valor numérico estándar
- Constante cosmológica Λ: Observaciones cosmológicas

## Autor

José Manuel Mota Burruezo
Octubre 2025

## Licencia

Ver LICENSE en el repositorio principal.
