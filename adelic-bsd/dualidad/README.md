# Principio de Dualidad de Poisson

## Descripción

Este módulo implementa el **principio geométrico de dualidad de Poisson**, que demuestra cómo la simetría geométrica `x ↔ 1/x` fuerza la ecuación funcional `D(s) = D(1-s)` de la función zeta.

## Concepto Matemático

### La Involución de Poisson

El operador fundamental es:

```
J: f(x) ↦ x^{-1/2} f(1/x)
```

**Propiedad clave:** `J² = Id` (involución)

Esta propiedad significa que aplicar `J` dos veces devuelve la función original.

### Conexión con la Ecuación Funcional

La dualidad `x ↔ 1/x` se manifiesta a nivel espectral como:

```
M[J f](s) = M[f](1-s)
```

donde `M[f]` denota la transformada de Mellin de `f`.

Si una función `D(s)` proviene de una distribución geométrica invariante bajo `J`, entonces:

```
D(s) = D(1-s)
```

### Factor Arquimediano

El factor gamma que aparece en la ecuación funcional de ζ(s) es:

```
Γ_ℝ(s) = π^{-s/2} Γ(s/2)
```

Este factor satisface:

```
Γ_ℝ(s) / Γ_ℝ(1-s) = π^{s-1/2}
```

## Funciones Principales

### `poisson_involution(f, x)`

Aplica el operador de Poisson a una función.

**Parámetros:**
- `f`: Función a transformar
- `x`: Punto de evaluación

**Returns:**
- Valor de `J f(x) = x^{-1/2} f(1/x)`

### `verify_involution(f, x, tolerance)`

Verifica que `J² = Id`.

**Parámetros:**
- `f`: Función de prueba
- `x`: Punto de evaluación
- `tolerance`: Tolerancia numérica

**Returns:**
- Tupla `(es_involucion, error_relativo)`

### `gamma_factor_computation(s)`

Calcula el factor gamma `Γ_ℝ(s) = π^{-s/2} Γ(s/2)`.

**Parámetros:**
- `s`: Parámetro complejo

**Returns:**
- Valor de `Γ_ℝ(s)`

### `verify_gamma_factor_functional_equation(s, tolerance)`

Verifica la ecuación funcional del factor gamma.

**Parámetros:**
- `s`: Parámetro complejo
- `tolerance`: Tolerancia numérica

**Returns:**
- Tupla `(satisface, error_relativo)`

## Ejemplo de Uso

```python
from dualidad_poisson import (
    poisson_involution, verify_involution, 
    gamma_factor_computation,
    verify_gamma_factor_functional_equation
)
import mpmath as mp

# Definir función de prueba (gaussiana)
def gaussian(x):
    return mp.exp(-x * x)

# Verificar que J² = Id
x = 2.0
is_involution, error = verify_involution(gaussian, x)
print(f"¿J² = Id? {is_involution} (error: {error:.2e})")

# Calcular factor gamma
s = mp.mpc(0.5, 14.134)  # En un cero de zeta
gamma_s = gamma_factor_computation(s)
print(f"Γ_ℝ({s}) = {gamma_s}")

# Verificar ecuación funcional
satisfies, error = verify_gamma_factor_functional_equation(s)
print(f"¿Satisface ecuación funcional? {satisfies} (error: {error:.2e})")
```

## Tests

Ejecutar los tests con:

```bash
pytest adelic-bsd/dualidad/tests_dualidad.py -v
```

Los tests verifican:
1. Propiedad de involución `J² = Id`
2. Comportamiento con diferentes funciones de prueba
3. Propiedades del núcleo de Mellin
4. Ecuación funcional del factor gamma `Γ_ℝ(s)`
5. Comportamiento en la línea crítica
6. Relación entre `M[J f]` y `M[f]`

## Interpretación Geométrica

### Dualidad x ↔ 1/x

La transformación `x ↦ 1/x` es una simetría fundamental:

- **Geométricamente**: Inversión respecto al círculo unitario
- **Analíticamente**: Intercambia `x → 0` con `x → ∞`
- **Espectralmente**: Intercambia `s` con `1-s`

### Factor x^{-1/2}

El factor `x^{-1/2}` es esencial para:

1. Preservar medidas: `dx/x` es invariante bajo `x ↦ 1/x`
2. Hacer `J` autoadjunto respecto a la medida apropiada
3. Centrar la simetría en `x = 1`

## Aplicaciones

### 1. Ecuación Funcional de ζ(s)

La ecuación funcional clásica:

```
ξ(s) = ξ(1-s)
```

donde `ξ(s) = (s(s-1)/2) π^{-s/2} Γ(s/2) ζ(s)` es consecuencia directa de la dualidad de Poisson aplicada a la distribución de primos.

### 2. Teoría de Tate

En la teoría de Tate para funciones L, la dualidad de Poisson se generaliza al caso adélico:

```
f(g) ↦ ∫ f(h) ψ(hg) dh
```

donde `ψ` es un carácter aditivo no trivial.

### 3. Correspondencia Modular

La dualidad `τ ↦ -1/τ` en el semiplano superior es análoga a la dualidad de Poisson y está en el corazón de la teoría de formas modulares.

## Referencias

- **Tate, J.** (1950). *Fourier analysis in number fields and Hecke's zeta-functions*. Princeton PhD thesis.

- **Weil, A.** (1964). *Sur la formule de Siegel dans la théorie des groupes classiques*. Acta Mathematica, 113, 1-87.

- **Godement, R., & Jacquet, H.** (1972). *Zeta functions of simple algebras*. Lecture Notes in Mathematics, 260.

- **Connes, A.** (1999). *Trace formula in noncommutative geometry*. Selecta Mathematica, 5(1), 29-106.

## Notas Técnicas

- La involución es exacta: `J² = Id` de manera algebraica
- En la práctica numérica, se verifican errores < 10^{-10}
- El factor gamma requiere cuidado cerca de polos de Γ(s/2)
- La transformada de Mellin converge en bandas verticales específicas
- Para funciones bien comportadas, la dualidad es numéricamente estable

## Conexión con Otros Módulos

- **inversion**: La dualidad justifica por qué el núcleo K_D es hermítico
- **unicidad**: La ecuación funcional es una condición de unicidad clave
- **operador**: El operador H hereda la simetría de la dualidad
