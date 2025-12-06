# Unicidad Paley-Wiener

## Descripción

Este módulo implementa el **teorema de unicidad de Paley-Wiener** que establece que una función con las mismas propiedades espectrales que Ξ(s) debe ser idéntica a Ξ(s).

## Teorema Principal

### Teorema de Unicidad (Paley-Wiener)

Sea `F(s)` una función entera que satisface:

1. **Orden ≤ 1**: `|F(s)| ≤ M(1 + |s|)` para alguna constante M
2. **Tipo finito**: Crecimiento controlado en bandas verticales
3. **Simetría funcional**: `F(1-s) = F(s)`
4. **Misma medida espectral**: F y Ξ tienen los mismos ceros (con multiplicidad)
5. **Normalización**: `F(1/2) = Ξ(1/2) ≠ 0`

Entonces `F ≡ Ξ`.

### Demostración (Esquema)

Por teoría de Hadamard para funciones enteras de orden ≤ 1:

```
F(s) = e^{a+bs} ∏_ρ E₁(s/ρ)
Ξ(s) = e^{a'+b's} ∏_ρ E₁(s/ρ)
```

donde `E₁(z) = (1-z)e^z` es el factor primario de Hadamard.

Por hipótesis, los productos son sobre los mismos ceros, así que:

```
H(s) := F(s)/Ξ(s) = e^{c+ds}
```

La simetría implica `H(1-s) = H(s)`, lo que fuerza `d = 0`.
La normalización fija `H ≡ 1`, por tanto `F ≡ Ξ`.

## Clase Principal

### `PaleyWienerClass`

Representa una función en la clase de Paley-Wiener.

**Métodos:**

#### `__init__(zeros, normalization)`

Inicializa una función desde sus ceros.

**Parámetros:**
- `zeros`: Lista de ceros (complejos)
- `normalization`: Constante multiplicativa

#### `construct_from_zeros(s)`

Construye F(s) desde la factorización de Hadamard.

```python
F(s) = C ∏_ρ E₁(s/ρ)
```

#### `verify_order_one(test_points)`

Verifica que `|F(s)| ≤ M(1 + |s|)`.

**Returns:**
- Tupla `(es_orden_uno, max_ratio)`

#### `verify_functional_equation(test_points, tolerance)`

Verifica que `F(1-s) = F(s)`.

**Returns:**
- Tupla `(satisface, lista_errores)`

## Funciones de Utilidad

### `compare_spectral_measures(zeros_F, zeros_Xi, tolerance)`

Compara las medidas espectrales de dos funciones.

**Returns:**
- Tupla `(son_iguales, info_detallada)`

### `verify_paley_wiener_uniqueness(F, Xi_zeros, F_at_half, Xi_at_half)`

Verifica todas las condiciones del teorema de unicidad.

**Returns:**
- Diccionario con resultados de verificación completos

### `perturb_zeros(zeros, perturbation)`

Perturba ceros para crear una función diferente (útil para tests).

### `uniqueness_demo(xi_zeros, num_zeros)`

Demostración completa del teorema de unicidad.

**Returns:**
- Diccionario comparando función idéntica vs. perturbada

## Ejemplo de Uso

```python
from unicidad_paleywiener import (
    PaleyWienerClass, verify_paley_wiener_uniqueness,
    uniqueness_demo
)

# Ceros de Ξ(s) en la línea crítica
riemann_zeros_gamma = [14.134725142, 21.022039639, 25.010857580, ...]
xi_zeros = [complex(0.5, gamma) for gamma in riemann_zeros_gamma]

# Crear función con los mismos ceros que Ξ
F = PaleyWienerClass(xi_zeros[:10], normalization=1.0)

# Verificar unicidad
results = verify_paley_wiener_uniqueness(F, xi_zeros[:10])

print(f"Orden ≤ 1: {results['order_one']}")
print(f"Ecuación funcional: {results['functional_equation']}")
print(f"Mismos ceros: {results['same_zeros']}")
print(f"Unicidad verificada: {results['uniqueness_verified']}")

# Demostración con función perturbada
demo_results = uniqueness_demo(xi_zeros, num_zeros=10)
print(f"\nFunción idéntica: {demo_results['identical_function']}")
print(f"Función perturbada: {demo_results['perturbed_function']}")
```

## Tests

Ejecutar los tests con:

```bash
pytest adelic-bsd/unicidad/tests_unicidad.py -v
```

Los tests verifican:
1. Construcción de funciones desde ceros
2. Verificación de orden ≤ 1
3. Ecuación funcional F(1-s) = F(s)
4. Comparación de medidas espectrales
5. Teorema de unicidad completo
6. Comportamiento con perturbaciones
7. Factorización de Hadamard

## Interpretación Matemática

### Significado de la Unicidad

El teorema establece que el espectro (ceros) determina completamente la función, siempre que:

1. **Control de crecimiento**: La función no crece demasiado rápido
2. **Simetría**: Refleja la dualidad geométrica
3. **Normalización**: Fija la escala

Esto es análogo a cómo en mecánica cuántica, el espectro de un operador hamiltoniano determina el sistema físico (bajo ciertas condiciones).

### Factorización de Hadamard

Para funciones enteras de orden ≤ 1, la representación:

```
F(s) = e^{a+bs} ∏_ρ (1 - s/ρ) e^{s/ρ}
```

es la forma canónica. Los factores `E₁(s/ρ) = (1 - s/ρ)e^{s/ρ}` aseguran convergencia absoluta del producto infinito.

### Clase de Paley-Wiener

La clase PW comprende funciones que son transformadas de Fourier de distribuciones con soporte compacto. En nuestro contexto:

- **Orden ≤ 1**: Crecimiento a lo más lineal
- **Tipo finito**: Controla la "velocidad" del crecimiento exponencial
- **Estas condiciones** permiten la factorización de Hadamard y garantizan unicidad

## Referencias

- **Paley, R. E. A. C., & Wiener, N.** (1934). *Fourier Transforms in the Complex Domain*. American Mathematical Society Colloquium Publications, Vol. 19.

- **Hadamard, J.** (1893). *Étude sur les propriétés des fonctions entières et en particulier d'une fonction considérée par Riemann*. Journal de Mathématiques Pures et Appliquées, 9, 171-215.

- **Levinson, N.** (1974). *Gap and Density Theorems*. American Mathematical Society Colloquium Publications, Vol. 26.

- **Titchmarsh, E. C.** (1986). *The Theory of the Riemann Zeta-Function* (2nd ed.). Oxford University Press.

## Aplicaciones

### 1. Prueba de Unicidad de ζ(s)

El teorema garantiza que si construimos una función D(s) con las propiedades correctas, y resulta tener los mismos ceros que ζ(s), entonces debe ser (esencialmente) ζ(s).

### 2. Verificación de Conjeturas

Si podemos demostrar que una función candidata satisface todas las condiciones y tiene los ceros esperados, el teorema de unicidad garantiza que es la función correcta.

### 3. Construcciones Alternativas

Permite verificar que construcciones alternativas de ζ(s) (vía producto de Euler, integral de Riemann-Stieltjes, etc.) son equivalentes.

## Notas Técnicas

- La verificación numérica de orden ≤ 1 usa muestreo en bandas verticales
- La ecuación funcional se verifica en puntos de prueba representativos
- Tolerancias típicas: 10^{-6} para ecuación funcional, 10^{-10} para ceros
- La perturbación de ceros es útil para tests negativos (demostrar que ceros diferentes → funciones diferentes)

## Conexión con Otros Módulos

- **inversion**: La unicidad garantiza que la medida reconstruida es única
- **dualidad**: La ecuación funcional es condición necesaria de unicidad
- **operador**: El espectro del operador H determina únicamente el operador (bajo condiciones análogas)
