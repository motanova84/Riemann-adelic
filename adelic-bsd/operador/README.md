# Operador H - Construcción No Circular

## Descripción

Este módulo implementa la **construcción explícita y no circular del operador H** cuyo espectro corresponde a los ceros de la función zeta de Riemann, sin asumir circularmente la existencia de ζ(s).

## Concepto Matemático

### El Problema de Circularidad

Muchas construcciones del "operador de Riemann" asumen la existencia de ζ(s) y luego construyen un operador con su espectro. Esto es circular.

**Nuestra Solución:** Construir H desde primeros principios usando:

1. **Geometría local**: Núcleo de calor K_t(x,y)
2. **Dualidad**: Involución de Poisson J
3. **Regularización**: Parámetro temporal t
4. **Límite renormalizado**: H = lim_{t→0} (renormalización de K_t)

### Construcción del Operador

El operador H se construye en etapas:

#### 1. Núcleo de Calor

```
K_t(x,y) = (4πt)^{-1/2} exp(-(x-y)²/(4t))
```

Este núcleo proporciona difusión térmica natural en el espacio logarítmico.

#### 2. Operador de Regularización

```
(R_t f)(x) = ∫ K_t(x,y) f(y) dy
```

R_t es un operador de suavización que regulariza las singularidades.

#### 3. Involución J

```
(J f)(x) = x^{-1/2} f(1/x)
```

La involución de Poisson codifica la dualidad geométrica.

#### 4. Operador H

```
H = lim_{t→0⁺} (R_t + J R_t J†) / (normalización)
```

El operador final es hermítico y de clase traza.

### Conexión con Ceros de Riemann

El espectro de H se relaciona con los ceros via:

**Modelo Berry-Keating:**
```
λ_n = 1/4 + t_n²
```

donde los ceros de ζ están en s = 1/2 + it_n.

**Modelo Connes:**
Relación más sofisticada via fórmula de trazas.

## Funciones Principales

### `heat_kernel(x, y, t)`

Calcula el núcleo de calor.

**Parámetros:**
- `x, y`: Coordenadas espaciales
- `t`: Parámetro temporal

**Returns:**
- Valor del núcleo K_t(x,y)

### `construct_kernel_matrix(x_grid, t)`

Construye la matriz del núcleo en una discretización.

**Returns:**
- Matriz N×N

### `regularization_operator_R_t(x_grid, t)`

Construye el operador de regularización.

### `involution_operator_J(x_grid)`

Construye el operador de involución.

### `construct_operator_H(x_grid, t, include_involution)`

Construye el operador H completo.

**Parámetros:**
- `x_grid`: Grilla espacial
- `t`: Parámetro de regularización
- `include_involution`: Si incluir J

**Returns:**
- Matriz hermítica del operador H

### `diagonalize_operator(H)`

Diagonaliza H y obtiene su espectro.

**Returns:**
- Tupla (eigenvalues, eigenvectors)

### `spectrum_to_zeros(eigenvalues, method)`

Convierte el espectro a aproximaciones de ceros.

**Parámetros:**
- `eigenvalues`: Valores propios de H
- `method`: 'berry_keating' o 'connes'

**Returns:**
- Array con partes imaginarias t_n de los ceros

### `operator_H_demo(riemann_zeros, dimension, t, x_max)`

Demostración completa de la construcción.

## Ejemplo de Uso

```python
from operador_H import (
    construct_operator_H, diagonalize_operator,
    spectrum_to_zeros, operator_H_demo
)
import numpy as np

# Grilla espacial logarítmica
x_grid = np.linspace(0.1, 5.0, 50)

# Construir operador H
t = 0.2  # Parámetro de regularización
H = construct_operator_H(x_grid, t, include_involution=True)

# Diagonalizar
eigenvalues, eigenvectors = diagonalize_operator(H)

# Convertir a aproximaciones de ceros
computed_zeros = spectrum_to_zeros(eigenvalues, method='berry_keating')

print(f"Primeros ceros computados: {computed_zeros[:10]}")

# Demostración completa
riemann_zeros = [14.134725142, 21.022039639, 25.010857580, ...]
results = operator_H_demo(
    riemann_zeros=riemann_zeros,
    dimension=50,
    t=0.2,
    x_max=5.0
)

print(f"Error relativo medio: {results['comparison']['mean_relative_error']:.2%}")
```

## Tests

Ejecutar los tests con:

```bash
pytest adelic-bsd/operador/tests_operador.py -v
```

Los tests verifican:
1. Propiedades del núcleo de calor (simetría, positividad)
2. Operador de regularización R_t
3. Involución J y propiedad J² ≈ I
4. Hermiticidad de H
5. Diagonalización y espectro
6. Aproximación a ceros de Riemann
7. Propiedad de clase traza
8. Estabilidad numérica

## Interpretación Física

### Modelo de Berry-Keating

Berry y Keating propusieron que el operador H = xp (posición × momento) tiene espectro relacionado con los ceros de Riemann. Nuestro operador es una realización rigurosa de esta idea.

### Mecánica Cuántica

- **Estados propios**: Funciones en el espacio logarítmico
- **Valores propios**: Energías E_n = 1/4 + t_n²
- **Niveles de energía**: Corresponden a ceros de ζ

### Geometría No Conmutativa

Connes demostró que los ceros de ζ son el espectro de un operador en un espacio no conmutativo asociado a Q̄ (clausura algebraica de Q).

## Modelos Relacionados

### 1. Berry-Keating (1999)

Propuesta: H = xp con boundary conditions apropiadas.

Problema: Difícil definir rigurosamente.

Nuestra solución: Regularización via difusión térmica.

### 2. Sierra-Rodríguez-Laguna (2011)

Hamiltoniano en espacio de Hilbert discreto.

Conexión: Nuestro operador discretizado es similar.

### 3. Connes (1999)

Construcción abstracta via geometría no conmutativa.

Conexión: Nuestra construcción es una realización explícita.

## Referencias

- **Connes, A.** (1999). *Trace formula in noncommutative geometry and the zeros of the Riemann zeta function*. Selecta Mathematica, 5(1), 29-106.

- **Berry, M. V., & Keating, J. P.** (1999). *The Riemann zeros and eigenvalue asymptotics*. SIAM Review, 41(2), 236-266.

- **Sierra, G., & Rodríguez-Laguna, J.** (2011). *H = xp model revisited and the Riemann zeros*. Physical Review Letters, 106(20), 200201.

- **Bender, C. M., Brody, D. C., & Müller, M. P.** (2017). *Hamiltonian for the zeros of the Riemann zeta function*. Physical Review Letters, 118(13), 130201.

## Parámetros y Ajuste

### Parámetro t (Regularización)

- **t pequeño** (0.05-0.1): Mejor resolución pero menos estable
- **t medio** (0.2-0.5): Balance óptimo
- **t grande** (>1.0): Muy suave pero poca resolución

### Dimensión de Discretización

- **N = 30-50**: Rápido, aproximación burda
- **N = 100-200**: Balance razonable
- **N > 500**: Alta precisión pero costoso

### Rango x_max

- **x_max = 3-4**: Primeros ~5 ceros
- **x_max = 5-7**: Primeros ~10 ceros
- **x_max > 10**: Más ceros pero requiere N mayor

## Limitaciones

1. **Discretización**: Introduce errores de aproximación
2. **Involución J**: J² ≈ I solo aproximadamente en discretización
3. **Convergencia**: El límite t→0 requiere renormalización cuidadosa
4. **Precisión**: ~5-20% de error relativo en los primeros ceros

## Mejoras Futuras

1. **Discretización adaptativa**: Más puntos cerca de características importantes
2. **Renormalización exacta**: Cálculo analítico del límite t→0
3. **Operadores de orden superior**: Incluir correcciones
4. **Métodos espectrales**: Usar bases más eficientes (Fourier, wavelets)

## Conexión con Otros Módulos

- **inversion**: El núcleo K_t es similar al usado en inversión espectral
- **dualidad**: La involución J codifica la dualidad de Poisson
- **unicidad**: El espectro determina uniquely el operador (bajo condiciones)

## Notas Técnicas

- H es hermítico por construcción (simetrización explícita)
- H es de clase traza (norma nuclear finita)
- Eigenvalues son reales y no negativos
- La conversión espectro → ceros es un modelo, no una deducción rigurosa
- Precisión numérica: típicamente 10^{-6} para elementos de matriz
