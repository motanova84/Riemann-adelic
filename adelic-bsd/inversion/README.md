# Teorema de Inversión Espectral

## Descripción

Este módulo implementa el **teorema de inversión espectral** que permite recuperar la distribución de números primos a partir de los ceros de la función Ξ(s) de Riemann.

## Concepto Matemático

El teorema establece una correspondencia fundamental:

```
Espectro (ceros de Ξ) ⟷ Geometría (distribución de primos)
```

### Construcción del Núcleo

El núcleo espectral se construye usando una ventana gaussiana:

```
K_D(x,y) = (2πt)^{-1/2} ∑_γ e^{-tγ²} e^{iγ(x-y)}
```

donde:
- `γ` son las partes imaginarias de los ceros no triviales de ζ(s)
- `t` es el parámetro de escala temporal (difusión)
- La ventana `e^{-tγ²}` regulariza la suma

### Recuperación de la Medida de Primos

La medida de primos Π_D se recupera de la traza del núcleo:

```
Π_D(x) ≈ K_D(x,x)
```

Esta medida tiene picos en `x = log(p)` para cada primo `p`.

## Funciones Principales

### `construct_K_D(D, x, y, zeros, t)`

Construye el núcleo espectral K_D(x,y).

**Parámetros:**
- `D`: Parámetro del divisor
- `x, y`: Coordenadas espaciales
- `zeros`: Lista de ceros (partes imaginarias γ)
- `t`: Parámetro temporal (default 1.0)

**Returns:**
- Valor complejo del núcleo

### `prime_measure_from_zeros(D, zeros, t, max_log_p, num_points)`

Recupera la aproximación de la medida de primos Π_D.

**Parámetros:**
- `D`: Parámetro del divisor
- `zeros`: Lista de ceros de Ξ(s)
- `t`: Parámetro de escala temporal
- `max_log_p`: Rango máximo de log(p)
- `num_points`: Número de puntos de discretización

**Returns:**
- Tupla `(x_values, measure_values)`

### `verify_prime_peaks(x_values, measure_values, expected_primes, tolerance)`

Verifica que la medida reconstruida tenga picos en log(p).

**Parámetros:**
- `x_values`: Puntos en log(p)
- `measure_values`: Valores de la medida
- `expected_primes`: Lista de primos esperados
- `tolerance`: Tolerancia para detección de picos

**Returns:**
- Lista de tuplas `(primo, encontrado, posición)`

## Ejemplo de Uso

```python
from inversion_spectral import prime_measure_from_zeros, verify_prime_peaks

# Primeros 50 ceros de ζ(s)
zeros = [14.134725142, 21.022039639, 25.010857580, ...]

# Recuperar medida de primos
x_vals, measure_vals = prime_measure_from_zeros(
    D=1.0, 
    zeros=zeros, 
    t=0.5, 
    max_log_p=4.0, 
    num_points=200
)

# Verificar picos en primos
primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
verification = verify_prime_peaks(x_vals, measure_vals, primes)

for p, found, pos in verification:
    if found:
        print(f"✓ Primo {p} encontrado en log(p) ≈ {pos:.3f}")
```

## Tests

Ejecutar los tests con:

```bash
pytest adelic-bsd/inversion/tests_inversion.py -v
```

Los tests verifican:
1. Propiedades del núcleo gaussiano (simetría, normalización)
2. Hermiticidad del núcleo K_D
3. Comportamiento de difusión con t
4. Recuperación de picos en log(p) para los primeros primos
5. Estabilidad numérica

## Referencias

- **Connes, A.** (1999). *Trace formula in noncommutative geometry and the zeros of the Riemann zeta function*. Selecta Mathematica, 5(1), 29-106.

- **Weil, A.** (1952). *Sur les "formules explicites" de la théorie des nombres premiers*. Meddelanden från Lunds Universitets Matematiska Seminarium.

- **Selberg, A.** (1956). *Harmonic analysis and discontinuous groups in weakly symmetric Riemannian spaces with applications to Dirichlet series*. Journal of the Indian Mathematical Society, 20, 47-87.

## Interpretación Física

Este teorema puede interpretarse como:

1. **Mecánica Cuántica**: Los ceros actúan como niveles de energía de un sistema cuántico, y los primos emergen como las órbitas clásicas correspondientes.

2. **Geometría No Conmutativa**: Los primos son los "puntos" de un espacio geométrico cuyo espectro está dado por los ceros.

3. **Correspondencia AdS/CFT**: Versión aritmética de la dualidad holográfica entre espectro (bulk) y primos (frontera).

## Notas Técnicas

- La precisión aumenta con más ceros
- El parámetro `t` controla el compromiso resolución/estabilidad
- Valores típicos: `t ∈ [0.3, 1.0]` para buena detección de primos
- La estabilidad numérica se mantiene hasta ~100 ceros con `mp.dps = 30`
