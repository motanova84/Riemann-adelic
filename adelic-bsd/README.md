# adelic-bsd: Módulos BSD para Análisis Adélico de la Hipótesis de Riemann

## Descripción General

Este directorio contiene una implementación modular completa de las técnicas matemáticas fundamentales para el análisis de la Hipótesis de Riemann via métodos adélicos. Los módulos están organizados según los cuatro pilares principales de la teoría:

1. **Inversión Espectral**: Teorema que conecta ceros con primos
2. **Dualidad de Poisson**: Principio geométrico que fuerza la ecuación funcional
3. **Unicidad de Paley-Wiener**: Caracterización única del espectro
4. **Operador No Circular**: Construcción explícita del operador RH

## Estructura del Proyecto

```
adelic-bsd/
│
├── inversion/              # Teorema de inversión espectral
│   ├── inversion_spectral.py
│   ├── tests_inversion.py
│   └── README.md
│
├── dualidad/               # Principio geométrico de dualidad
│   ├── dualidad_poisson.py
│   ├── tests_dualidad.py
│   └── README.md
│
├── unicidad/               # Caracterización única del espectro
│   ├── unicidad_paleywiener.py
│   ├── tests_unicidad.py
│   └── README.md
│
├── operador/               # Construcción del operador RH
│   ├── operador_H.py
│   ├── tests_operador.py
│   └── README.md
│
└── docs/                   # Documentación matemática detallada
    ├── Teorema_Inversion.md
    ├── Principio_Geometrico.md
    ├── Unicidad_Espectro.md
    └── Operador_NoCircular.md
```

## Módulos

### 1. inversion/: Inversión Espectral (Primos ← Ceros)

**Idea Principal**: Recuperar la distribución de números primos desde los ceros de ζ(s).

**Componentes**:
- `construct_K_D(D, x, y, zeros, t)`: Construye núcleo espectral con ventana gaussiana e^{-tΔ}
- `prime_measure_from_zeros(D, zeros, t)`: Recupera medida Π_D aproximada
- `verify_prime_peaks(x_values, measure, primes)`: Verifica picos en log(p)

**Test Principal**:
Verificar que con los primeros 50 ceros de Ξ se recuperan picos en log(p) para primos p.

**Documentación**: [inversion/README.md](inversion/README.md)

### 2. dualidad/: Dualidad de Poisson (Geometría ⇒ Ecuación Funcional)

**Idea Principal**: La simetría x ↔ 1/x fuerza D(s) = D(1-s).

**Componentes**:
- `poisson_involution(f, x)`: Operador J: f(x) ↦ x^{-1/2} f(1/x)
- `verify_involution(f, x)`: Verifica J² = Id
- `gamma_factor_computation(s)`: Calcula Γ_ℝ(s) = π^{-s/2} Γ(s/2)
- `verify_gamma_factor_functional_equation(s)`: Verifica ecuación funcional

**Test Principal**:
Reproducir el factor arquimediano Γ_ℝ(s) y su ecuación funcional.

**Documentación**: [dualidad/README.md](dualidad/README.md)

### 3. unicidad/: Unicidad de Paley-Wiener

**Idea Principal**: Dos distribuciones de Weil con mismo espectro son idénticas.

**Componentes**:
- `PaleyWienerClass`: Clase para funciones enteras de orden ≤ 1
- `verify_order_one()`: Verifica |F(s)| ≤ M(1 + |s|)
- `verify_functional_equation()`: Verifica F(1-s) = F(s)
- `compare_spectral_measures()`: Compara ceros (con multiplicidad)
- `verify_paley_wiener_uniqueness()`: Verificación completa

**Test Principal**:
Comparar Ξ(s) con función perturbada y verificar que fallan las condiciones de unicidad.

**Documentación**: [unicidad/README.md](unicidad/README.md)

### 4. operador/: Operador No Circular

**Idea Principal**: Construir operador H cuyo espectro da ceros, sin asumir ζ(s).

**Componentes**:
- `heat_kernel(x, y, t)`: Núcleo K_t(x,y) de difusión térmica
- `regularization_operator_R_t()`: Operador de regularización
- `involution_operator_J()`: Operador de dualidad
- `construct_operator_H()`: Construcción completa: H = (R_t + J R_t J†)/2
- `diagonalize_operator()`: Cálculo del espectro
- `spectrum_to_zeros()`: Conversión λ_n → t_n via λ_n = 1/4 + t_n²

**Test Principal**:
Diagonalización truncada → espectro ≈ primeros ceros de ζ (con error ~5-20%).

**Documentación**: [operador/README.md](operador/README.md)

## Instalación y Uso

### Requisitos

```bash
pip install mpmath numpy scipy sympy pytest
```

### Ejecutar Tests

Cada módulo tiene su suite de tests:

```bash
# Desde el directorio raíz del proyecto
cd adelic-bsd

# Test inversión
cd inversion && python -m pytest tests_inversion.py -v

# Test dualidad
cd ../dualidad && python -m pytest tests_dualidad.py -v

# Test unicidad
cd ../unicidad && python -m pytest tests_unicidad.py -v

# Test operador
cd ../operador && python -m pytest tests_operador.py -v
```

### Ejemplo de Uso

```python
import sys
sys.path.insert(0, 'adelic-bsd/inversion')
sys.path.insert(0, 'adelic-bsd/operador')

from inversion_spectral import prime_measure_from_zeros
from operador_H import construct_operator_H, diagonalize_operator

# Ceros conocidos de ζ(s)
zeros = [14.134725142, 21.022039639, 25.010857580, ...]

# 1. Inversión: Ceros → Primos
x_vals, measure = prime_measure_from_zeros(D=1.0, zeros=zeros, t=0.5)

# 2. Operador: Geometría → Espectro
import numpy as np
x_grid = np.linspace(0.1, 5.0, 50)
H = construct_operator_H(x_grid, t=0.2)
eigenvalues, eigenvectors = diagonalize_operator(H)

print(f"Primeros eigenvalues: {eigenvalues[:5]}")
```

## Documentación Matemática

El directorio `docs/` contiene explicaciones detalladas con matemáticas formales:

- [Teorema de Inversión](docs/Teorema_Inversion.md): Demostración completa del teorema de inversión espectral
- [Principio Geométrico](docs/Principio_Geometrico.md): Dualidad de Poisson y ecuación funcional
- [Unicidad del Espectro](docs/Unicidad_Espectro.md): Teorema de Paley-Wiener con demostración
- [Operador No Circular](docs/Operador_NoCircular.md): Construcción rigurosa del operador H

## Filosofía del Diseño

### Modularidad

Cada módulo es independiente y puede usarse por separado. Las dependencias entre módulos son mínimas.

### No Circularidad

**Crítico**: El módulo `operador/` construye H **sin asumir** la función ζ(s). Solo usa:
- Geometría del espacio logarítmico
- Difusión térmica (física estándar)
- Dualidad de Poisson (geometría)
- Álgebra lineal (diagonalización)

### Testeo Exhaustivo

Cada módulo tiene >10 tests que verifican:
- Propiedades matemáticas básicas
- Consistencia numérica
- Casos borde
- Funcionalidad principal

### Documentación Rigurosa

Cada función está documentada con:
- Descripción matemática precisa
- Parámetros con tipos
- Returns con interpretación
- Referencias a teoría subyacente

## Conexión con la Hipótesis de Riemann

### Flujo Lógico

1. **Construir H** (operador) desde principios geométricos → espectro {λ_n}
2. **Convertir** espectro → aproximaciones de ceros {t_n} via λ_n = 1/4 + t_n²
3. **Verificar inversión**: Desde {t_n}, recuperar distribución de primos
4. **Aplicar unicidad**: Si la construcción satisface todas las condiciones, debe ser ζ(s)
5. **Dualidad**: La ecuación funcional emerge de geometría, no es postulada

### Evitando Circularidad

El enfoque es fundamentalmente diferente de:

❌ **Circular**: Tomar ceros conocidos de ζ → construir operador → "demostrar" conexión

✓ **No Circular**: Geometría → operador H → espectro → identificar con ζ por unicidad

## Referencias

- **Connes, A.** (1999). Trace formula in noncommutative geometry. Selecta Mathematica, 5(1), 29-106.
- **Weil, A.** (1952). Sur les "formules explicites". Meddelanden från Lunds Universitets Matematiska Seminarium.
- **Tate, J.** (1950). Fourier analysis in number fields. Princeton PhD thesis.
- **Paley & Wiener** (1934). Fourier Transforms in the Complex Domain. AMS.
- **Berry & Keating** (1999). The Riemann zeros and eigenvalue asymptotics. SIAM Review, 41(2), 236-266.

## Contribuciones

Este código implementa ideas de:
- Teoría analítica de números clásica (Weil, Selberg)
- Geometría no conmutativa (Connes)
- Física matemática (Berry-Keating)
- Análisis armónico (Tate, Godement-Jacquet)

## Licencia

Ver LICENSE en el directorio raíz del proyecto.

## Contacto

Para preguntas sobre la implementación, abrir un issue en el repositorio de GitHub.

Para discusión matemática, consultar las referencias y la documentación en `docs/`.

---

**Nota**: Este es un proyecto de investigación matemática. Los métodos numéricos tienen limitaciones conocidas y están documentadas en cada módulo.
