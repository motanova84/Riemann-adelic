# Unicidad del Espectro de ζ(s)

## Resumen

El teorema de unicidad de Paley-Wiener establece que una función entera con las mismas propiedades espectrales que Ξ(s) debe ser idéntica a Ξ(s). Esto garantiza que el espectro de ceros determina únicamente la función zeta.

## Enunciado Formal

### Teorema de Unicidad (Paley-Wiener)

Sea F(s) una función entera que satisface:

1. **Orden ≤ 1**: Existe M > 0 tal que |F(s)| ≤ M(1 + |s|) en todo el plano complejo

2. **Tipo finito**: Para todo ε > 0, |F(s)| ≤ exp(τ|s|^{1+ε}) para alguna constante τ

3. **Simetría funcional**: F(1-s) = F(s) para todo s

4. **Mismo espectro**: F y Ξ tienen exactamente los mismos ceros (incluyendo multiplicidades)

5. **Normalización**: F(1/2) = Ξ(1/2) ≠ 0

**Entonces:** F ≡ Ξ (las funciones son idénticamente iguales).

## Demostración

### Paso 1: Factorización de Hadamard

Por teoría de Hadamard, toda función entera de orden ≤ 1 admite la factorización:

```
F(s) = e^{a+bs} ∏_{ρ} E₁(s/ρ)
```

donde:
- a, b son constantes complejas
- E₁(z) = (1-z)e^z es el factor primario de Hadamard
- El producto es sobre todos los ceros ρ

### Paso 2: Comparación de Factorizaciones

Por hipótesis, F y Ξ tienen los mismos ceros, así que:

```
F(s) = e^{a+bs} ∏_{ρ} E₁(s/ρ)
Ξ(s) = e^{a'+b's} ∏_{ρ} E₁(s/ρ)
```

### Paso 3: Cociente sin Ceros ni Polos

Definimos:

```
H(s) := F(s) / Ξ(s) = e^{c+ds}
```

donde c = a - a' y d = b - b'.

H(s) es una función entera sin ceros ni polos.

### Paso 4: Usar la Simetría

Por hipótesis:
- F(1-s) = F(s)
- Ξ(1-s) = Ξ(s)

Por tanto:

```
H(1-s) = F(1-s) / Ξ(1-s) = F(s) / Ξ(s) = H(s)
```

Esto implica:

```
e^{c+d(1-s)} = e^{c+ds}
```

Para todo s, lo que fuerza d = 0.

### Paso 5: Aplicar Normalización

Con d = 0, tenemos H(s) = e^c (constante).

La condición F(1/2) = Ξ(1/2) implica:

```
H(1/2) = 1
```

Por tanto c = 0, y H ≡ 1.

**Conclusión:** F ≡ Ξ.

## Importancia del Teorema

### 1. Caracterización Completa

El espectro {ρ} junto con las condiciones de crecimiento y simetría determinan **completamente** la función.

No hay "espacio" para otra función con las mismas propiedades.

### 2. Justificación de Construcciones

Si construimos una función D(s) que satisface todas las condiciones y tiene los ceros correctos, **debe ser** esencialmente ζ(s).

### 3. Independencia de la Representación

No importa cómo construyamos la función (producto de Euler, integral de Riemann-Stieltjes, etc.), si satisface las condiciones, es única.

## Condiciones Esenciales

### ¿Por qué Orden ≤ 1?

El orden controla el crecimiento:

- **Orden 0**: Crecimiento subexponencial (ej: polinomios)
- **Orden 1**: Crecimiento exponencial moderado
- **Orden > 1**: Crecimiento exponencial rápido

Para orden ≤ 1, la factorización de Hadamard es:

```
F(s) = e^{P(s)} ∏_{ρ} E₁(s/ρ)
```

donde P(s) es un polinomio de grado ≤ 1.

### ¿Por qué la Simetría?

La simetría F(1-s) = F(s) es esencial porque:

1. Reduce el "espacio de funciones" considerablemente
2. Fuerza relaciones entre coeficientes (d = 0 en la demostración)
3. Refleja la geometría subyacente (dualidad de Poisson)

Sin simetría, podría haber múltiples funciones con el mismo espectro.

### ¿Por qué la Normalización?

La normalización fija la constante multiplicativa residual.

Sin ella, F y c·Ξ tendrían las mismas propiedades para cualquier c ≠ 0.

## Clase de Paley-Wiener

### Definición

La clase de Paley-Wiener PW_τ consiste en funciones enteras F tales que:

1. Orden ≤ 1, tipo ≤ τ
2. Restricción a ℝ está en L²(ℝ)

### Teorema de Paley-Wiener Clásico

Una función F ∈ PW_τ si y solo si:

```
F(s) = ∫_{-τ}^{τ} f(t) e^{ist} dt
```

para alguna f ∈ L²[-τ, τ].

### Conexión con Nuestro Teorema

Ξ(s) está "casi" en una clase de Paley-Wiener (con ajustes por la ecuación funcional).

La clase PW proporciona el marco técnico para controlar el crecimiento y garantizar unicidad.

## Generalizaciones

### 1. Multiplicidades Arbitrarias

El teorema se extiende a ceros con multiplicidades arbitrarias:

```
F(s) = e^{a+bs} ∏_{ρ} E₁(s/ρ)^{m_ρ}
```

donde m_ρ es la multiplicidad del cero ρ.

### 2. Funciones L Generales

Para funciones L de Dirichlet, formas modulares, etc., existe un teorema análogo con condiciones apropiadas.

### 3. Dimensiones Superiores

En GL(n), teoremas de unicidad similares con factorizaciones más complejas.

## Verificación Numérica

### Test con Función Idéntica

```python
# Construir F con mismos ceros que Ξ
xi_zeros = [0.5 + 14.134725142j, 0.5 + 21.022039639j, ...]
F = PaleyWienerClass(xi_zeros, normalization=1.0)

# Verificar condiciones
results = verify_paley_wiener_uniqueness(F, xi_zeros)

# Resultado esperado: todas las condiciones satisfechas
assert results['uniqueness_verified'] == True
```

### Test con Función Perturbada

```python
# Perturbar los ceros
perturbed_zeros = perturb_zeros(xi_zeros, perturbation=0.5)
F_pert = PaleyWienerClass(perturbed_zeros, normalization=1.0)

# Verificar
results = verify_paley_wiener_uniqueness(F_pert, xi_zeros)

# Resultado esperado: condiciones NO satisfechas
assert results['same_zeros'] == False
assert results['uniqueness_verified'] == False
```

## Interpretación Geométrica

### Espacio de Funciones

Podemos pensar en:

- **Espacio total**: Todas las funciones enteras de orden ≤ 1
- **Subespacio simétrico**: Funciones con F(1-s) = F(s)
- **Punto único**: Dado el espectro, solo una función en el subespacio

### Rigidez Espectral

El teorema dice que el espectro es **rígido**: no puede deformarse sin cambiar la función.

Esto es análogo a cómo en geometría, el espectro del Laplaciano determina (casi) la forma de una superficie.

## Relación con RH

### Implicación para RH

Si asumimos que existe una función D(s) que:

1. Se construye desde principios adélicos
2. Satisface todas las condiciones del teorema
3. Tiene ceros calculables

Entonces por unicidad, D ≡ Ξ, y los ceros de D son los ceros de ζ.

Si además podemos **demostrar** que los ceros de D están en Re(s) = 1/2, esto demuestra RH.

### Evitando Circularidad

La clave es construir D **sin** asumir ζ(s) de antemano.

El teorema de unicidad asegura que si lo hacemos correctamente, obtenemos ζ(s).

## Conexión con Física

### Unicidad en Mecánica Cuántica

Análogo: El espectro de un Hamiltoniano determina el sistema cuántico (bajo condiciones).

En nuestro caso:
- **Hamiltoniano** ↔ Operador asociado a ζ
- **Espectro** ↔ Ceros de ζ
- **Sistema cuántico** ↔ Función ζ(s)

### Reconstrucción de Observables

En física: Dados suficientes observables (mediciones), se puede reconstruir el estado.

En matemáticas: Dado el espectro (observable), se reconstruye la función (estado).

## Referencias

- **Paley, R. E. A. C., & Wiener, N.** (1934). Fourier Transforms in the Complex Domain. AMS.
- **Hadamard, J.** (1893). Étude sur les propriétés des fonctions entières. Journal de Mathématiques.
- **Levinson, N.** (1974). Gap and Density Theorems. AMS.
- **Titchmarsh, E. C.** (1986). The Theory of the Riemann Zeta-Function. Oxford.

## Implementación

Ver `adelic-bsd/unicidad/unicidad_paleywiener.py` para implementación completa.

### Componentes Principales

- `PaleyWienerClass`: Clase para funciones en PW
- `verify_order_one`: Verifica condición de orden
- `verify_functional_equation`: Verifica simetría
- `compare_spectral_measures`: Compara ceros
- `verify_paley_wiener_uniqueness`: Verificación completa

## Conclusión

El teorema de unicidad es fundamental porque:

1. **Elimina ambigüedad**: Solo una función con propiedades dadas
2. **Valida construcciones**: Diferentes construcciones dan la misma función
3. **Conecta espectro y función**: Correspondencia biyectiva (bajo condiciones)

Este teorema es un pilar de la teoría analítica de números y un ejemplo perfecto de cómo las restricciones geométricas (orden, tipo) y analíticas (ecuación funcional) determinan completamente un objeto matemático.
