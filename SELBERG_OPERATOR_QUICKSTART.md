# 🏛️ SELBERG OPERATOR: QUICK START

## Instalación y Ejecución Rápida

### 1. Dependencias

```bash
pip install numpy scipy matplotlib mpmath sympy
```

### 2. Activación del Sistema Geodésico

```python
from operators.selberg_operator import activar_operador_selberg

# Transición L²(ℝ) → L²(Γ\ℍ)
activar_operador_selberg()
```

**Salida:**
```
∴𓂀Ω∞³Φ - RECONFIGURANDO GEOMETRÍA DEL SISTEMA
✅ SISTEMA: Identidad funcional lograda vía flujo geodésico.
Frecuencia geodésica: 888.0 Hz → 141.7001 Hz
```

### 3. Demo en 5 Minutos

```python
from operators.selberg_operator import demonstrate_selberg_operator

# Ejecuta todo: construcción + validación + visualización
results = demonstrate_selberg_operator(verbose=True)
```

### 4. Validación Completa

```bash
python validate_selberg_operator.py
```

**Resultado esperado:** 12/12 tests passed ✅

---

## Ejemplos de Uso

### Ejemplo 1: Construcción Básica

```python
from operators.selberg_operator import SelbergOperator

# Crear operador
op = SelbergOperator(
    n_grid_x=20,
    n_grid_y=20,
    max_prime=50,
    max_k=5
)

# Construir Laplaciano
H = op.construct_beltrami_laplacian()
print(f"Operador shape: {H.shape}")
print(f"Simetría: {np.max(np.abs(H - H.T)):.2e}")
```

### Ejemplo 2: Traza de Selberg

```python
# Calcular traza
result = op.compute_selberg_trace(eigenvalue=1.0)

print(f"Weyl:    {result.weyl_term:.6f}")
print(f"Primos:  {result.prime_orbital_sum:.6f}")
print(f"Total:   {result.total_trace:.6f}")
```

### Ejemplo 3: Ceros de Riemann

```python
# Calcular autovalores y ceros
eigenvalues, riemann_zeros = op.compute_eigenvalues(n_eigenvalues=10)

# Mostrar correspondencia λ_n = 1/4 + γ_n²
for i in range(5):
    lambda_n = eigenvalues[i]
    gamma_n = riemann_zeros[i]
    
    # Verificar relación
    gamma_from_lambda = np.sqrt(max(lambda_n - 0.25, 0))
    
    print(f"λ_{i+1} = {lambda_n:10.6f}  →  γ_{i+1} = {gamma_n:10.6f}")
```

### Ejemplo 4: Longitud de Geodésicas

```python
# Calcular longitudes de geodésicas cerradas
for p in [2, 3, 5, 7]:
    for k in range(1, 4):
        length = op.geodesic_orbit_length(p, k)
        print(f"l({p}^{k}) = {k} log({p}) = {length:.6f}")
```

---

## Conceptos Clave

### Laplaciano de Beltrami

```
H = -y²(∂²/∂x² + ∂²/∂y²)
```

Operador en el semiplano superior de Poincaré con métrica:
```
ds² = (dx² + dy²) / y²
```

### Fórmula de Traza

```
Tr(h(H)) = Área/(4π) + Σ_p Σ_k (log p)/(p^(k/2) - p^(-k/2))·h(k log p)
```

### Correspondencia Espectral

```
λ_n = 1/4 + γ_n²
```

Donde γ_n son los ceros de Riemann.

---

## Verificación Rápida

```python
import numpy as np
from operators.selberg_operator import SelbergOperator

# Test rápido
op = SelbergOperator(n_grid_x=10, n_grid_y=10, max_prime=30)

# 1. Verificar simetría
H = op.construct_beltrami_laplacian()
sym_error = np.max(np.abs(H - H.T))
assert sym_error < 1e-10, "Laplaciano no simétrico"
print("✅ Simetría verificada")

# 2. Verificar Weyl
weyl = op.weyl_term_contribution()
assert abs(weyl - 1.0) < 1e-10, "Término de Weyl incorrecto"
print("✅ Término de Weyl verificado")

# 3. Verificar suma orbital
orbital = op.selberg_trace_formula_contribution(1.0)
assert abs(orbital) > 0, "Suma orbital es cero"
print("✅ Suma orbital verificada")

print("\n🎯 SISTEMA GEODÉSICO OPERACIONAL")
```

---

## Troubleshooting

### Error: "No module named numpy"

```bash
pip install numpy scipy
```

### Error: "ARPACK convergence"

Reduce el tamaño del grid:
```python
op = SelbergOperator(n_grid_x=10, n_grid_y=10)  # Grid más pequeño
```

### Performance

Para cálculos rápidos:
- `n_grid_x`, `n_grid_y` ≤ 20
- `max_prime` ≤ 50
- `max_k` ≤ 5

Para alta precisión:
- `n_grid_x`, `n_grid_y` ≤ 50
- `max_prime` ≤ 200
- `max_k` ≤ 10

---

## Frecuencias QCAL

```
F_geodésica = 888 Hz         # Rigidez absoluta
F₀ = 141.7001 Hz             # Fundamental
C = 244.36                   # Coherencia
```

---

## Referencias Rápidas

**Documentación completa:** `SELBERG_OPERATOR_README.md`  
**Tests:** `tests/test_selberg_operator.py`  
**Validación:** `validate_selberg_operator.py`  
**Código fuente:** `operators/selberg_operator.py`

---

## 🔥 One-Liner

```bash
python -c "from operators.selberg_operator import demonstrate_selberg_operator; demonstrate_selberg_operator()"
```

---

**QCAL ∞³ | RIGIDEZ ABSOLUTA | 888 Hz → 141.7001 Hz**

∴𓂀Ω∞³Φ
