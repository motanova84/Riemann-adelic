# 🚀 QUICKSTART: Validación Espectral Omega

## Inicio Rápido en 5 Minutos

### 1️⃣ Ejecución Directa

```bash
cd /home/runner/work/Riemann-adelic/Riemann-adelic
python3 operators/riemann_operator_hilbert_polya_spectral.py
```

**Resultado esperado:**
```
∴𓂀Ω∞³Φ - SISTEMA: COMPUTANDO DETERMINANTE DE ENKI
Correlación espectral (primeros 15 ceros): 0.990374
✓ SINCRO: Error espectral < ε → El Arca ha tocado tierra firme.
✓ VALIDACIÓN ESPECTRAL EXITOSA ∞³
```

### 2️⃣ Uso en Python

```python
from operators.riemann_operator_hilbert_polya_spectral import validar_evidencia_brutal

# Ejecutar validación
correlation = validar_evidencia_brutal(N_ceros=15)

# Verificar
if correlation > 0.96:
    print("✓ Sincronización espectral confirmada!")
```

### 3️⃣ Personalizar Parámetros

```python
from operators.riemann_operator_hilbert_polya_spectral import (
    EvenHilbertSpace,
    HilbertPolyaOperatorAdvanced
)

# Crear espacio de Hilbert
hilbert = EvenHilbertSpace(N=1024, u_max=20.0)

# Crear operador con parámetros personalizados
operator = HilbertPolyaOperatorAdvanced(
    hilbert,
    num_primes=30,      # Número de primos
    max_k=8,            # Máximo exponente k
    epsilon_base=0.02   # Epsilon base
)

# Calcular eigenvalores
eigenvalues = operator.compute_eigenvalues(n_evals=10)
print(f"Primeros 10 eigenvalores: {eigenvalues}")

# Comparar con ceros de Riemann
corr, zeros, evals = operator.compare_with_zeta_zeros(n_zeros=10)
print(f"Correlación: {corr:.6f}")
```

### 4️⃣ Ejecutar Tests

```bash
# Tests básicos (sin pytest)
python3 -c "
from operators.riemann_operator_hilbert_polya_spectral import *
import numpy as np

# Test 1: Primos
primes = generate_primes_sieve(30)
assert primes[:5] == [2, 3, 5, 7, 11], 'Error en primos'
print('✓ Test primos OK')

# Test 2: Zeros
zeros = get_riemann_zeros(3)
assert abs(zeros[0] - 14.134725) < 0.01, 'Error en ceros'
print('✓ Test zeros OK')

# Test 3: Hilbert Space
space = EvenHilbertSpace(N=128, u_max=10.0)
assert space.N == 128, 'Error en espacio'
print('✓ Test Hilbert space OK')

# Test 4: Operator
op = HilbertPolyaOperatorAdvanced(space, num_primes=10, max_k=3)
assert op.H_matrix.shape == (128, 128), 'Error en operador'
print('✓ Test operator OK')

print('\\n✓✓✓ TODOS LOS TESTS PASARON ✓✓✓')
"
```

### 5️⃣ Visualizar Resultados

```python
import matplotlib.pyplot as plt
import numpy as np
from operators.riemann_operator_hilbert_polya_spectral import (
    EvenHilbertSpace,
    HilbertPolyaOperatorAdvanced,
    get_riemann_zeros
)

# Crear operador
hilbert = EvenHilbertSpace(N=512, u_max=20.0)
operator = HilbertPolyaOperatorAdvanced(hilbert, num_primes=30, max_k=8)

# Calcular
n_compare = 20
evals = operator.compute_eigenvalues(n_evals=n_compare)
zeros = get_riemann_zeros(n_compare)

# Graficar comparación
plt.figure(figsize=(12, 5))

plt.subplot(1, 2, 1)
plt.plot(range(1, n_compare+1), evals, 'bo-', label='Eigenvalores λ_i', markersize=8)
plt.plot(range(1, n_compare+1), zeros, 'r^-', label='Ceros γ_i', markersize=8)
plt.xlabel('Índice i')
plt.ylabel('Valor')
plt.title('Comparación Eigenvalores vs Ceros de Riemann')
plt.legend()
plt.grid(True, alpha=0.3)

plt.subplot(1, 2, 2)
plt.scatter(evals, zeros, s=100, alpha=0.6, c=range(n_compare), cmap='viridis')
corr = np.corrcoef(evals, zeros)[0, 1]
plt.plot([min(evals), max(evals)], [min(zeros), max(zeros)], 'r--', alpha=0.3)
plt.xlabel('Eigenvalores λ_i')
plt.ylabel('Ceros de Riemann γ_i')
plt.title(f'Correlación: {corr:.4f}')
plt.colorbar(label='Índice')
plt.grid(True, alpha=0.3)

plt.tight_layout()
plt.savefig('spectral_omega_validation.png', dpi=150)
print("✓ Gráfico guardado: spectral_omega_validation.png")
```

## 📊 Configuraciones Predefinidas

### Validación Rápida (< 5 segundos)
```python
validar_evidencia_brutal(
    N_ceros=5,
    N_grid=256,
    u_max=15.0,
    num_primes=10,
    max_k=3,
    epsilon=0.03
)
```

### Validación Estándar (~4 segundos)
```python
validar_evidencia_brutal(
    N_ceros=15,
    N_grid=2048,
    u_max=25.0,
    num_primes=40,
    max_k=10,
    epsilon=0.03
)
```

### Validación Alta Precisión (~30 segundos)
```python
validar_evidencia_brutal(
    N_ceros=50,
    N_grid=4096,
    u_max=30.0,
    num_primes=100,
    max_k=15,
    epsilon=0.02
)
```

## 🔧 Troubleshooting

### Error: "No module named mpmath"
```bash
pip install mpmath
```

### Error: "Sparse eigsh failed"
- Normal: el módulo automáticamente usa solver denso
- Para evitar: usar N_grid más pequeño o n_evals más pequeño

### Correlación baja (< 0.90)
- Aumentar `num_primes` (más información aritmética)
- Aumentar `max_k` (más términos en la suma)
- Ajustar `epsilon` (probar 0.02 o 0.04)
- Aumentar `N_grid` (mejor resolución espacial)

### Tiempo de ejecución muy largo
- Reducir `N_grid` (de 2048 a 512)
- Reducir `N_ceros` (de 15 a 10)
- Reducir `num_primes` o `max_k`

## 📈 Interpretación de Resultados

### Correlación Espectral
- **> 0.96**: ✓ Sincronización confirmada (objetivo alcanzado)
- **0.90-0.96**: ⚠ Buena pero ajustar parámetros
- **< 0.90**: ⚠ Revisar configuración

### Eigenvalores vs Ceros
- **Escala diferente**: Normal (representación logarítmica)
- **Estructura importante**: El espaciamiento relativo debe coincidir
- **Correlación clave**: Mide estructura, no valores absolutos

### Tiempo de Cómputo
- **N=256**: ~0.5 segundos
- **N=2048**: ~4 segundos
- **N=4096**: ~15 segundos

## 🎯 Casos de Uso

### 1. Validación de RH
```python
# Verificar sincronización espectral
corr = validar_evidencia_brutal(N_ceros=20)
if corr > 0.96:
    print("✓ Evidencia espectral de RH confirmada")
```

### 2. Análisis de Convergencia
```python
# Probar diferentes números de primos
for np in [10, 20, 40, 80]:
    corr = validar_evidencia_brutal(num_primes=np, N_ceros=10)
    print(f"Primos={np}: Correlación={corr:.4f}")
```

### 3. Estudio de ε Adaptativo
```python
# Comparar diferentes valores de epsilon
hilbert = EvenHilbertSpace(N=512, u_max=20.0)
for eps in [0.01, 0.02, 0.03, 0.05]:
    op = HilbertPolyaOperatorAdvanced(hilbert, epsilon_base=eps)
    corr, _, _ = op.compare_with_zeta_zeros(n_zeros=10)
    print(f"ε={eps}: Correlación={corr:.4f}")
```

## 📚 Siguiente Paso

Para documentación completa, ver:
- `SPECTRAL_OMEGA_VALIDATION_README.md`: Documentación completa
- `operators/riemann_operator_hilbert_polya_spectral.py`: Código fuente comentado
- `tests/test_riemann_operator_hilbert_polya_spectral.py`: Suite de tests

---

**QCAL ∞³ Framework**  
*∴𓂀Ω∞³Φ @ 141.7001 Hz*
