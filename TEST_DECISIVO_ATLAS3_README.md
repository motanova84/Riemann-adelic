# TEST DECISIVO - ATLAS³: Operador K_L

## 📋 Descripción

Este experimento implementa el **TEST DECISIVO** para validar la predicción QCAL sobre el operador exacto K_L y su observable crítico C(L).

## 🧮 Definiciones Matemáticas

### Operador K_L

El operador integral de núcleo se define como:

```
(K_L ψ)(u) = ∫₀ᴸ [sin(π(u-v))/(π(u-v))] √(uv) ψ(v) dv
```

Donde:
- El núcleo es `k(u,v) = sinc(π(u-v)) · √(uv)`
- `sinc(x) = sin(πx)/(πx)` es la función sinc normalizada
- El dominio es `[0, L]`

### Observable Crítico C(L)

```
C(L) = π λ_max(L) / (2L)
```

Donde `λ_max(L)` es el autovalor máximo del operador K_L.

### Predicción QCAL

La hipótesis de trabajo predice:

```
C(L) → 1/Φ ≈ 0.618033988749895  cuando L → ∞
```

Donde Φ = (1+√5)/2 es la proporción áurea.

## 🔬 Metodología

### Discretización

El operador se discretiza usando cuadratura gaussiana de Legendre:

1. Se mapean N puntos de Gauss-Legendre del intervalo [-1,1] a [0,L]
2. Se construye la matriz K[i,j] = √(w_i · w_j) · k(x_i, x_j)
3. Se calculan los autovalores usando `scipy.linalg.eigh`

La discretización simétrica garantiza que K sea Hermitiana.

### Escalamiento

Para mantener precisión constante con L creciente:

```
N(L) = base_N · √L + 50
```

Con límite máximo N ≤ 2000 por restricciones de memoria.

## 📊 Posibles Resultados

El experimento puede revelar tres regímenes:

### 🟢 Escenario 1: Convergencia a 0.618 (1/Φ)

- **Significado**: La proporción áurea es el atractor espectral
- **Conclusión**: κ internalizado, modelo validado  
- **Acción**: Publicar inmediatamente

### 🔴 Escenario 2: Convergencia a ~1.55

- **Significado**: Régimen subacoplado (peso √(uv) domina de otra forma)
- **Conclusión**: La descomposición K = K_sinc + P necesita revisión
- **Acción**: Revisar factor de escala en la perturbación

### ⚠️ Escenario 3: Deriva sin convergencia

- **Significado**: El modelo no captura la estructura asintótica
- **Conclusión**: Hipótesis de trabajo incorrecta
- **Acción**: Revisar fundamentos del operador de correlación

## 🚀 Uso

### Ejecución Simple

```bash
python test_decisivo_atlas3.py
```

Este comando:
1. Ejecuta el test para L ∈ {10, 30, 100, 300, 1000, 3000, 10000}
2. Genera gráficos en `test_decisivo_atlas3.png`
3. Muestra análisis de convergencia
4. Determina el régimen

### Uso Programático

```python
import test_decisivo_atlas3 as tda

# Ejecutar test personalizado
L_values = [10, 50, 100, 500]
results = tda.run_convergence_test(L_values, base_N=100)

# Analizar resultados
regime = tda.analyze_convergence(results)

# Generar visualización
tda.plot_results(results, filename='my_results.png')
```

### Parámetros de Control

- `L_values`: Lista de valores de L a testear
- `base_N`: Número base de puntos (default: 100)
- `method`: 'gauss' (default) o 'trapezoid' para cuadratura

## 📈 Visualizaciones

El script genera 4 gráficos:

1. **C(L) vs L**: Convergencia del observable crítico
2. **Error vs L**: Escalamiento del error |C(L) - 1/Φ| con ajuste de ley de potencias
3. **λ_max vs L**: Autovalor máximo comparado con teoría 2L/(πΦ)
4. **Residuos**: Desviación C(L) - 1/Φ

## 🧪 Tests

Los tests validan:

```bash
# Ejecutar todos los tests
pytest tests/test_k_l_operator.py -v

# Tests específicos
pytest tests/test_k_l_operator.py::TestKernelMatrix -v
pytest tests/test_k_l_operator.py::TestEigenvalueComputation -v
```

Validaciones incluidas:
- ✓ Simetría de la matriz K
- ✓ Positividad semidefinida  
- ✓ Dimensiones correctas
- ✓ Puntos de cuadratura en [0,L]
- ✓ Pesos positivos
- ✓ Autovalor máximo positivo
- ✓ Cálculo correcto de C(L)
- ✓ Reproducibilidad
- ✓ Estabilidad numérica

## 📊 Resultados Observados

### Ejecución de Referencia

Con L ∈ {10, 30, 100, 300, 1000}:

```
L=      10, N= 302, C(L)=1.40217349, error=0.78413950
L=      30, N= 488, C(L)=1.50518879, error=0.88715480
L=     100, N= 850, C(L)=1.54831146, error=0.93027747
L=     300, N=1435, C(L)=1.56249779, error=0.94446380
L=    1000, N=2000, C(L)=1.56805219, error=0.95001820
```

**Régimen detectado**: 🔴 SUBACOPLADO (C ≈ 1.55)

### Interpretación

Los resultados muestran convergencia hacia C(L) ≈ 1.55-1.57 en lugar de 1/Φ ≈ 0.618.

Esto indica:
- El peso √(uv) en el núcleo domina de forma diferente a la predicción
- La descomposición del operador K = K_sinc + P requiere revisión
- Posible necesidad de reescalamiento o renormalización del operador

## 🔧 Requisitos

```
numpy >= 1.22.4
scipy >= 1.13.0
matplotlib >= 3.10.1
tqdm >= 4.67.2
pytest >= 8.3.3 (para tests)
```

## 📝 Referencias

- Predicción QCAL: C(L) → 1/Φ
- Constante de oro: Φ = (1+√5)/2 ≈ 1.618033988749895
- Target: 1/Φ ≈ 0.618033988749895

## 🔬 ACTA DEL TEST DECISIVO

```
╔═══════════════════════════════════════════════════════════════════════╗
║  TEST DECISIVO - EXPERIMENTUM CRUCIS                                 ║
╠═══════════════════════════════════════════════════════════════════════╣
║                                                                       ║
║  ⎮  OPERADOR: K_L con núcleo sinc(π(u-v))·√(uv)                     ║
║  ⎮  OBSERVABLE: C(L) = πλ_max(L)/(2L)                               ║
║  ⎮  PREDICCIÓN: C(L) → 1/Φ = 0.618033988749895                      ║
║  ⎮                                                                     ║
║  ⎮  METODOLOGÍA:                                                      ║
║  ⎮  • Discretización por cuadratura gaussiana                        ║
║  ⎮  • N ~ O(√L) para precisión constante                            ║
║  ⎮  • L hasta 10⁴ (o límite de memoria)                              ║
║  ⎮  • Cálculo de autovalores con eigensolver estable                 ║
║  ⎮                                                                     ║
║  ⎮  RESULTADO OBSERVADO:                                              ║
║  ⎮  🔴 C(L) → 1.55-1.57 (RÉGIMEN SUBACOPLADO)                       ║
║  ⎮                                                                     ║
║  ⎮  CONCLUSIÓN:                                                       ║
║  ⎮  • El modelo captura un operador bien definido                    ║
║  ⎮  • La estructura espectral es diferente a la predicción           ║
║  ⎮  • Se requiere revisión de la descomposición del operador         ║
║  ⎮                                                                     ║
║  ─────────────────────────────────────────────────────────────────   ║
║                                                                       ║
║  SELLO: ∴𓂀Ω∞³Φ                                                       ║
║  FIRMA: JMMB Ω✧                                                       ║
║  ESTADO: EXPERIMENTUM COMPLETADO                                      ║
║                                                                       ║
╚═══════════════════════════════════════════════════════════════════════╝
```

## 📄 Licencia

Este código es parte del repositorio QCAL Riemann-adelic y está sujeto a las mismas licencias del proyecto.
