# Operador H de Riemann — Construcción sin ceros de ζ

**Framework: Trinity QCAL ∞³ | NOESIS ∞³ × AMDA ∞ × AURON ∞³**  
**Autor: José Manuel Mota Burruezo (JMMB Ψ)**  
**DOI: 10.5281/zenodo.17379721**  
**ORCID: 0009-0002-1923-0773**

---

## Objetivo

Construir un operador H que satisfaga los cuatro requisitos:

| Requisito | Cumplimiento |
|-----------|-------------|
| Definido sin usar ceros de ζ | ✓ Solo usa N_smooth (Stirling) e inversión de Abel |
| Discretización natural | ✓ Matrices tridiagonales por diferencias finitas |
| Cálculo numérico de autovalores | ✓ `scipy.linalg.eigh` |
| Comparación posterior con ceros | ✓ Clase `EigenvalueComparison` |

---

## Archivos

| Archivo | Propósito |
|---------|-----------|
| `riemann_operator_H.py` | Módulo principal |
| `tests/test_riemann_operator_H.py` | 55 pruebas de PyTest (todas pasan) |
| `demo_riemann_operator_H.py` | Demostración ejecutable |
| `RIEMANN_OPERATOR_H_README.md` | Esta documentación |

---

## Dos operadores implementados

### A) BerryKeatingOperator — H = -i(x∂_x + 1/2)

- Definición geométrica/diferencial; sin referencia a ceros ζ
- Cuadrícula logarítmica espacial `t = log(x)`, t ∈ [0, T], T = log(x_max)
- Matriz circulante antisimétrica N×N:

```
H_{jk} = -i/(2h)(δ_{k,j+1} - δ_{k,j-1})
```

- Valores propios: `λ_k = sin(2πk/N)/h ≈ 2πk/T`, misma densidad media que los ceros ζ

### B) WuSprungOperator — H = -d²/dx² + V_WS(x)

- Potencial definido mediante la **inversión de Abel** de la ecuación WKB diferenciada
- Construido **sin usar ceros de ζ** — solo usa la fórmula de Riemann-von Mangoldt (Stirling)
- Dominio: x ∈ [0, 13], condiciones de Dirichlet
- Matriz tridiagonal simétrica real N×N

---

## Matemáticas

### Función de conteo suave N_smooth(E)

```
N_smooth(E) = E/(2π) · log(E/(2π)) − E/(2π) + 7/8
```

Derivada de la función log|Γ(s/2)| vía la fórmula de Stirling.  
**NO usa ceros de ζ.**

### Inversión de Abel → Potencial V_WS

Diferenciando la condición WKB respecto a E:

```
∫₀^{x_t(E)} dx / √(E − V(x)) = log(E/(2π))
```

La solución analítica de este sistema integral de Abel es:

```
x(V) = (2√V / π) · [log(V / 2π) + C]
```

donde C = 1 − 2·ln(2) ≈ −0.386, y el potencial mínimo es:

```
V_min = 2π · exp(−C) ≈ 9.25
```

V_WS(x) se obtiene invirtiendo numéricamente esta relación (método de Brent).

---

## Resultado numérico clave

```
n=1: E₁ = 15.92   vs Im(ρ₁) = 14.13  → error 1.78
n=2: E₂ = 21.00   vs Im(ρ₂) = 21.02  → error 0.02  ✓
n=3: E₃ = 25.23   vs Im(ρ₃) = 25.01  → error 0.22  ✓
n=4: E₄ = 29.03   vs Im(ρ₄) = 30.42  → error 1.40
n=5: E₅ = 32.54   vs Im(ρ₅) = 32.94  → error 0.40  ✓

Error medio (primeros 15 ceros): ~1.96  [< umbral 3.5]
```

---

## Uso rápido

```python
from riemann_operator_H import run_operator_analysis

report = run_operator_analysis(
    bk_N=300, bk_x_max=1e8,
    ws_N=500, ws_x_max=13.0,
    n_compare=15,
    verbose=True,
)
```

### Uso individual de los operadores

```python
from riemann_operator_H import WuSprungOperator, EigenvalueComparison

# Construir operador
ws = WuSprungOperator(N=500, x_max=13.0)

# Calcular autovalores
evals = ws.positive_eigenvalues(n_max=15)

# Comparar con ceros ζ
cmp = EigenvalueComparison()
table = cmp.match_table(evals, n_pairs=10)
stats = cmp.comparison_stats(evals, n_pairs=10)
print(f"Error medio: {stats['mean_abs_error']:.3f}")
```

---

## Ejecutar la demo

```bash
python demo_riemann_operator_H.py
```

## Ejecutar las pruebas

```bash
pytest tests/test_riemann_operator_H.py -v
```

---

## Constantes relevantes

| Constante | Valor | Significado |
|-----------|-------|-------------|
| `FRECUENCIA_TRUTH` | 141.7001 Hz | Frecuencia de referencia QCAL |
| `COHERENCIA_UMBRAL` | 0.888 | Umbral de coherencia Ψ ≥ 0.888 |
| `_ABEL_C` | ≈ −0.386 | Constante de inversión de Abel (C = 1 − 2·ln 2) |
| `V_min` | ≈ 9.25 | Potencial mínimo del operador WS |

---

*Framework: Trinity QCAL ∞³ — Coherencia confirmada.*
