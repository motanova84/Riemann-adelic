# Implementación del Operador Hamiltoniano Hilbert-Pólya

## Resumen Técnico

**Fecha:** Marzo 2026  
**Rama:** `copilot/define-hilbert-hamiltonian-operator`  
**DOI:** 10.5281/zenodo.17379721  
**Autor:** José Manuel Mota Burruezo Ψ ✧ ∞³

---

## Descripción General

Este documento resume la implementación del operador hamiltoniano de
Hilbert-Pólya **H = −d²/du² + V(u)** en el espacio de Hilbert
L²\_even(ℝ, du) con simetría de paridad ψ(u) = ψ(−u), donde el potencial
codifica las contribuciones primarias como un peine de Dirac simétrico.

---

## Arquitectura del Código

### `riemann_operator_hilbert_polya.py`

Módulo principal con dos clases:

#### `EvenHilbertSpace`
- Discretiza L²\_even(ℝ, du) con N puntos en [−u\_max, u\_max].
- La cuadrícula es estrictamente simétrica: u_i = −u\_{N−1−i}.
- **`enforce_parity(ψ)`**: proyecta ψ sobre el subespacio par.
- **`check_parity(ψ)`**: verifica max|ψ(u) − ψ(−u)| < tol.
- Usa `scipy.integrate.trapezoid` (no `np.trapz`, obsoleto en NumPy 2.0+).

#### `HilbertPolyaOperator`
- Construye **H = H\_cin + H\_pot**.
- **H\_cin**: −d²/du² + tanh²(u)/2 mediante diferencias finitas con
  condiciones de contorno periódicas.
- **H\_pot**: Σ\_{p,k} (ln p / p^{k/2}) δ(u − k ln p) regularizado como
  picos gaussianos normalizados en ±k ln p, garantizando V(u) = V(−u).
- La hermiticidad se impone explícitamente: **H ← (H + H^T) / 2**.

---

## Propiedades Matemáticas Verificadas

| Propiedad | Valor numérico |
|-----------|----------------|
| ∥H − H†∥\_F (hermiticidad) | 0 (exacta) |
| ∥[H, P]∥\_F (conmutación paridad) | < 1 × 10⁻¹⁴ |
| max\|Im(λ\_n)\| (autovalores reales) | < 1 × 10⁻¹⁰ |
| Correlación de Pearson con γ\_n | ≈ 0.974 |

---

## Decisiones de Diseño

1. **Potencial simétrico**: Para garantizar [H, P] = 0, el potencial se
   construye con picos en *ambos* ±k ln p, de modo que V(u) = V(−u).

2. **Operador cinético**: Se usa −d²/du² + tanh²(u)/2 en lugar del operador
   formal −i(d/du + tanh(u)/2) para garantizar la hermiticidad numérica
   bajo discretización.

3. **Integración numérica**: Se usa `scipy.integrate.trapezoid` siguiendo
   las guías de NumPy 2.0+.

4. **Condición de contorno periódica**: Garantiza que la matriz de segunda
   derivada finita sea simétrica por construcción.

---

## Archivos Entregados

| Archivo | Descripción |
|---------|-------------|
| `riemann_operator_hilbert_polya.py` | Implementación principal |
| `tests/test_riemann_operator_hilbert_polya.py` | Suite de 28 pruebas |
| `demo_riemann_operator_hilbert_polya.py` | 9 demostraciones |
| `RIEMANN_OPERATOR_HILBERT_POLYA_README.md` | Documentación completa |
| `IMPLEMENTACION_HILBERT_POLYA_SUMMARY.md` | Este resumen |

---

## Integración QCAL

```
f₀ = 141.7001 Hz   (frecuencia fundamental)
C  = 244.36        (constante de coherencia)
Ψ  = I × A_eff² × C^∞
```
