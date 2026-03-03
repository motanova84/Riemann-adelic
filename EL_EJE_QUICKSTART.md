# El Eje: La Línea Crítica - Quick Start Guide

## Inicio Rápido

Este es un tutorial de 5 minutos para explorar "El Eje: La Línea Crítica", una implementación del árbol del universo matemático centrado en Re(s) = 1/2.

## Instalación

```bash
# Requisitos
pip install numpy matplotlib mpmath scipy pytest

# Clone el repositorio (si aún no lo has hecho)
git clone https://github.com/motanova84/Riemann-adelic.git
cd Riemann-adelic
```

## Uso Básico

### 1. Demostración en Consola (30 segundos)

```bash
python el_eje_linea_critica.py
```

**Salida esperada:**
```
================================================================================
EL EJE: LA LÍNEA CRÍTICA
Re(s) = 1/2 — El Árbol del Universo Vibracional
================================================================================

I. 🌳 LA LÍNEA CRÍTICA Re(s) = 1/2
   Equilibrio: Re(s) = 0.5
   Coherencia C = 244.36
   
II. ⚖️ LOS EXTREMOS: +1 y -1
   +1: Serie armónica → ∞
   -1: ζ(-1) = -0.083333
   
III. 🌀 LOS PRIMOS EN ESPIRAL
   r(p) = log(p), θ(p) = p
   
IV. 🌊 LA FRECUENCIA COMO MAR
   f₀ = 141.7001 Hz — El viento eterno
```

### 2. Demostración Completa con Visualizaciones (2 minutos)

```bash
python demo_el_eje.py
```

**Genera 5 visualizaciones en `visualizations/`:**
- `el_eje_linea_critica.png` - Línea crítica y regiones
- `el_eje_extremos.png` - Extremos +1 y -1
- `el_eje_espiral_primos.png` - Espiral de primos
- `el_eje_campo_frecuencia.png` - Campo de frecuencia
- `el_eje_arbol_universo_completo.png` - Visión total

### 3. Verificar con Tests (15 segundos)

```bash
python -m pytest test_el_eje.py -v
```

**Salida esperada:**
```
============================== 25 passed in 0.15s ===============================
```

## Uso Programático

### Ejemplo 1: Explorar la Línea Crítica

```python
from el_eje_linea_critica import CriticalLineAxis

# Crear el eje
axis = CriticalLineAxis()

# Punto de equilibrio
print(f"Equilibrio: Re(s) = {axis.equilibrium_point()}")

# Clasificar puntos
puntos = [0.3 + 14j, 0.5 + 14j, 0.7 + 14j]
for s in puntos:
    region = axis.classify_region(s)
    print(f"{s} → {region}")

# Campo de coherencia
for t in [0, 10, 50]:
    coherencia = axis.coherence_field(t)
    print(f"Ψ(t={t}) = {coherencia:.6f}")
```

### Ejemplo 2: Explorar los Extremos

```python
from el_eje_linea_critica import VibrationalExtremes

extremes = VibrationalExtremes()

# Serie armónica en +1
h100 = extremes.harmonic_divergence(100)
print(f"H_100 = {h100:.4f}")

# Explosión en -1
zeta_minus_1 = extremes.zeta_at_minus_one()
print(f"ζ(-1) = {zeta_minus_1}")

# Código dual
roots = extremes.dual_code_roots()
print(f"Existencia: {roots['existencia']['simbolo']}")
print(f"Anti-existencia: {roots['anti_existencia']['simbolo']}")
```

### Ejemplo 3: Espiral de Primos

```python
from el_eje_linea_critica import PrimeSpiral

spiral = PrimeSpiral()

# Obtener primos
primes = spiral.get_primes(10)
print(f"Primeros 10 primos: {primes}")

# Coordenadas de espiral
for p in [2, 3, 5, 7]:
    r, theta = spiral.spiral_coordinates(p)
    x, y = spiral.spiral_cartesian(p)
    f_buzz = spiral.magicicada_frequency(p)
    print(f"p={p}: r={r:.4f}, θ={theta:.1f}, "
          f"(x,y)=({x:.4f},{y:.4f}), f={f_buzz:.2f} Hz")

# Nodos de curvatura
nodes = spiral.curvature_nodes(n_primes=50)
print(f"Nodos calculados: {nodes['n_nodes']}")
```

### Ejemplo 4: Campo de Frecuencia

```python
from el_eje_linea_critica import FrequencyField

field = FrequencyField()

# Propiedades del viento eterno
wind = field.eternal_wind()
print(f"Frecuencia: f₀ = {wind['frecuencia']:.6f} Hz")
print(f"Período: T = {wind['periodo']:.8f} s")
print(f"Coherencia: C = {wind['coherencia']:.2f}")

# Campo de onda
for t in [0, 0.001, 0.01]:
    psi = field.wave_field(t, x=0)
    print(f"|Ψ(t={t})| = {abs(psi):.6f}")

# Presión cuántica
p = field.quantum_pressure(0.01)
print(f"Presión cuántica: P = {p:.6f}")
```

### Ejemplo 5: Árbol del Universo Completo

```python
from el_eje_linea_critica import UniverseTree

# Crear el árbol
universe = UniverseTree()

# Describir estructura
structure = universe.describe_structure()
print("\n=== ESTRUCTURA DEL ÁRBOL ===")
print(f"Eje: {structure['eje_tronco']['tipo']}")
print(f"Raíz Superior: {structure['raices_invertidas']['superior']['naturaleza']}")
print(f"Raíz Inferior: {structure['raices_invertidas']['inferior']['naturaleza']}")
print(f"Hojas: {structure['hojas_giratorias']['metafora']}")
print(f"Viento: {structure['viento_eterno']['metafora']}")

# Visión total
vision = universe.compute_vision_total(n_primes=100, t_range=(0, 100))
print(f"\nCálculo completo:")
print(f"  Eje: {len(vision['eje']['t_axis'])} puntos")
print(f"  Hojas: {vision['hojas']['n_nodes']} primos")
print(f"  Viento: {vision['viento']['frecuencia']:.6f} Hz")
```

## Conceptos Clave

### La Línea Crítica Re(s) = 1/2
- **Es**: El eje vertical perfecto donde todo se equilibra
- **Separa**: Caos (Re < 1/2) de simetría oculta (Re > 1/2)
- **Campo**: Ψ(t) = exp(-t²/(2C)) con C = 244.36

### Los Extremos ±1
- **+1**: Divergencia de la serie armónica → ∞ (Existencia)
- **-1**: Explosión ζ(-1) = -1/12 (Anti-existencia)
- **Código Dual**: Raíces invertidas del árbol

### Los Primos en Espiral
- **Ecuación**: r(p) = log(p), θ(p) = p
- **Geometría**: Serpiente de luz en torno al eje
- **Frecuencia**: f_p = f₀·log(p)/(2π) (zumbido Magicicada)

### La Frecuencia f₀ = 141.7001 Hz
- **Es**: El viento eterno que canta entre las ramas
- **Campo**: Ψ(x,t) = exp(i·ω₀·t)·exp(-x²/(2C))
- **Efecto**: Medio donde los ceros respiran

## Visualizaciones

### Ver las Imágenes Generadas

```bash
# Abrir directorio de visualizaciones
cd visualizations/

# Ver lista
ls -lh el_eje*.png
```

### Personalizar Visualizaciones

```python
from demo_el_eje import (
    plot_critical_line_axis,
    plot_vibrational_extremes,
    plot_prime_spiral,
    plot_frequency_field,
    plot_universe_tree_complete
)

# Generar visualización personalizada
plot_critical_line_axis("mi_linea_critica.png")
plot_prime_spiral("mi_espiral.png")
```

## Ejemplos de Salida

### Consola
```
∞ VISIÓN TOTAL ∞

El eje no es solo vertical.
Es el árbol del universo.
+1 y -1 son sus raíces invertidas.
Los primos son las hojas que giran.
Y la frecuencia:
el viento eterno que canta entre sus ramas.

Re(s) = 1/2 — La vertical perfecta
f₀ = 141.7001 Hz — El viento que no cesa
C = 244.36 — La coherencia que sostiene

∴ 𓂀 Ω ∞³
```

### Datos Numéricos
```python
Primeros 10 primos en coordenadas espirales:
p    r(p)=log(p)    θ(p)=p       x          y         f_buzz(Hz)
------------------------------------------------------------------------
  2    0.6931         2.0     -0.2885     0.6303     15.63
  3    1.0986         3.0     -1.0876     0.1550     24.78
  5    1.6094         5.0      0.4565    -1.5433     36.30
  7    1.9459         7.0      1.4670     1.2784     43.88
 11    2.3979        11.0      0.0106    -2.3979     54.08
```

## Referencias

### QCAL ∞³ Framework
- **Frecuencia**: f₀ = 141.7001 Hz (`.qcal_beacon`)
- **Coherencia**: C = 244.36
- **Ecuación**: Ψ = I × A_eff² × C^∞

### Documentación
- `EL_EJE_IMPLEMENTATION_SUMMARY.md` - Resumen completo
- `el_eje_linea_critica.py` - Docstrings detalladas
- `test_el_eje.py` - Ejemplos de uso en tests

### Autor
- **Nombre**: José Manuel Mota Burruezo Ψ ✧ ∞³
- **Institución**: Instituto de Conciencia Cuántica (ICQ)
- **DOI**: 10.5281/zenodo.17379721
- **ORCID**: 0009-0002-1923-0773

## Solución de Problemas

### Error: ModuleNotFoundError
```bash
# Instalar dependencias
pip install numpy matplotlib mpmath scipy pytest
```

### Visualizaciones no se generan
```bash
# Verificar directorio
mkdir -p visualizations

# Ejecutar demo
python demo_el_eje.py
```

### Tests fallan
```bash
# Reinstalar dependencias
pip install --upgrade numpy matplotlib mpmath scipy pytest

# Ejecutar tests con más detalle
python -m pytest test_el_eje.py -vv
```

## Próximos Pasos

1. **Explorar**: Lee `EL_EJE_IMPLEMENTATION_SUMMARY.md`
2. **Experimentar**: Modifica parámetros en `demo_el_eje.py`
3. **Integrar**: Conecta con otros módulos QCAL ∞³
4. **Extender**: Añade nuevas visualizaciones o análisis

## Contacto y Contribuciones

Para preguntas, sugerencias o contribuciones:
- **GitHub**: https://github.com/motanova84/Riemann-adelic
- **Email**: institutoconsciencia@proton.me

---

**∴ 𓂀 Ω ∞³**

**Fecha**: Febrero 8, 2026  
**Versión**: 1.0.0  
**Licencia**: Creative Commons BY-NC-SA 4.0
