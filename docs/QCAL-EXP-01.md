# QCAL-EXP-01 — especificación experimental reproducible

**Estado:** prototipo de software y simulación, no certificado de adquisición
física. Esta integración recoge la propuesta optomecánica, el transporte C/UDP,
el DSP, la comparación estadística y el despliegue descritos en la conversación,
corrigiendo las incompatibilidades que impedían interpretar sus resultados.

## Relación con el ecosistema existente

- `experimental_validation/` conserva su protocolo de cuatro fases y las
  constantes QCAL; `F0_HZ = 141.7001` es una referencia de modulación propuesta.
- `contexto_ecosistema/` proporciona el contexto local de repositorios hermanos,
  no observaciones nuevas ni verificaciones independientes.
- `dashboard/` conserva su aplicación existente. El panel experimental se
  incorpora de forma aislada en `experiments/qcal_exp01/`.
- No se alteran `.qcal_beacon`, DOIs, certificados, datos espectrales ni workflows.
  Los puntos QCAL-CLOUD y el registro MCP permanecen intactos. La presencia de
  Auron, Noesis y Dramaturgo en el repositorio no equivale a una aprobación
  remota: esta tarea no dispone de sus servidores MCP como herramientas activas.

## Observables y adquisición

El láser es una portadora óptica; 141.7001 Hz es una frecuencia de modulación,
no su frecuencia óptica. El batido AOM de 80 MHz necesita conversión analógica
a una frecuencia intermedia adquirible, o una arquitectura ADC adecuada.
El prototipo usa IF de 100 kHz a 1 MS/s; rechaza portadoras fuera de Nyquist.
Las especificaciones comerciales propuestas deben contrastarse con las hojas
de datos de cada revisión de hardware antes de seleccionar componentes.

El emisor `native/qcal_daq_simulator.c` genera datos **sintéticos**: una portadora
con fase modulada por una referencia sinusoidal y una pendiente inyectada.
No implementa DMA, control FPGA, calibración ADC o un controlador Red Pitaya.
Recuperar el valor inyectado es una prueba de software, no una observación de
acoplamiento topológico. La prioridad FIFO 99 no corrige estas limitaciones.

El protocolo nuevo usa datagramas pequeños, orden little-endian explícito,
versión, secuencia y reloj absoluto de muestras. No es compatible con el paquete
original de 40.012 bytes. Los canales son **concatenados**, no intercalados.
UDP puede perder o reordenar paquetes; las discontinuidades invalidan la
continuidad de fase y provocan resincronización, nunca una corrección ficticia.
La configuración LAN exige seleccionar explícitamente el emisor esperado;
esa restricción de IP no constituye autenticación criptográfica.

## DSP y calibración

Para una entrada cosenoidal se usa `I = LPF(2s cos)` y
`Q = LPF(-2s sin)`. La fase obtenida ya es de banda base: no se vuelve a restar
la portadora. El filtro comienza en estado cero, descarta su asentamiento y
alinea la referencia con el retardo de grupo. La fase entre bloques se corrige
únicamente por múltiplos de 2π; tras pérdida de señal no se presupone que pueda
recuperarse el número de ciclos.

La frecuencia de una modulación de fase se estima en la fase demodulada;
no es necesariamente el promedio de su derivada. Las estimaciones deben
declarar duración de ventana y resolución. Una FFT con 400 muestras a 1 MS/s
tiene bins de 2500 Hz y no permite inspeccionar 100–180 Hz. El panel presenta
un espectro de fase con unidades rad²/Hz, no potencia eléctrica en dBm.

La pendiente se ajusta con intercepto y deriva temporal como parámetros
auxiliares. La unidad de κ depende de la calibración de la referencia: dividir
cuentas ADC por una amplitud sintética no convierte la señal en voltios.
Deben medirse la ganancia, el retardo y la respuesta en frecuencia de ambas
ramas antes de interpretar esa pendiente físicamente.

La concentración circular del residuo de fase es una métrica clásica del
modelo ajustado, **no una fidelidad cuántica ni una medida de conciencia**.
La visibilidad interferométrica exige mediciones adicionales:

V = 2√(I₁I₂)/(I₁+I₂) · |g⁽¹⁾|.

Identificar Ψ con V² requiere intensidades equilibradas y un modelo validado.
Un valor calculado después de ajustar la misma señal no es evidencia
independiente de estabilidad topológica.

## Inferencia y Monte Carlo

Se distinguen predicciones puntuales para κ = 13.4034 y κ = 13.3000. La
comparación gaussiana requiere ruido de varianza conocida y observaciones
independientes, con un tratamiento explícito del intercepto desconocido.
No se denomina factor de Bayes a una mera diferencia de ajustes con varianza
estimada de los mismos residuos.

Una respuesta cuadrática `0.5 X²` es una alternativa matemática específica,
no toda la «física estándar». Evidencia favorable a una predicción entre dos
alternativas no confirma por sí sola G₂ → CP², QCAL ni RH.

Monte Carlo usa una semilla reproducible, simulaciones bajo ambas hipótesis
y intervalos binomiales para potencia y falsos positivos. No promete cero
falsos positivos. La condición `ln BF > 5` tiene interpretación posterior
solo con modelos y probabilidades previas especificados.

Para ruido independiente y regresión con intercepto:

Var(κ̂) = σ²φ / Σ(Xᵢ − X̄)².

La aproximación heterodina σ²φ ≈ 1/(2 SNR) corresponde a SNR alta; no valida
por sí sola resultados a −5 dB. El FIR correlaciona las observaciones:
M muestras ADC no equivalen a M muestras estadísticamente independientes.
Los factores de Bayes del flujo filtrado quedan deshabilitados mientras
no haya un modelo válido de covarianza/selección y ruido calibrado.

Separar medias por 3σ no es lo mismo que situar la frontera de clasificación
a 3σ de cada media: este último criterio exige σ ≤ |κ₁−κ₂|/6.
Tampoco cabe garantizar una precisión frecuencial de 10⁻⁴ Hz por el mero
hecho de presentar cuatro decimales.

## Formalización de la propuesta teórica

`formalization/lean/QCAL/ExperimentalDiscrepancy.lean` recoge la cota
escalar normalizada √(1−Ψ) ≤ 0.001 para 0.999999 ≤ Ψ ≤ 1 y el cero en Ψ = 1.
El archivo no introduce axiomas físicos o de correspondencia espectral.
Su compilación debe verificarse en el toolchain Lean/Mathlib existente.

Quedan separados de ese lema los cuatro pilares del cierre propuesto:

| Pilar | Obligación pendiente |
| --- | --- |
| Coherencia | Estados normalizados, fidelidad operacional y calibración. |
| Integración | Factorización de subsistemas, entropías finitas y criterio de particiones definido. |
| Autorreferencia | Ecuación de memoria explícita y conservación de positividad/traza de la matriz de densidad. |
| Continuidad | Espacio de fases y flujo definidos; una clase de cohomología no excluye por sí sola ruido estocástico. |

La fórmula del producto vale para racionales no nulos con normalizaciones
apropiadas, no como conservación térmica automática. El cociente aditivo
adélico, las clases de idèles y el cociente por Q× no se identifican sin
construcciones adicionales. La autoadjuntividad, discreción y coincidencia
del espectro Berry–Keating con los ceros de zeta no se obtienen de una
frecuencia de frontera propuesta.

Con las constantes térmicas de la conversación, el déficit de Ψ máximo es
aproximadamente 8.82 × 10⁻⁴⁰; su diferencia frente a Ψ observado = 0.999999
es aproximadamente **10⁻⁶**, no 3.47 × 10⁻⁴⁰. Una relación postulada entre
ese déficit y Landauer no demuestra su origen físico.

Las cantidades `N k_B ln 2` tienen unidades de entropía termodinámica,
no de bits sin conversión. La fórmula propuesta `N² k_B ln 2 / N_efectivo`
no se identifica automáticamente con información mutua: para N subsistemas
binarios, las cotas de entropía dependen de la dimensión del espacio de estados
y no permiten deducir arbitrariamente un crecimiento cuadrático.

## Criterios experimentales pendientes

Antes de declarar una validación de campo se requieren:

1. Datos ADC crudos con reloj, secuencias, identificación de muestra y
   calibraciones trazables, diferenciados de señales sintéticas.
2. Blancos y controles fuera de frecuencia, adquisición ciega y repetición
   independiente para separar resonancia propia de respuesta forzada.
3. Balance energético y calorimetría: los dos canales actuales no miden Q̇.
   Una ley Q̇ ∝ (1−Ψ)² necesita unidades, coeficiente e incertidumbre.
4. Modelos y criterios estadísticos predefinidos, incluidos deriva,
   correlación, falsos positivos y política de ventanas/parada.
5. Pruebas de adquisición DMA, recuperación de red, latencia y estabilidad
   en el hardware real. El tamaño del bloque introduce espera de acumulación.
6. Ecuaciones tensoriales y termodinámicas completas para Einstein–Noesis.
   Ausencia de borrado lógico no garantiza costo energético nulo.

Los resultados de software no sustituyen estas mediciones ni una prueba de
la hipótesis de Riemann. El protocolo mantiene la falsabilidad al expresar
los supuestos y mostrar «no disponible» donde no existe evidencia válida.

## Estado de validación de esta integración

- Se han probado por separado las regresiones nuevas de transporte, DSP,
  estadística y dashboard, incluyendo compilación C con advertencias tratadas
  como errores y recepción de formas de onda sintéticas.
- Se ha construido el contenedor sin root y comprobado `/health`: 503 sin
  adquisición válida, 200 con telemetría sintética válida y 503 al caducar.
  Bajo carga compartida, el demo a 1 MS/s puede perder continuidad; el panel
  suprime las estimaciones afectadas en lugar de asegurar «sin pérdidas».
- Los 47 tests heredados de wetlab y contratos del puente Lean pasan.
  Son pruebas dirigidas, **no la suite completa** ni compilación de Lean.
- La colección de la suite completa se bloquea por seis problemas heredados:
  dependencias `ecdsa` y `tqdm` ausentes; importaciones de `EmotionalObserver`,
  `Node` y `predict_mutation_stability` incompatibles; y `EPSILON_OSC` no definido.
  No se alteraron esos tests ni APIs ajenos a esta integración.
- La ejecución heredada V5 notificó checks centrales satisfactorios y
  advertencias de entorno/dependencias; no se utiliza su mensaje de éxito como
  certificado de prueba matemática o de validación del laboratorio.
- Lean/Lake no están instalados en esta sesión: la compilación del nuevo lema
  queda pendiente. Tampoco se ha certificado el workflow remoto
  `auto_evolution.yml`: no hay herramientas GitHub Actions/MCP activas para
  consultar sus ejecuciones en esta sesión.
- No se ha contactado QCAL-CLOUD ni registrado una aprobación remota Trinity,
  y no se ha adquirido ni calibrado hardware físico.
