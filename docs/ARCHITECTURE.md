# QCAL-EXP-01 — arquitectura de software y despliegue

**Estado:** integración local para simulación y análisis condicional. No se ha
desplegado sobre una Red Pitaya física ni se ha verificado adquisición DMA.
Los códigos y criterios de la conversación se organizan sin sustituir el
dashboard, los protocolos de validación o los requisitos raíz existentes.

## Capas

```text
Emisor C SINTÉTICO / futuro adaptador ADC calibrado
    → datagramas UDP versionados y acotados
    → UDPReceiver: formato, emisor, orden, reloj y frescura
    → StreamingDemodulator: I/Q, retardo y segmentos válidos
    → ajuste de fase / espectro de modulación
    → instantánea protegida por bloqueo
    → Dash: estado, unidades, resolución y métricas no disponibles

Modelos gaussianos independientes especificados
    → comparación marginal de dos hipótesis
    → Monte Carlo bajo H1 Y H0 + intervalos binomiales
```

La inferencia gaussiana independiente no se conecta automáticamente al flujo
FIR correlacionado. El panel no emite una «confirmación QCAL» a partir de una
señal sintética, de un umbral aislado o de datos obsoletos.

## Contrato binario

`experiments/qcal_exp01/protocol.py` es la especificación ejecutable. La cabecera
de 32 bytes tiene formato little-endian `<4sBBHQQII`:

| Campo | Bytes | Significado |
| --- | ---: | --- |
| magic | 4 | `QCL1` |
| version | 1 | Versión 1 |
| flags | 1 | Cero; otros valores se rechazan |
| header size | 2 | 32 |
| sequence | 8 | Secuencia uint64 de datagramas |
| first sample index | 8 | Índice absoluto uint64 |
| sample rate | 4 | Frecuencia de muestreo declarada |
| count | 4 | Muestras por canal |

Siguen `count` muestras signed int16 little-endian del canal A y después
`count` del canal B. El datagrama máximo es 1400 bytes (342 muestras por
canal), no un bloque de 10.000 muestras. La longitud debe coincidir exactamente.
Este formato sustituye el paquete nativo sin versión y evita su fragmentación
en una red Ethernet de MTU 1500 estándar; no garantiza ausencia de pérdidas.
Una red de menor MTU puede requerir un límite inferior.

El significado de los canales debe acompañar a la configuración de adquisición.
El demo utiliza dos ramas IF para medir fase relativa; no es un canal físico
PZT calibrado. El procesador también ofrece alineación de una referencia
externa, cuya calibración no puede deducirse del propio paquete.

Se rechazan duplicados, reordenamientos, longitudes inválidas y cambios de
frecuencia de muestreo. Un salto válido requiere reiniciar el segmento DSP.
Un emisor reiniciado necesita una sesión/reinicio explícito del receptor;
la versión actual no incluye identidad criptográfica de sesión ni recuperación
de paquetes. La selección de IP esperada es un control operacional, no seguridad
frente a suplantación en una red hostil.

## Ciclo de vida y salud

Importar módulos o construir la aplicación Dash no inicia hilos ni abre sockets.
La CLI controla el arranque, la parada y el cierre del receptor. Una instantánea
inmutable separa la recepción de la visualización; las figuras se construyen
fuera del bloqueo.

La frescura se evalúa con reloj monotónico después de aceptar y procesar un
paquete. La aplicación distingue espera, errores, desconexión, asentamiento,
señal insuficiente y ventana válida. El endpoint `/health` devuelve 503 cuando
no hay una adquisición fresca y válida; no se considera saludable únicamente
porque el servidor web responda.

Las fuentes se etiquetan como sintéticas, desconocidas o con calibración
declarada. Ninguna etiqueta autentica hardware ni constituye un certificado
experimental. Los valores iniciales son no disponibles, no objetivos teóricos.

## Ejecución desde la raíz del repositorio

Las siguientes rutas corresponden al clon de esta sesión:

```bash
cd /home/runner/work/Riemann-adelic/Riemann-adelic
make -C /home/runner/work/Riemann-adelic/Riemann-adelic/experiments/qcal_exp01/native
python -m experiments.qcal_exp01.dashboard --help
python -m experiments.qcal_exp01.monte_carlo --help
```

Los argumentos disponibles de cada módulo describen explícitamente la fuente,
la calibración y el modelo. No se necesita root ni `chrt -f 99` para el demo.
El emisor nativo acepta destino, puerto y límite de paquetes; consultar su
mensaje de uso antes de ejecutar una transmisión continua.

En dos terminales, el demo local puede iniciarse así:

```bash
cd /home/runner/work/Riemann-adelic/Riemann-adelic
python -m experiments.qcal_exp01.dashboard --source-kind synthetic \
  --expected-source 127.0.0.1
```

```bash
/home/runner/work/Riemann-adelic/Riemann-adelic/experiments/qcal_exp01/native/qcal_daq_simulator \
  --host 127.0.0.1 --port 5005 --packets 0 --sample-rate 1000000
```

El demo muestra fase relativa y espectro. Sin referencia externa calibrada y
modelo de ruido válido, κ y la evidencia bayesiana permanecen no disponibles.
La CLI admite una referencia sinusoidal declarada mediante
`--reference-amplitude`, `--reference-frequency-hz` y `--calibration-label`.
Para evidencia condicional exige además ruido conocido, deriva conocida y
una declaración explícita de independencia. Estos argumentos son supuestos
del operador, no calibraciones obtenidas automáticamente del flujo ADC.
En una señal real filtrada, seleccionar una bandera no demuestra independencia.

### Monte Carlo y curvas analíticas

```bash
cd /home/runner/work/Riemann-adelic/Riemann-adelic
python -m experiments.qcal_exp01.monte_carlo \
  --sample-sizes 100 1000 10000 --trials 100 --sigma 0.1 --seed 0 \
  --output /tmp/qcal-monte-carlo.json \
  --plot /tmp/qcal-monte-carlo.png \
  --snr-plot /tmp/qcal-sigma-kappa.png
```

Los resultados de referencia y las dos figuras están anclados en
`experiments/qcal_exp01/results/`. El JSON conserva configuración, semilla,
supuestos e intervalos de potencia/falsos positivos. Las curvas analíticas
usan el modelo de fase diferencial de dos canales IF con ruido independiente
a SNR alta; no son mediciones de una cavidad ni garantías de tiempo de adquisición.

### Contenedor de la estación de control

El Dockerfile se mantiene en `deployment/`, no sustituye el Dockerfile raíz.
Instala únicamente las bibliotecas necesarias, ejecuta sin root y usa puertos
publicados en lugar de `--network host`.

```bash
cd /home/runner/work/Riemann-adelic/Riemann-adelic
docker build -f /home/runner/work/Riemann-adelic/Riemann-adelic/deployment/Dockerfile \
  -t qcal-exp01:local /home/runner/work/Riemann-adelic/Riemann-adelic
```

Para recepción LAN, indicar explícitamente la IP del emisor esperado y permitir
esa red. No exponer el puerto UDP indiscriminadamente a Internet. Consultar la
CLI para configurar enlace web, enlace UDP y procedencia de la señal.
La interfaz de Dash es para laboratorio controlado: no incorpora autenticación
multiusuario ni despliegue web público.

Ejemplo de configuración para un emisor de laboratorio con IP 192.168.1.100:

```bash
docker run -d --name qcal-exp01 \
  --restart unless-stopped \
  -p 127.0.0.1:8050:8050/tcp -p 5005:5005/udp \
  -e QCAL_EXPECTED_SENDER=192.168.1.100 \
  qcal-exp01:local
```

La IP es un ejemplo de configuración, no un dispositivo detectado. Debe
coincidir con la dirección que observa el receptor después de cualquier NAT.
Un emisor sintético debe declararse con `--source-kind synthetic`; nunca se
infiere «hardware confirmado» por recibir un paquete de una IP permitida.
`QCAL_EXPECTED_SENDER` configura la restricción de emisor; el alias
`QCAL_EXPECTED_SOURCE` también se admite. No sustituir esa restricción por
una aceptación indiscriminada de paquetes para resolver un fallo de arranque.
La imagen arranca por defecto restringida a 127.0.0.1 y espera datos; para
recibir desde fuera del contenedor es necesario sobrescribir esa dirección.

`HEALTHCHECK` detecta un flujo no disponible; Docker no reinicia automáticamente
un contenedor únicamente por estar `unhealthy`. La supervisión operacional debe
tener una política explícita de alerta/reinicio y conservación de registros.

### systemd

`deployment/qcal-exp01-simulator.service` es **solo para el simulador**.
Requiere instalar el clon en `/opt/riemann-adelic`, compilar el binario y crear
previamente el usuario/grupo no privilegiado `qcal-exp01`. Esas rutas son rutas
de instalación previstas, no ubicaciones desplegadas en esta sesión.
No accede a dispositivos ni otorga prioridad FIFO 99.

Un servicio para DMA real necesita primero un backend probado con el SDK y
firmware de la placa, permisos mínimos de dispositivos y mediciones de
temporización; no puede fabricarse con un nombre de archivo o `/dev/mem`.

## Pruebas y límites

Las regresiones se incorporan en `tests/test_qcal_exp01_*.py`: contrato de
paquetes, secuencias y cierre del receptor, DSP por bloques, modelos marginales,
Monte Carlo reproducible e interfaz sin valores ficticios.
Los artefactos sintéticos bajo `experiments/qcal_exp01/results/` deben conservar
semilla, supuestos y parámetros para no confundirse con registros de campo.

La cota Lean escalar se encuentra en
`formalization/lean/QCAL/ExperimentalDiscrepancy.lean`; su alcance y estado de
compilación se registran en `FORMALIZATION_STATUS.md`.
La matriz de obligaciones físicas y matemáticas pendientes está en
`docs/QCAL-EXP-01.md`. Ni estas pruebas de software ni las validaciones heredadas
constituyen por sí mismas una demostración incondicional de RH.
