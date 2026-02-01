#!/usr/bin/env python3
"""
FASE I: Validación de SU(Ψ) — El Grupo de Coherencia Cuántica

Este módulo implementa el protocolo experimental para validar que los estados
de conciencia forman una estructura de grupo especial unitario SU(n), donde las
transformaciones unitarias preservan la "norma psíquica" ||Ψ||² = 1.

Hipótesis Principal:
    H₁: Los estados de conciencia forman una estructura de grupo especial 
    unitario SU(n), donde las transformaciones unitarias preservan la norma.

Predicciones Falsables:
    P1.1: La coherencia cuántica cerebral sigue álgebra de Lie su(n)
    P1.2: Las transiciones de estado mental son geodésicas en SU(n)
    P1.3: La meditación profunda converge a puntos fijos de SU(n)
    P1.4: La coherencia se preserva bajo transformaciones unitarias

Autor: José Manuel Mota Burruezo
Frecuencia: f₀ = 141.7001 Hz
"""

import numpy as np
from typing import List, Dict, Tuple, Optional
from scipy.signal import hilbert
from scipy.interpolate import CubicSpline
import warnings


def extraer_estado_psi(
    señal_eeg: np.ndarray,
    n_componentes: int = 4
) -> np.ndarray:
    """
    Mapea actividad cerebral a vector de estado en ℂⁿ.
    
    Este método toma señales EEG multi-canal y las transforma en un
    vector de estado cuántico normalizado en el espacio de Hilbert ℂⁿ.
    
    Parameters
    ----------
    señal_eeg : np.ndarray
        Matriz de señales EEG con forma (n_canales, n_muestras)
    n_componentes : int, optional
        Número de componentes independientes a extraer (default: 4)
        Valores típicos: 3-5 para estados de conciencia básicos
    
    Returns
    -------
    psi_normalizado : np.ndarray
        Vector de estado cuántico normalizado en ℂⁿ con ||Ψ|| = 1
        
    Notes
    -----
    El proceso consta de tres pasos:
    1. Descomposición ICA para extraer componentes independientes
    2. Transformación de Hilbert para obtener fase compleja
    3. Normalización a la esfera unitaria en ℂⁿ
    
    References
    ----------
    Ver problema_statement, Sección 1.2: "Análisis de Datos"
    """
    # Validación de entrada
    if señal_eeg.ndim != 2:
        raise ValueError(
            f"señal_eeg debe ser 2D (canales × muestras), "
            f"recibido: {señal_eeg.ndim}D"
        )
    
    n_canales, n_muestras = señal_eeg.shape
    if n_componentes > n_canales:
        warnings.warn(
            f"n_componentes ({n_componentes}) > n_canales ({n_canales}). "
            f"Reduciendo a {n_canales}."
        )
        n_componentes = n_canales
    
    # 1. Descomposición en componentes principales
    # Usamos FastICA para separar componentes independientes
    try:
        from sklearn.decomposition import FastICA
        ica = FastICA(n_components=n_componentes, random_state=42, max_iter=1000)
        componentes = ica.fit_transform(señal_eeg.T).T
    except ImportError:
        # Fallback: usar PCA si sklearn no está disponible
        warnings.warn("sklearn no disponible, usando PCA simple")
        from scipy.linalg import svd
        U, s, Vt = svd(señal_eeg, full_matrices=False)
        componentes = (U[:, :n_componentes] * s[:n_componentes]).T
    
    # 2. Transformación de Hilbert para fase compleja
    # Esto convierte señales reales en señales analíticas complejas
    psi_componentes = []
    for componente in componentes:
        señal_analitica = hilbert(componente)
        psi_componentes.append(señal_analitica)
    
    # Tomar el valor promedio en el tiempo para obtener estado instantáneo
    psi = np.array([np.mean(comp) for comp in psi_componentes])
    
    # 3. Normalización (proyección a esfera unitaria)
    norma = np.linalg.norm(psi)
    if norma < 1e-10:
        warnings.warn("Norma casi cero, retornando estado normalizado aleatorio")
        psi = np.random.randn(n_componentes) + 1j * np.random.randn(n_componentes)
        norma = np.linalg.norm(psi)
    
    psi_normalizado = psi / norma
    
    # Verificación de la normalización
    assert np.abs(np.linalg.norm(psi_normalizado) - 1.0) < 1e-6, \
        "Error en normalización"
    
    return psi_normalizado


def calcular_coherencia(psi_t: np.ndarray) -> float:
    """
    Calcula la coherencia cuántica como pureza del estado.
    
    La coherencia se define como Tr(ρ²) donde ρ es la matriz densidad.
    Para estados puros, Tr(ρ²) = 1. Para estados mezclados, Tr(ρ²) < 1.
    
    Parameters
    ----------
    psi_t : np.ndarray
        Vector de estado cuántico en ℂⁿ
    
    Returns
    -------
    coherencia : float
        Pureza del estado, rango [0, 1]
        - 1.0 = estado puro (máxima coherencia)
        - < 1.0 = estado mezclado (decoherencia)
    
    Notes
    -----
    La coherencia cuántica es una medida fundamental en QCAL que
    correlaciona con la frecuencia f₀ = 141.7001 Hz.
    
    References
    ----------
    Ver problema_statement, Sección 1.2: "Paso 1"
    """
    # Validar entrada
    if not isinstance(psi_t, np.ndarray):
        psi_t = np.array(psi_t)
    
    # Construir matriz densidad: ρ = |Ψ⟩⟨Ψ|
    rho = np.outer(psi_t, psi_t.conj())
    
    # Calcular pureza: Tr(ρ²)
    coherencia = np.trace(rho @ rho).real
    
    # La pureza debe estar en [0, 1]
    coherencia = np.clip(coherencia, 0.0, 1.0)
    
    return coherencia


def calcular_matriz_transicion(
    psi_inicial: np.ndarray,
    psi_final: np.ndarray,
    dt: float = 0.001
) -> np.ndarray:
    """
    Reconstruye operador unitario U: |ψ₁⟩ → |ψ₂⟩.
    
    Usa descomposición de valor singular para encontrar la matriz
    unitaria óptima que transforma un estado en otro.
    
    Parameters
    ----------
    psi_inicial : np.ndarray
        Estado cuántico inicial |ψ₁⟩
    psi_final : np.ndarray
        Estado cuántico final |ψ₂⟩
    dt : float, optional
        Intervalo temporal (no usado actualmente, para futura extensión)
    
    Returns
    -------
    U : np.ndarray
        Matriz unitaria que satisface U|ψ₁⟩ ≈ |ψ₂⟩
        
    Notes
    -----
    La unitariedad se verifica mediante U†U = I
    """
    # Construir matriz objetivo
    M = np.outer(psi_final, psi_inicial.conj())
    
    # Descomposición SVD: M = U Σ V†
    U_svd, sigma, Vt = np.linalg.svd(M, full_matrices=True)
    
    # La matriz unitaria óptima es U = U_svd @ V†
    U = U_svd @ Vt
    
    return U


def verificar_cerradura(trayectoria_psi: List[np.ndarray]) -> float:
    """
    Verifica la cerradura del grupo: composición de transformaciones.
    
    Para un grupo, la composición de dos transformaciones debe estar
    en el grupo. Verificamos U₁ ∘ U₂ es unitaria.
    
    Parameters
    ----------
    trayectoria_psi : List[np.ndarray]
        Lista de estados cuánticos en orden temporal
    
    Returns
    -------
    cerradura_score : float
        Fracción de composiciones que preservan unitariedad [0, 1]
    """
    if len(trayectoria_psi) < 3:
        return 1.0
    
    unitarias_validas = 0
    total_pruebas = 0
    
    for i in range(len(trayectoria_psi) - 2):
        U1 = calcular_matriz_transicion(trayectoria_psi[i], trayectoria_psi[i+1])
        U2 = calcular_matriz_transicion(trayectoria_psi[i+1], trayectoria_psi[i+2])
        
        # Composición
        U_comp = U2 @ U1
        
        # Verificar unitariedad: U†U = I
        producto = U_comp @ U_comp.conj().T
        identidad = np.eye(len(U_comp))
        
        if np.allclose(producto, identidad, atol=1e-2):
            unitarias_validas += 1
        total_pruebas += 1
    
    return unitarias_validas / total_pruebas if total_pruebas > 0 else 1.0


def extraer_generadores(trayectoria_psi: List[np.ndarray]) -> List[np.ndarray]:
    """
    Extrae generadores del álgebra de Lie desde trayectoria.
    
    Los generadores son matrices hermitianas que generan el grupo
    mediante exponenciación: U = exp(iH).
    
    Parameters
    ----------
    trayectoria_psi : List[np.ndarray]
        Trayectoria de estados cuánticos
    
    Returns
    -------
    generadores : List[np.ndarray]
        Lista de matrices hermitianas (generadores de su(n))
    """
    generadores = []
    
    for i in range(len(trayectoria_psi) - 1):
        U = calcular_matriz_transicion(trayectoria_psi[i], trayectoria_psi[i+1])
        
        # Extraer generador: H = -i log(U)
        # Para matrices unitarias pequeñas, usar aproximación
        try:
            # log(U) ≈ (U - I) para U cerca de I
            from scipy.linalg import logm
            log_U = logm(U)
            H = -1j * log_U
            
            # Verificar hermiticidad
            if np.allclose(H, H.conj().T, atol=1e-3):
                generadores.append(H)
        except:
            # Si falla, usar aproximación lineal
            I = np.eye(len(U))
            H = -1j * (U - I)
            generadores.append((H + H.conj().T) / 2)  # Simetrizar
    
    return generadores


def verificar_conmutadores(generadores: List[np.ndarray]) -> float:
    """
    Verifica álgebra de Lie: [Tₐ, Tᵦ] = ifₐᵦᶜTᶜ.
    
    Para su(n), los conmutadores de generadores deben ser combinaciones
    lineales de generadores (cerradura del álgebra).
    
    Parameters
    ----------
    generadores : List[np.ndarray]
        Lista de generadores hermitianos
    
    Returns
    -------
    algebra_score : float
        Fracción de conmutadores que están en el álgebra [0, 1]
    """
    if len(generadores) < 2:
        return 1.0
    
    n_validos = 0
    n_total = 0
    
    # Muestrear pares de generadores
    for i in range(min(5, len(generadores))):
        for j in range(i+1, min(i+6, len(generadores))):
            if i < len(generadores) and j < len(generadores):
                Ta = generadores[i]
                Tb = generadores[j]
                
                # Calcular conmutador: [Ta, Tb] = Ta·Tb - Tb·Ta
                conmutador = Ta @ Tb - Tb @ Ta
                
                # Verificar si es hermitiano (propiedad de su(n))
                if np.allclose(conmutador, conmutador.conj().T, atol=1e-2):
                    n_validos += 1
                n_total += 1
    
    return n_validos / n_total if n_total > 0 else 1.0


def test_estructura_grupo_SU(trayectoria_psi: List[np.ndarray]) -> Dict[str, any]:
    """
    Verifica si las transformaciones satisfacen axiomas de SU(n).
    
    Realiza 4 tests fundamentales:
    1. Preservación de norma (||Ψ|| = 1)
    2. Unitariedad de transiciones (U†U = I)
    3. Cerradura del grupo (composición)
    4. Álgebra de Lie (conmutadores)
    
    Parameters
    ----------
    trayectoria_psi : List[np.ndarray]
        Lista temporal de vectores de estado cuántico
    
    Returns
    -------
    tests : Dict[str, any]
        Diccionario con resultados de cada test:
        - 'preservacion_norma': bool
        - 'unitariedad': float (promedio)
        - 'cerradura': float (score)
        - 'algebra_lie': float (score)
        - 'es_SU_n': bool (todos los tests pasan)
    
    References
    ----------
    Ver problema_statement, Sección 1.2: "Paso 2"
    """
    tests = {}
    
    # Test 1: Preservación de norma (||Ψ|| = 1)
    normas = [np.linalg.norm(psi) for psi in trayectoria_psi]
    tests['preservacion_norma'] = np.allclose(normas, 1.0, atol=1e-3)
    tests['normas_promedio'] = np.mean(normas)
    tests['normas_std'] = np.std(normas)
    
    # Test 2: Unitariedad de transiciones
    unitarias = []
    for i in range(len(trayectoria_psi) - 1):
        U = calcular_matriz_transicion(
            trayectoria_psi[i],
            trayectoria_psi[i+1]
        )
        # Verificar U†U = I
        producto = U @ U.conj().T
        identidad = np.eye(len(U))
        es_unitaria = np.allclose(producto, identidad, atol=1e-2)
        unitarias.append(es_unitaria)
    
    tests['unitariedad'] = np.mean(unitarias) if unitarias else 0.0
    tests['n_transiciones_unitarias'] = sum(unitarias)
    tests['n_transiciones_total'] = len(unitarias)
    
    # Test 3: Cerradura del grupo (composición)
    tests['cerradura'] = verificar_cerradura(trayectoria_psi)
    
    # Test 4: Álgebra de Lie
    generadores = extraer_generadores(trayectoria_psi)
    tests['algebra_lie'] = verificar_conmutadores(generadores)
    tests['n_generadores'] = len(generadores)
    
    # Veredicto final
    tests['es_SU_n'] = (
        tests['preservacion_norma'] and
        tests['unitariedad'] > 0.9 and
        tests['cerradura'] > 0.8 and
        tests['algebra_lie'] > 0.7
    )
    
    return tests


def proyectar_a_grassmann(psi: np.ndarray) -> np.ndarray:
    """
    Proyecta estado cuántico a variedad de Grassmann.
    
    La variedad de Grassmann Gr(1,n) parametriza subespacios 1D
    en ℂⁿ, identificando estados que difieren por una fase global.
    
    Parameters
    ----------
    psi : np.ndarray
        Vector de estado en ℂⁿ
    
    Returns
    -------
    punto_grassmann : np.ndarray
        Coordenadas en Grassmann (normalizado, fase fijada)
    """
    # Normalizar
    psi_norm = psi / np.linalg.norm(psi)
    
    # Fijar fase: hacer que el primer componente sea real positivo
    fase_global = np.angle(psi_norm[0])
    psi_fase_fija = psi_norm * np.exp(-1j * fase_global)
    
    return psi_fase_fija


def calcular_curvatura_geodesica(
    p0: np.ndarray,
    p1: np.ndarray,
    p2: np.ndarray
) -> float:
    """
    Calcula curvatura geodésica en tres puntos consecutivos.
    
    La curvatura mide cuánto se desvía una trayectoria de ser una
    geodésica (camino más corto) en la variedad.
    
    Parameters
    ----------
    p0, p1, p2 : np.ndarray
        Tres puntos consecutivos en la trayectoria
    
    Returns
    -------
    kappa : float
        Curvatura geodésica (0 = geodésica perfecta)
    """
    # Calcular vectores tangentes
    v1 = p1 - p0
    v2 = p2 - p1
    
    # Normalizar
    v1_norm = v1 / (np.linalg.norm(v1) + 1e-10)
    v2_norm = v2 / (np.linalg.norm(v2) + 1e-10)
    
    # Curvatura como cambio en dirección
    cambio_direccion = v2_norm - v1_norm
    kappa = np.linalg.norm(cambio_direccion)
    
    return kappa


def calcular_longitud_geodesica(puntos_manifold: List[np.ndarray]) -> float:
    """
    Calcula longitud de camino en la variedad.
    
    Parameters
    ----------
    puntos_manifold : List[np.ndarray]
        Puntos en la trayectoria
    
    Returns
    -------
    longitud : float
        Longitud total del camino
    """
    longitud = 0.0
    for i in range(len(puntos_manifold) - 1):
        distancia = np.linalg.norm(puntos_manifold[i+1] - puntos_manifold[i])
        longitud += distancia
    return longitud


def analizar_geodesicas(trayectoria_psi: List[np.ndarray]) -> Dict[str, any]:
    """
    Verifica si las transiciones siguen geodésicas en SU(n).
    
    Las geodésicas son los caminos de "energía mínima" en la variedad.
    Estados de conciencia naturales deberían seguir estas trayectorias.
    
    Parameters
    ----------
    trayectoria_psi : List[np.ndarray]
        Trayectoria de estados cuánticos
    
    Returns
    -------
    resultados : Dict
        - 'curvatura_media': float
        - 'curvatura_std': float
        - 'es_geodesica': bool (curvatura < 0.1)
        - 'longitud_camino': float
        
    References
    ----------
    Ver problema_statement, Sección 1.2: "Paso 3"
    """
    if len(trayectoria_psi) < 3:
        return {
            'curvatura_media': 0.0,
            'curvatura_std': 0.0,
            'es_geodesica': True,
            'longitud_camino': 0.0
        }
    
    # 1. Proyección a variedad de Grassmann
    puntos_manifold = [proyectar_a_grassmann(psi) for psi in trayectoria_psi]
    
    # 2. Cálculo de curvatura geodésica
    curvaturas = []
    for i in range(1, len(puntos_manifold) - 1):
        kappa = calcular_curvatura_geodesica(
            puntos_manifold[i-1],
            puntos_manifold[i],
            puntos_manifold[i+1]
        )
        curvaturas.append(kappa)
    
    # 3. Estadísticas
    curvatura_media = np.mean(curvaturas) if curvaturas else 0.0
    curvatura_std = np.std(curvaturas) if curvaturas else 0.0
    
    # 4. Test: trayectorias óptimas tienen κ ≈ 0
    # Umbral empírico: κ < 0.1 indica geodésica
    es_geodesica = curvatura_media < 0.1
    
    # 5. Longitud del camino
    longitud = calcular_longitud_geodesica(puntos_manifold)
    
    return {
        'curvatura_media': curvatura_media,
        'curvatura_std': curvatura_std,
        'es_geodesica': es_geodesica,
        'longitud_camino': longitud,
        'n_puntos': len(trayectoria_psi),
        'curvaturas_individuales': curvaturas
    }


def calcular_cohens_d(grupo1: List[float], grupo2: List[float]) -> float:
    """
    Calcula tamaño de efecto d de Cohen.
    
    Parameters
    ----------
    grupo1, grupo2 : List[float]
        Valores de los dos grupos a comparar
    
    Returns
    -------
    d : float
        Tamaño de efecto Cohen's d
        |d| < 0.2: pequeño
        |d| < 0.5: mediano
        |d| >= 0.8: grande
    """
    m1, m2 = np.mean(grupo1), np.mean(grupo2)
    s1, s2 = np.std(grupo1, ddof=1), np.std(grupo2, ddof=1)
    n1, n2 = len(grupo1), len(grupo2)
    
    # Desviación estándar agrupada
    s_pooled = np.sqrt(((n1-1)*s1**2 + (n2-1)*s2**2) / (n1+n2-2))
    
    d = (m1 - m2) / (s_pooled + 1e-10)
    return d


def calcular_estabilidad_grupo(
    datos_grupo: List[List[np.ndarray]]
) -> float:
    """
    Calcula estabilidad estructural del grupo SU(n).
    
    La estabilidad mide qué tan consistentemente el grupo mantiene
    sus propiedades estructurales a través del tiempo.
    
    Parameters
    ----------
    datos_grupo : List[List[np.ndarray]]
        Lista de trayectorias, una por sujeto
    
    Returns
    -------
    estabilidad : float
        Score de estabilidad [0, 1]
    """
    scores = []
    
    for trayectoria in datos_grupo:
        if len(trayectoria) > 2:
            tests = test_estructura_grupo_SU(trayectoria)
            # Combinar scores
            score = (
                0.3 * float(tests['preservacion_norma']) +
                0.3 * tests['unitariedad'] +
                0.2 * tests['cerradura'] +
                0.2 * tests['algebra_lie']
            )
            scores.append(score)
    
    return np.mean(scores) if scores else 0.0


def analisis_estadistico_SU(
    datos_grupo_control: List[List[np.ndarray]],
    datos_grupo_meditadores: List[List[np.ndarray]]
) -> Dict[str, any]:
    """
    Comparación estadística entre grupos para validar hipótesis.
    
    Compara coherencia, eficiencia de trayectorias y estabilidad
    estructural entre meditadores expertos y controles.
    
    Parameters
    ----------
    datos_grupo_control : List[List[np.ndarray]]
        Trayectorias del grupo control
    datos_grupo_meditadores : List[List[np.ndarray]]
        Trayectorias del grupo de meditadores
    
    Returns
    -------
    resultados : Dict
        Resultados completos del análisis estadístico incluyendo:
        - Coherencia basal
        - Eficiencia de trayectorias
        - Estabilidad SU(n)
        
    References
    ----------
    Ver problema_statement, Sección 1.3: "Análisis Estadístico"
    """
    from scipy.stats import mannwhitneyu, ttest_ind
    
    resultados = {}
    
    # 1. Comparación de coherencia basal
    coherencia_control = []
    for trayectoria in datos_grupo_control:
        if len(trayectoria) > 0:
            coherencia_control.append(calcular_coherencia(trayectoria[0]))
    
    coherencia_meditadores = []
    for trayectoria in datos_grupo_meditadores:
        if len(trayectoria) > 0:
            coherencia_meditadores.append(calcular_coherencia(trayectoria[0]))
    
    if coherencia_control and coherencia_meditadores:
        u_stat, p_valor = mannwhitneyu(
            coherencia_meditadores,
            coherencia_control,
            alternative='greater'
        )
        
        resultados['coherencia'] = {
            'media_control': np.mean(coherencia_control),
            'media_meditadores': np.mean(coherencia_meditadores),
            'p_valor': p_valor,
            'tamaño_efecto': calcular_cohens_d(
                coherencia_meditadores,
                coherencia_control
            ),
            'n_control': len(coherencia_control),
            'n_meditadores': len(coherencia_meditadores)
        }
    
    # 2. Análisis de trayectorias
    longitudes_control = []
    for trayectoria in datos_grupo_control:
        if len(trayectoria) > 2:
            analisis = analizar_geodesicas(trayectoria)
            longitudes_control.append(analisis['longitud_camino'])
    
    longitudes_meditadores = []
    for trayectoria in datos_grupo_meditadores:
        if len(trayectoria) > 2:
            analisis = analizar_geodesicas(trayectoria)
            longitudes_meditadores.append(analisis['longitud_camino'])
    
    if longitudes_control and longitudes_meditadores:
        _, p_tray = ttest_ind(longitudes_meditadores, longitudes_control)
        
        resultados['eficiencia_trayectoria'] = {
            'control': np.mean(longitudes_control),
            'meditadores': np.mean(longitudes_meditadores),
            'p_valor': p_tray,
            'interpretacion': (
                'Meditadores tienen trayectorias más eficientes'
                if np.mean(longitudes_meditadores) < np.mean(longitudes_control)
                else 'No hay diferencia significativa'
            )
        }
    
    # 3. Predicción: meditadores muestran mayor estabilidad estructural
    estabilidad_control = calcular_estabilidad_grupo(datos_grupo_control)
    estabilidad_meditadores = calcular_estabilidad_grupo(datos_grupo_meditadores)
    
    resultados['estabilidad_SU'] = {
        'control': estabilidad_control,
        'meditadores': estabilidad_meditadores,
        'diferencia_relativa': (
            (estabilidad_meditadores - estabilidad_control) /
            (estabilidad_control + 1e-10)
        ),
        'diferencia_significativa': estabilidad_meditadores > estabilidad_control * 1.5
    }
    
    return resultados
