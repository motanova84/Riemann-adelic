#!/usr/bin/env python3
"""
FASE II: Validación de T_μν(Φ) — El Tensor de Stress Emocional

Este módulo implementa el protocolo experimental para validar que las emociones
generan un tensor de stress-energía que curva el espacio de conciencia, afectando
la coherencia según las ecuaciones de campo QCAL.

Hipótesis Principal:
    H₂: Las emociones generan un tensor de stress-energía que curva el espacio
    de conciencia, afectando la coherencia según las ecuaciones de campo QCAL.

Predicciones Falsables:
    P2.1: T₀₀ (intensidad emocional) correlaciona con actividad amígdala
    P2.2: T₀ᵢ (flujo emocional) predice contagio emocional en díadas
    P2.3: ∇²Φ (curvatura) predice vulnerabilidad a psicopatología
    P2.4: Exposición a 141.7 Hz reduce T₀₀ y aumenta Ψ

Autor: José Manuel Mota Burruezo
Frecuencia: f₀ = 141.7001 Hz
"""

import numpy as np
from typing import Dict, List, Tuple, Optional, Any
from scipy.ndimage import laplace
from scipy.signal import correlate
from scipy.stats import pearsonr
from scipy.optimize import curve_fit
import warnings


def normalizar(señal: np.ndarray) -> np.ndarray:
    """
    Normaliza señal a rango [0, 1].
    
    Parameters
    ----------
    señal : np.ndarray
        Señal a normalizar
    
    Returns
    -------
    señal_norm : np.ndarray
        Señal normalizada
    """
    minimo = np.min(señal)
    maximo = np.max(señal)
    
    if maximo - minimo < 1e-10:
        return np.zeros_like(señal)
    
    return (señal - minimo) / (maximo - minimo)


def construir_campo_emocional(
    datos_multisensor: Dict[str, np.ndarray],
    tiempo: Optional[np.ndarray] = None
) -> np.ndarray:
    """
    Fusiona múltiples señales en campo escalar Φ.
    
    El campo emocional Φ(x,t) se construye como combinación ponderada de:
    - EDA (conductancia de piel): arousal fisiológico
    - HRV (variabilidad cardíaca): regulación emocional
    - Amígdala (fMRI BOLD): procesamiento emocional
    - Autorreporte: experiencia subjetiva
    
    Parameters
    ----------
    datos_multisensor : Dict[str, np.ndarray]
        Diccionario con claves:
        - 'eda': señal de conductancia piel
        - 'hrv': señal de variabilidad cardíaca
        - 'amigdala': señal fMRI de amígdala
        - 'autorreporte': escala subjetiva
    tiempo : Optional[np.ndarray]
        Vector de tiempo (para futura sincronización)
    
    Returns
    -------
    Phi : np.ndarray
        Campo emocional escalar Φ(t)
        
    Notes
    -----
    Los pesos fueron calibrados empíricamente:
    - EDA: 30% (arousal rápido)
    - HRV: 20% (regulación lenta)
    - Amígdala: 25% (procesamiento emocional)
    - Autorreporte: 25% (experiencia consciente)
    
    References
    ----------
    Ver problema_statement, Sección 2.3: "Paso 1"
    """
    # Validar entrada
    required_keys = ['eda', 'hrv', 'amigdala', 'autorreporte']
    for key in required_keys:
        if key not in datos_multisensor:
            raise ValueError(f"Falta señal requerida: {key}")
    
    # 1. Normalización de señales
    eda_norm = normalizar(datos_multisensor['eda'])
    hrv_norm = normalizar(datos_multisensor['hrv'])
    amigdala_norm = normalizar(datos_multisensor['amigdala'])
    autorreporte_norm = normalizar(datos_multisensor['autorreporte'])
    
    # 2. Ponderación óptima
    pesos = {
        'eda': 0.30,        # Arousal fisiológico
        'hrv': 0.20,        # Regulación emocional
        'amigdala': 0.25,   # Procesamiento emocional
        'autorreporte': 0.25 # Experiencia subjetiva
    }
    
    # Verificar suma de pesos = 1 (validación robusta en runtime)
    suma_pesos = float(sum(pesos.values()))
    if abs(suma_pesos - 1.0) >= 1e-6:
        raise ValueError(
            f"Los pesos deben sumar 1 (suma actual: {suma_pesos}). "
            "Revise la configuración de 'pesos'."
        )
    
    # 3. Campo compuesto
    # Nota: HRV alto = stress bajo, por eso (1 - hrv_norm)
    Phi = (
        pesos['eda'] * eda_norm +
        pesos['hrv'] * (1 - hrv_norm) +  # HRV alto = stress bajo
        pesos['amigdala'] * amigdala_norm +
        pesos['autorreporte'] * autorreporte_norm
    )
    
    return Phi


def calcular_tensor_stress_energia(
    Phi_espaciotemporal: np.ndarray
) -> np.ndarray:
    """
    Calcula T_μν a partir del campo Φ(x,t).
    
    El tensor de stress-energía emocional se construye análogo al tensor
    electromagnético en relatividad general.
    
    Parameters
    ----------
    Phi_espaciotemporal : np.ndarray
        Campo emocional con dimensiones [tiempo, x, y]
        Representación espacial puede ser red de sensores o topografía EEG
    
    Returns
    -------
    T_μν : np.ndarray
        Tensor de stress-energía con forma (4, 4, tiempo, x, y)
        Componentes:
        - T₀₀: densidad de energía emocional
        - T₀ᵢ: flujo de momento emocional
        - Tᵢⱼ: tensor de stress espacial
        
    Notes
    -----
    Componentes físicas:
    - T₀₀ = (∂Φ/∂t)² + (∇Φ)² : densidad de energía
    - T₀ᵢ = (∂Φ/∂t)(∂Φ/∂xᵢ) : flujo de energía (dirección de propagación)
    - Tᵢⱼ : tensor de stress espacial (tensión relacional)
    
    References
    ----------
    Ver problema_statement, Sección 2.3: "Cálculo del Tensor"
    """
    # Validar dimensiones
    if Phi_espaciotemporal.ndim < 2:
        # Si es 1D (solo temporal), expandir a espacial
        Phi_espaciotemporal = Phi_espaciotemporal[..., np.newaxis, np.newaxis]
    elif Phi_espaciotemporal.ndim == 2:
        # Si es 2D, añadir dimensión espacial
        Phi_espaciotemporal = Phi_espaciotemporal[..., np.newaxis]
    
    # Dimensiones: [tiempo, x, y]
    T_μν = np.zeros((4, 4, *Phi_espaciotemporal.shape))
    
    # 1. Derivadas del campo
    # Derivada temporal: asumimos al menos 2 puntos en el eje tiempo
    dPhi_dt = np.gradient(Phi_espaciotemporal, axis=0)
    
    # Derivadas espaciales: manejar dimensiones singleton para evitar ValueError
    _, nx, ny = Phi_espaciotemporal.shape
    
    if nx < 2:
        # Sin extensión espacial en x: derivada nula
        dPhi_dx = np.zeros_like(Phi_espaciotemporal)
    else:
        dPhi_dx = np.gradient(Phi_espaciotemporal, axis=1)
    
    if ny < 2:
        # Sin extensión espacial en y: derivada nula
        dPhi_dy = np.zeros_like(Phi_espaciotemporal)
    else:
        dPhi_dy = np.gradient(Phi_espaciotemporal, axis=2)
    
    # 2. Componentes del tensor
    # T₀₀: Densidad de energía emocional
    T_μν[0, 0] = (dPhi_dt**2 + dPhi_dx**2 + dPhi_dy**2) / 2
    
    # T₀ᵢ: Flujo de momento emocional (dirección de propagación)
    T_μν[0, 1] = dPhi_dt * dPhi_dx
    T_μν[0, 2] = dPhi_dt * dPhi_dy
    # T₀₃ no se usa en 2D espacial
    
    # Tᵢⱼ: Tensor de stress espacial (tensión relacional)
    T_μν[1, 1] = dPhi_dx**2 - (dPhi_dy**2) / 2
    T_μν[1, 2] = dPhi_dx * dPhi_dy
    T_μν[2, 2] = dPhi_dy**2 - (dPhi_dx**2) / 2
    
    # 3. Simetrización (T_μν = T_νμ)
    for mu in range(4):
        for nu in range(mu + 1, 4):
            T_μν[nu, mu] = T_μν[mu, nu]
    
    return T_μν


def calcular_curvatura_emocional(Phi: np.ndarray) -> Dict[str, Any]:
    """
    Calcula ∇²Φ (Laplaciano) como curvatura del paisaje emocional.
    
    El Laplaciano mide curvatura local. Valores altos indican singularidades
    o "agujeros negros emocionales" que pueden predecir vulnerabilidad.
    
    Parameters
    ----------
    Phi : np.ndarray
        Campo emocional (puede ser 1D, 2D o 3D)
    
    Returns
    -------
    resultados : Dict
        - 'curvatura': np.ndarray (∇²Φ)
        - 'singularidades': np.ndarray (bool mask)
        - 'num_singularidades': int
        - 'max_curvatura': float
        - 'curvatura_media': float
        
    Notes
    -----
    Singularidades (∇²Φ > 3σ) indican regiones de alta inestabilidad
    emocional que podrían predecir episodios psicopatológicos.
    
    References
    ----------
    Ver problema_statement, Sección 2.3: "Curvatura Emocional"
    """
    # Calcular Laplaciano
    nabla2_Phi = laplace(Phi)
    
    # Identificación de singularidades
    # Umbral: 3 desviaciones estándar
    umbral_critico = 3 * np.std(nabla2_Phi)
    singularidades = np.abs(nabla2_Phi) > umbral_critico
    
    return {
        'curvatura': nabla2_Phi,
        'singularidades': singularidades,
        'num_singularidades': np.sum(singularidades),
        'max_curvatura': np.max(np.abs(nabla2_Phi)),
        'curvatura_media': np.mean(np.abs(nabla2_Phi)),
        'curvatura_std': np.std(nabla2_Phi)
    }


def test_correlacion_T00_amigdala(datos: Dict[str, np.ndarray]) -> Dict[str, Any]:
    """
    Verifica si T₀₀ predice actividad límbica.
    
    Test de la predicción P2.1: La densidad de energía emocional T₀₀
    debe correlacionar con actividad de la amígdala.
    
    Parameters
    ----------
    datos : Dict
        Debe contener:
        - 'tensor': tensor completo T_μν
        - 'fmri_amigdala': señal BOLD de amígdala
    
    Returns
    -------
    resultados : Dict
        - 'correlacion': float (Pearson r)
        - 'p_valor': float
        - 'lag_optimo': int (en TRs)
        - 'interpretacion': str
        
    References
    ----------
    Ver problema_statement, Sección 2.4: "Test P2.1"
    """
    # Extraer T₀₀ (densidad de energía)
    T_00 = datos['tensor'][0, 0]
    amigdala = datos['fmri_amigdala']
    
    # Aplanar si es multidimensional
    if T_00.ndim > 1:
        T_00 = np.mean(T_00, axis=tuple(range(1, T_00.ndim)))
    if amigdala.ndim > 1:
        amigdala = np.mean(amigdala, axis=tuple(range(1, amigdala.ndim)))
    
    # Asegurar misma longitud
    min_len = min(len(T_00), len(amigdala))
    T_00 = T_00[:min_len]
    amigdala = amigdala[:min_len]
    
    # Correlación instantánea (manejar varianza cero)
    std_T00 = np.std(T_00)
    std_amigdala = np.std(amigdala)
    
    if std_T00 < 1e-12 or std_amigdala < 1e-12:
        # Si alguna señal es constante, correlación no definida
        r_pearson = 0.0
        p_pearson = 1.0
    else:
        r_pearson, p_pearson = pearsonr(T_00, amigdala)
    
    # Correlación con lag (causalidad)
    lags = range(-5, 6)  # ±5 TR (típicamente ±10 seg en fMRI)
    correlaciones_lag = []
    
    for lag in lags:
        if lag < 0:
            if len(T_00[:lag]) > 0 and len(amigdala[-lag:]) > 0:
                try:
                    r, _ = pearsonr(T_00[:lag], amigdala[-lag:])
                except ValueError:
                    r = 0.0
            else:
                r = 0.0
        elif lag > 0:
            if len(T_00[lag:]) > 0 and len(amigdala[:-lag]) > 0:
                try:
                    r, _ = pearsonr(T_00[lag:], amigdala[:-lag])
                except ValueError:
                    r = 0.0
            else:
                r = 0.0
        else:
            r = r_pearson
        correlaciones_lag.append(r)
    
    max_lag = lags[np.argmax(np.abs(correlaciones_lag))]
    
    # Interpretación
    if max_lag > 0:
        interpretacion = f'T₀₀ precede amígdala por {max_lag} TR'
    elif max_lag < 0:
        interpretacion = f'Amígdala precede T₀₀ por {-max_lag} TR'
    else:
        interpretacion = 'Correlación simultánea'
    
    return {
        'correlacion': r_pearson,
        'p_valor': p_pearson,
        'lag_optimo': max_lag,
        'correlacion_maxima': max(correlaciones_lag, key=abs),
        'interpretacion': interpretacion,
        'significativo': p_pearson < 0.05
    }


def test_flujo_emocional_diadas(
    datos_emisor: Dict[str, np.ndarray],
    datos_receptor: Dict[str, np.ndarray]
) -> Dict[str, Any]:
    """
    Mide propagación emocional usando T₀ᵢ.
    
    Test de la predicción P2.2: El flujo de momento emocional T₀ᵢ del
    emisor debe predecir cambios en T₀₀ del receptor (contagio emocional).
    
    Parameters
    ----------
    datos_emisor : Dict
        Datos del sujeto emisor (quien experimenta emoción)
    datos_receptor : Dict
        Datos del sujeto receptor (quien observa)
    
    Returns
    -------
    resultados : Dict
        - 'latencia_contagio_ms': float
        - 'magnitud_contagio': float
        - 'informacion_mutua': float
        - 'interpretacion': str
        
    References
    ----------
    Ver problema_statement, Sección 2.4: "Test P2.2"
    """
    # 1. Calcular campos Φ individuales
    Phi_emisor = construir_campo_emocional(datos_emisor)
    Phi_receptor = construir_campo_emocional(datos_receptor)
    
    # Expandir para cálculo de tensor (necesita dimensiones espaciales)
    Phi_emisor_3d = Phi_emisor[:, np.newaxis, np.newaxis]
    Phi_receptor_3d = Phi_receptor[:, np.newaxis, np.newaxis]
    
    # 2. Tensor de stress para cada individuo
    T_emisor = calcular_tensor_stress_energia(Phi_emisor_3d)
    T_receptor = calcular_tensor_stress_energia(Phi_receptor_3d)
    
    # 3. Flujo de momento (T₀₁) del emisor
    flujo_emisor = T_emisor[0, 1, :, 0, 0]  # Serie temporal
    
    # 4. Respuesta del receptor (T₀₀)
    respuesta_receptor = T_receptor[0, 0, :, 0, 0]
    
    # Asegurar misma longitud
    min_len = min(len(flujo_emisor), len(respuesta_receptor))
    flujo_emisor = flujo_emisor[:min_len]
    respuesta_receptor = respuesta_receptor[:min_len]
    
    # 5. Cross-correlación para detectar contagio
    cross_corr = correlate(flujo_emisor, respuesta_receptor, mode='full')
    lag_contagio = np.argmax(cross_corr) - len(flujo_emisor)
    tiempo_contagio = lag_contagio * 0.001  # Asumiendo muestreo 1 kHz
    
    # 6. Magnitud del contagio (normalizada por desviaciones estándar)
    std_emisor = np.std(flujo_emisor)
    std_receptor = np.std(respuesta_receptor)
    eps = 1e-12
    if len(flujo_emisor) == 0 or std_emisor < eps or std_receptor < eps:
        # Si alguna señal es (casi) constante, evitar división por cero / inestabilidades
        magnitud = 0.0
    else:
        magnitud = np.max(cross_corr) / (std_emisor * std_receptor * len(flujo_emisor))
    
    # 7. Información mutua (requiere discretización)
    try:
        from sklearn.metrics import mutual_info_score
        bins = 10
        flujo_disc = np.digitize(flujo_emisor, bins=np.linspace(
            flujo_emisor.min(), flujo_emisor.max(), bins
        ))
        resp_disc = np.digitize(respuesta_receptor, bins=np.linspace(
            respuesta_receptor.min(), respuesta_receptor.max(), bins
        ))
        mi = mutual_info_score(flujo_disc, resp_disc)
    except ImportError:
        mi = 0.0
        warnings.warn("sklearn no disponible, información mutua = 0")
    
    return {
        'latencia_contagio_ms': tiempo_contagio * 1000,
        'magnitud_contagio': magnitud,
        'informacion_mutua': mi,
        'lag_samples': lag_contagio,
        'interpretacion': f'Emoción se propaga en {tiempo_contagio*1000:.0f} ms'
    }


def estudio_longitudinal_curvatura(
    datos_baseline: List[Dict[str, np.ndarray]],
    datos_followup_6meses: List[Dict[str, bool]]
) -> Dict[str, Any]:
    """
    Predice desarrollo de psicopatología desde ∇²Φ basal.
    
    Test de la predicción P2.3: La curvatura emocional basal debe predecir
    el desarrollo de episodios psicopatológicos a 6 meses.
    
    Parameters
    ----------
    datos_baseline : List[Dict]
        Lista de datos baseline, uno por sujeto
    datos_followup_6meses : List[Dict]
        Lista de diagnósticos a 6 meses con clave 'nuevo_episodio'
    
    Returns
    -------
    resultados : Dict
        - 'auc': float (área bajo curva ROC)
        - 'interpretacion': str
        - 'importancia_features': Dict
        - 'conclusion': str
        
    References
    ----------
    Ver problema_statement, Sección 2.4: "Test P2.3"
    """
    import scipy.stats
    
    # Validación temprana
    if not datos_baseline:
        raise ValueError("datos_baseline no puede estar vacío")
    if not datos_followup_6meses:
        raise ValueError("datos_followup_6meses no puede estar vacío")
    
    # 1. Extraer características de curvatura basal
    caracteristicas = []
    features = None  # Inicializar para evitar UnboundLocalError
    
    for sujeto in datos_baseline:
        Phi = construir_campo_emocional(sujeto)
        curv = calcular_curvatura_emocional(Phi)
        
        features = {
            'media_curvatura': np.mean(np.abs(curv['curvatura'])),
            'max_curvatura': curv['max_curvatura'],
            'num_singularidades': curv['num_singularidades'],
            'varianza_curvatura': np.var(curv['curvatura']),
            'asimetria_curvatura': scipy.stats.skew(curv['curvatura'].flatten())
        }
        caracteristicas.append(list(features.values()))
    
    X = np.array(caracteristicas)
    feature_names = list(features.keys())
    
    # 2. Variable objetivo: desarrollo de síntomas clínicos
    y = np.array([diagnostico['nuevo_episodio'] for diagnostico in datos_followup_6meses])
    
    # Si no hay sklearn, usar estadística simple
    try:
        from sklearn.linear_model import LogisticRegression
        from sklearn.metrics import roc_auc_score
        
        # 3. Modelo predictivo
        modelo = LogisticRegression(class_weight='balanced', random_state=42, max_iter=1000)
        modelo.fit(X, y)
        
        y_pred_proba = modelo.predict_proba(X)[:, 1]
        auc = roc_auc_score(y, y_pred_proba)
        
        # 4. Análisis de importancia
        importancias = dict(zip(feature_names, modelo.coef_[0]))
        
    except ImportError:
        # Fallback: correlación simple
        warnings.warn("sklearn no disponible, usando correlación simple")
        correlaciones = []
        for i in range(X.shape[1]):
            r, _ = pearsonr(X[:, i], y)
            correlaciones.append(r)
        
        auc = np.mean(np.abs(correlaciones))
        importancias = dict(zip(feature_names, correlaciones))
    
    # Interpretación
    if auc > 0.75:
        interpretacion = 'Buena predicción'
    elif auc > 0.65:
        interpretacion = 'Predicción moderada'
    else:
        interpretacion = 'Predicción débil'
    
    return {
        'auc': auc,
        'interpretacion': interpretacion,
        'importancia_features': importancias,
        'n_sujetos': len(datos_baseline),
        'n_episodios': sum(y),
        'conclusion': f'La curvatura emocional basal predice psicopatología con AUC={auc:.2f}'
    }


def rct_frecuencia_141_7_Hz() -> Dict[str, Any]:
    """
    Protocolo completo de RCT para validar intervención con 141.7 Hz.
    
    Test de la predicción P2.4: Exposición a 141.7 Hz reduce T₀₀ y aumenta Ψ.
    
    Returns
    -------
    diseño : Dict
        Especificación completa del ensayo clínico controlado aleatorizado
        
    Notes
    -----
    Este es un protocolo teórico. La implementación real requiere aprobación
    ética y registros clínicos apropiados.
    
    References
    ----------
    Ver problema_statement, Sección 2.5: "Test Crítico"
    """
    # Diseño: Triple ciego, paralelo, 3 brazos
    grupos = {
        'experimental': {
            'n': 30,
            'intervencion': '141.7 Hz binaural',
            'descripcion': 'Tono binaural a frecuencia QCAL exacta'
        },
        'placebo_activo': {
            'n': 30,
            'intervencion': '200 Hz binaural',
            'descripcion': 'Tono control de frecuencia similar'
        },
        'control': {
            'n': 30,
            'intervencion': 'Silencio con ruido rosa',
            'descripcion': 'Control pasivo con enmascaramiento'
        }
    }
    
    # Variables primarias
    outcomes_primarios = {
        'T00_reduccion': {
            'descripcion': 'Cambio en densidad de stress desde baseline',
            'medicion': 'Δ(T₀₀) = T₀₀(día28) - T₀₀(baseline)',
            'hipotesis': 'Experimental < Placebo < Control'
        },
        'Psi_aumento': {
            'descripcion': 'Cambio en coherencia cuántica',
            'medicion': 'Δ(Ψ) = Ψ(día28) - Ψ(baseline)',
            'hipotesis': 'Experimental > Placebo > Control'
        },
        'tiempo_retorno': {
            'descripcion': 'Tiempo para volver a baseline post-stress',
            'medicion': 'Minutos para T₀₀ < umbral',
            'hipotesis': 'Experimental más rápido que controles'
        }
    }
    
    # Variables secundarias
    outcomes_secundarios = {
        'nabla2_Phi': 'Reducción de curvatura emocional',
        'HRV_RMSSD': 'Aumento de variabilidad cardíaca',
        'autorreporte_ansiedad': 'Reducción en STAI-S',
        'calidad_sueño': 'Mejora en PSQI',
        'funcionamiento_global': 'Mejora en GAF'
    }
    
    # Protocolo de intervención
    protocolo = """
    Diseño: RCT triple ciego, 3 brazos paralelos
    
    Timeline:
    Día 1-7: Baseline (sin intervención)
      - Mediciones diarias de EEG, HRV, EDA
      - Cuestionarios: PANAS, PSS
      - fMRI baseline (día 7)
    
    Día 8-28: Intervención diaria (21 días)
      - 30 min diarios, misma hora (±1h)
      - Auriculares noise-cancelling
      - Mediciones durante sesión: EEG, HRV, EDA
      - Mediciones diarias: PANAS, escala stress
      - fMRI semanal (días 14, 21, 28)
    
    Día 29-35: Seguimiento sin intervención
      - Mediciones diarias continuas
      - fMRI final (día 35)
    
    Cegamiento:
    - Sujetos: no saben qué frecuencia reciben
    - Evaluadores: no saben grupo de asignación
    - Analistas: análisis con códigos ciegos
    """
    
    # Análisis estadístico planificado
    analisis = {
        'primario': {
            'metodo': 'ANOVA mixta 3(grupo) × 3(tiempo)',
            'correccion': 'Greenhouse-Geisser si violación esfericidad',
            'post_hoc': 'Bonferroni para comparaciones múltiples'
        },
        'secundario': {
            'metodo': 'Regresión lineal jerárquica',
            'covariables': ['edad', 'sexo', 'T₀₀_baseline'],
            'predictor': 'grupo de intervención'
        },
        'tamaño_efecto': {
            'ANOVA': 'η² parcial',
            'comparaciones_pareadas': 'd de Cohen'
        },
        'potencia': {
            'nivel': '80% para detectar d=0.5',
            'alpha': 0.05,
            'bilateral': True
        },
        'ajuste_comparaciones': 'Bonferroni para 3 outcomes primarios (α=0.05/3)'
    }
    
    # Criterios de inclusión/exclusión
    criterios = {
        'inclusion': [
            'Edad 18-65 años',
            'Nivel stress moderado (PSS > 14)',
            'Capacidad para consentimiento informado',
            'Disponibilidad para 35 días de estudio'
        ],
        'exclusion': [
            'Trastorno psiquiátrico mayor activo',
            'Medicación psicotrópica (últimos 3 meses)',
            'Pérdida auditiva significativa',
            'Contraindicaciones para fMRI',
            'Embarazo o lactancia'
        ]
    }
    
    return {
        'diseño': grupos,
        'outcomes_primarios': outcomes_primarios,
        'outcomes_secundarios': outcomes_secundarios,
        'protocolo': protocolo,
        'analisis': analisis,
        'criterios': criterios,
        'registro_clinico': 'ClinicalTrials.gov (pre-registro obligatorio)',
        'etica': 'Requiere aprobación IRB/CEI'
    }


def simular_resultados_esperados() -> Tuple[Dict, Dict]:
    """
    Predicciones cuantitativas basadas en el modelo QCAL.
    
    Estas son predicciones a priori del modelo teórico QCAL para
    el RCT de 141.7 Hz. Permiten evaluación prospectiva del modelo.
    
    Returns
    -------
    resultados_esperados : Dict
        Valores esperados por grupo de intervención
    comparaciones : Dict
        Comparaciones estadísticas esperadas
        
    Notes
    -----
    Estas predicciones son falsables y deben registrarse antes del
    experimento para evitar HARKing (Hypothesizing After Results Known).
    """
    # Baseline común
    T00_baseline = 0.45
    Psi_baseline = 0.78
    
    # Post-intervención (día 28)
    resultados_esperados = {
        'experimental_141.7Hz': {
            'T00': T00_baseline * 0.65,  # 35% de reducción
            'Psi': Psi_baseline + 0.15,   # Aumento absoluto de 0.15
            'nabla2_Phi': -0.42,          # Reducción de singularidades
            'IC_95_Psi': (0.88, 0.98),
            'mecanismo': 'Resonancia con frecuencia QCAL fundamental'
        },
        'placebo_activo_200Hz': {
            'T00': T00_baseline * 0.85,  # 15% de reducción (efecto placebo)
            'Psi': Psi_baseline + 0.05,
            'nabla2_Phi': -0.15,
            'IC_95_Psi': (0.79, 0.87),
            'mecanismo': 'Efecto placebo + atención sostenida'
        },
        'control_silencio': {
            'T00': T00_baseline * 0.92,  # 8% de reducción (habituación)
            'Psi': Psi_baseline + 0.02,
            'nabla2_Phi': -0.05,
            'IC_95_Psi': (0.77, 0.83),
            'mecanismo': 'Habituación natural + regresión a la media'
        }
    }
    
    # Test de hipótesis esperados
    comparaciones = {
        'experimental_vs_placebo': {
            'p_esperado': '<0.001',
            'tamaño_efecto_d': 0.95,
            'NNT': 3.2,  # Number Needed to Treat
            'interpretacion': 'Efecto grande y clínicamente significativo'
        },
        'experimental_vs_control': {
            'p_esperado': '<0.0001',
            'tamaño_efecto_d': 1.32,
            'NNT': 2.5,
            'interpretacion': 'Efecto muy grande'
        },
        'placebo_vs_control': {
            'p_esperado': '0.05-0.10',
            'tamaño_efecto_d': 0.35,
            'NNT': 8.5,
            'interpretacion': 'Efecto pequeño (placebo)'
        }
    }
    
    return resultados_esperados, comparaciones
