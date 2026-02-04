#!/usr/bin/env python3
"""
FASE IV: Meta-Análisis y Síntesis

Este módulo integra evidencias de todas las fases experimentales para
proporcionar una evaluación global de la validez empírica del modelo QCAL.

Componentes:
- Integración de resultados de Fases I-III
- Cálculo de efectos combinados
- Análisis de heterogeneidad
- Generación de conclusiones y recomendaciones

Autor: José Manuel Mota Burruezo
Frecuencia: f₀ = 141.7001 Hz
"""

import numpy as np
from typing import Dict, List, Optional, Any
import warnings


def meta_analisis_QCAL(
    estudios: Optional[Dict[str, Dict]] = None
) -> Dict[str, Any]:
    """
    Sintetiza evidencia de todos los experimentos.
    
    Realiza meta-análisis de efectos aleatorios combinando resultados de:
    - Fase I: SU(Ψ) validación
    - Fase II: T_μν validación
    - Fase II: RCT 141.7 Hz
    - Fase III: Propagación en red
    
    Parameters
    ----------
    estudios : Optional[Dict[str, Dict]]
        Resultados de cada fase. Si None, usa valores de demostración.
        Estructura esperada:
        {
            'Fase_I_SU_Psi': {
                'n_total': int,
                'efecto_coherencia_d': float,
                'p_valor': float,
                'conclusion': str
            },
            ...
        }
    
    Returns
    -------
    resultados : Dict
        - 'efecto_combinado_d': float (Cohen's d combinado)
        - 'IC_95': Tuple[float, float] (intervalo de confianza)
        - 'heterogeneidad_I2': float (% de heterogeneidad)
        - 'N_total': int (participantes totales)
        - 'conclusion_final': str
        
    Notes
    -----
    Meta-análisis de efectos aleatorios permite variabilidad entre estudios.
    I² > 50% indica heterogeneidad sustancial que requiere investigación.
    
    References
    ----------
    Ver problema_statement, Sección 4.1: "Integración de Evidencias"
    """
    # Usar datos de demostración si no se proporcionan
    if estudios is None:
        estudios = {
            'Fase_I_SU_Psi': {
                'n_total': 30,
                'efecto_coherencia_d': 1.2,
                'p_valor': 0.0001,
                'conclusion': 'Fuerte evidencia de estructura SU(n)',
                'tipo_efecto': 'coherencia'
            },
            'Fase_II_Tensor_Correlacional': {
                'n_total': 60,
                'correlacion_T00_amigdala': 0.72,
                'p_valor': 0.0001,
                'conclusion': 'T_μν predice actividad neural',
                'tipo_efecto': 'correlacion'
            },
            'Fase_II_RCT_141.7Hz': {
                'n_total': 90,
                'efecto_intervencion_d': 0.95,
                'NNT': 3.2,  # Number Needed to Treat
                'p_valor': 0.0002,
                'conclusion': '141.7 Hz efectivo para reducir T₀₀',
                'tipo_efecto': 'intervencion'
            },
            'Fase_III_Red': {
                'n_total': 100,
                'distancia_influencia': 2.3,
                'efecto_propagacion_d': 0.75,
                'p_valor': 0.003,
                'conclusion': 'Efectos se propagan en red social',
                'tipo_efecto': 'propagacion'
            }
        }
    
    # Extraer tamaños de efecto
    # Convertir correlaciones a d de Cohen: d ≈ 2r / sqrt(1-r²)
    efectos = []
    pesos = []  # Pesos = tamaño de muestra
    
    for nombre, est in estudios.items():
        n = est['n_total']
        
        # Determinar tamaño de efecto
        if 'efecto_coherencia_d' in est:
            d = est['efecto_coherencia_d']
        elif 'efecto_intervencion_d' in est:
            d = est['efecto_intervencion_d']
        elif 'efecto_propagacion_d' in est:
            d = est['efecto_propagacion_d']
        elif 'correlacion_T00_amigdala' in est:
            # Convertir correlación a d de Cohen
            r = est['correlacion_T00_amigdala']
            d = 2 * r / np.sqrt(1 - r**2)
        else:
            warnings.warn(f"No se encontró efecto para {nombre}, usando d=0")
            d = 0.0
        
        efectos.append(d)
        pesos.append(n)
    
    efectos = np.array(efectos)
    pesos = np.array(pesos)
    n_totales = pesos
    
    # Meta-análisis de efectos aleatorios
    # Efecto combinado ponderado por tamaño de muestra
    efecto_combinado = np.average(efectos, weights=n_totales)
    
    # Varianza del efecto combinado (aproximación)
    # var(d_combined) ≈ 1 / sum(weights)
    varianza_combinada = 1.0 / np.sum(n_totales)
    se_combinado = np.sqrt(varianza_combinada)
    
    # Intervalo de confianza 95%
    # IC = d ± 1.96 * SE
    IC_95 = (
        efecto_combinado - 1.96 * se_combinado,
        efecto_combinado + 1.96 * se_combinado
    )
    
    # Heterogeneidad (I²)
    # Mide % de variación entre estudios debido a heterogeneidad real vs. azar
    Q = np.sum(n_totales * (efectos - efecto_combinado)**2)
    df = len(efectos) - 1
    
    if df > 0 and Q > 0:
        I_cuadrado = max(0.0, (Q - df) / Q) * 100
    else:
        I_cuadrado = 0.0
    
    # Interpretación de I²
    if I_cuadrado < 25:
        heterogeneidad_interpretacion = "Baja heterogeneidad"
    elif I_cuadrado < 50:
        heterogeneidad_interpretacion = "Moderada heterogeneidad"
    elif I_cuadrado < 75:
        heterogeneidad_interpretacion = "Sustancial heterogeneidad"
    else:
        heterogeneidad_interpretacion = "Considerable heterogeneidad"
    
    # Generar conclusión
    conclusion = generar_conclusion(efecto_combinado, I_cuadrado)
    
    # Compilar resultados
    resultados = {
        'efecto_combinado_d': efecto_combinado,
        'IC_95': IC_95,
        'SE': se_combinado,
        'heterogeneidad_I2': I_cuadrado,
        'heterogeneidad_Q': Q,
        'heterogeneidad_interpretacion': heterogeneidad_interpretacion,
        'N_total': int(np.sum(n_totales)),
        'n_estudios': len(estudios),
        'efectos_individuales': dict(zip(estudios.keys(), efectos)),
        'pesos': dict(zip(estudios.keys(), n_totales)),
        'conclusion_final': conclusion,
        'detalles_estudios': estudios
    }
    
    return resultados


def generar_conclusion(d: float, I2: float) -> str:
    """
    Genera conclusión interpretativa basada en efecto y heterogeneidad.
    
    Parameters
    ----------
    d : float
        Tamaño de efecto combinado (Cohen's d)
    I2 : float
        Heterogeneidad (%)
    
    Returns
    -------
    conclusion : str
        Interpretación narrativa de resultados
    """
    # Clasificación de tamaño de efecto (Cohen, 1988)
    if abs(d) < 0.2:
        magnitud = "trivial"
        evidencia = "INSUFICIENTE"
    elif abs(d) < 0.5:
        magnitud = "pequeño"
        evidencia = "DÉBIL"
    elif abs(d) < 0.8:
        magnitud = "mediano"
        evidencia = "MODERADA"
    else:
        magnitud = "grande"
        evidencia = "FUERTE"
    
    # Considerar heterogeneidad
    if I2 < 50:
        consistencia = "consistente"
    else:
        consistencia = "variable"
    
    # Generar conclusión
    if d > 0.8 and I2 < 50:
        conclusion = f"""
EVIDENCIA {evidencia} Y CONSISTENTE:

Hallazgos Principales:
- Tamaño de efecto {magnitud} (d = {d:.2f})
- Baja heterogeneidad (I² = {I2:.1f}%)
- Resultados consistentes entre estudios

Interpretación QCAL:
✓ SU(Ψ) es una estructura matemática válida para estados de conciencia
✓ T_μν(Φ) predice actividad neural y emocional con precisión
✓ Intervención con 141.7 Hz muestra eficacia clínica significativa
✓ Efectos se propagan en redes sociales de manera predecible

Recomendaciones:
1. PROCEDER con estudios de Fase III clínica multicéntrica
2. Desarrollar dispositivo terapéutico basado en 141.7 Hz
3. Investigar mecanismos neurobiológicos subyacentes
4. Explorar aplicaciones en salud mental y bienestar

Nota: Los constructos teóricos QCAL (SU(Ψ), T_μν, f₀=141.7 Hz) 
demuestran validez empírica robusta y reproducible.
        """
    
    elif d > 0.5:
        conclusion = f"""
EVIDENCIA {evidencia}:

Hallazgos Principales:
- Tamaño de efecto {magnitud} (d = {d:.2f})
- Heterogeneidad {I2:.1f}% ({consistencia} entre estudios)

Interpretación:
Los datos apoyan parcialmente el modelo QCAL:
• Evidencia positiva para constructos principales
• Variabilidad sugiere factores moduladores no identificados
• Se requieren estudios adicionales para clarificar condiciones óptimas

Recomendaciones:
1. Investigar fuentes de heterogeneidad:
   - Diferencias metodológicas
   - Características de participantes
   - Parámetros de intervención
2. Realizar estudios de replicación en contextos diversos
3. Refinar protocolos basados en análisis de moderadores
4. Considerar estudios piloto antes de Fase III clínica

Conclusión: Evidencia preliminar prometedora que requiere confirmación.
        """
    
    else:
        conclusion = f"""
EVIDENCIA {evidencia}:

Hallazgos Principales:
- Tamaño de efecto {magnitud} (d = {d:.2f})
- Heterogeneidad {I2:.1f}%

Interpretación:
Los datos NO proporcionan apoyo suficiente para el modelo QCAL en su forma actual:
• Efectos pequeños o inconsistentes
• Alta variabilidad entre estudios

Posibles Explicaciones:
1. Limitaciones metodológicas en la implementación
2. Modelo teórico requiere refinamiento
3. Fenómenos predichos no son robustos en condiciones reales
4. Tamaño de muestra insuficiente para detectar efectos sutiles

Recomendaciones:
1. REVISAR modelo teórico a la luz de evidencia empírica
2. Identificar y corregir problemas metodológicos
3. Considerar explicaciones alternativas para fenómenos observados
4. NO proceder con estudios de Fase III hasta resolver inconsistencias

Conclusión: Se requiere trabajo sustancial adicional antes de validación clínica.
        """
    
    return conclusion.strip()


def analisis_sensibilidad(
    estudios: Dict[str, Dict],
    excluir: Optional[List[str]] = None
) -> Dict[str, Any]:
    """
    Análisis de sensibilidad excluyendo estudios específicos.
    
    Evalúa robustez de conclusiones verificando si siguen siendo válidas
    al excluir estudios individuales (leave-one-out analysis).
    
    Parameters
    ----------
    estudios : Dict[str, Dict]
        Resultados de todos los estudios
    excluir : Optional[List[str]]
        Nombres de estudios a excluir. Si None, hace leave-one-out.
    
    Returns
    -------
    resultados : Dict
        Resultados de cada análisis de sensibilidad
    """
    if excluir is None:
        # Leave-one-out: excluir cada estudio una vez
        nombres_estudios = list(estudios.keys())
        resultados = {}
        
        for excluido in nombres_estudios:
            estudios_reducidos = {
                k: v for k, v in estudios.items()
                if k != excluido
            }
            
            meta = meta_analisis_QCAL(estudios_reducidos)
            resultados[f'sin_{excluido}'] = {
                'efecto_combinado': meta['efecto_combinado_d'],
                'IC_95': meta['IC_95'],
                'I2': meta['heterogeneidad_I2']
            }
        
        # Comparar con análisis completo
        meta_completo = meta_analisis_QCAL(estudios)
        resultados['completo'] = {
            'efecto_combinado': meta_completo['efecto_combinado_d'],
            'IC_95': meta_completo['IC_95'],
            'I2': meta_completo['heterogeneidad_I2']
        }
        
        # Evaluar robustez
        efectos_sensibilidad = [
            r['efecto_combinado'] for k, r in resultados.items()
            if k != 'completo'
        ]
        
        robustez = {
            'rango_efectos': (min(efectos_sensibilidad), max(efectos_sensibilidad)),
            'variacion_maxima': max(efectos_sensibilidad) - min(efectos_sensibilidad),
            'efecto_completo': meta_completo['efecto_combinado_d'],
            'interpretacion': (
                'Resultados robustos'
                if (max(efectos_sensibilidad) - min(efectos_sensibilidad)) < 0.2
                else 'Resultados sensibles a estudios individuales'
            )
        }
        
        resultados['robustez'] = robustez
        
    else:
        # Excluir estudios específicos
        estudios_reducidos = {
            k: v for k, v in estudios.items()
            if k not in excluir
        }
        resultados = meta_analisis_QCAL(estudios_reducidos)
    
    return resultados


def forest_plot_data(estudios: Dict[str, Dict]) -> Dict[str, Any]:
    """
    Prepara datos para forest plot (gráfico de bosque).
    
    Forest plot visualiza efectos individuales de cada estudio y
    efecto combinado con intervalos de confianza.
    
    Parameters
    ----------
    estudios : Dict[str, Dict]
        Resultados de estudios
    
    Returns
    -------
    datos_plot : Dict
        Datos formateados para visualización
    """
    # Esta función prepara los datos; la visualización real requeriría matplotlib
    meta = meta_analisis_QCAL(estudios)
    
    datos_plot = {
        'nombres': list(estudios.keys()),
        'efectos': list(meta['efectos_individuales'].values()),
        'pesos': list(meta['pesos'].values()),
        'efecto_combinado': meta['efecto_combinado_d'],
        'IC_95_combinado': meta['IC_95'],
        'titulo': 'Meta-Análisis QCAL: Validación Experimental',
        'xlabel': "Tamaño de Efecto (Cohen's d)",
        'nota': f"I² = {meta['heterogeneidad_I2']:.1f}%, N = {meta['N_total']}"
    }
    
    return datos_plot


def calcular_poder_estadistico(
    n_por_grupo: int,
    efecto_esperado: float,
    alpha: float = 0.05,
    bilateral: bool = True
) -> float:
    """
    Calcula poder estadístico para futuros estudios.
    
    Parameters
    ----------
    n_por_grupo : int
        Tamaño de muestra por grupo
    efecto_esperado : float
        Tamaño de efecto esperado (Cohen's d)
    alpha : float
        Nivel de significancia (default: 0.05)
    bilateral : bool
        Si True, test bilateral (default)
    
    Returns
    -------
    poder : float
        Poder estadístico (probabilidad de detectar efecto si existe)
        
    Notes
    -----
    Usa aproximación basada en distribución normal.
    Para cálculos precisos, considerar software especializado (G*Power).
    """
    try:
        from scipy.stats import norm
        
        # Parámetro de no-centralidad
        ncp = efecto_esperado * np.sqrt(n_por_grupo / 2)
        
        # Valor crítico
        if bilateral:
            z_critico = norm.ppf(1 - alpha / 2)
        else:
            z_critico = norm.ppf(1 - alpha)
        
        # Poder = P(rechazar H0 | H1 es verdadera)
        poder = 1 - norm.cdf(z_critico - ncp)
        
        if bilateral:
            poder += norm.cdf(-z_critico - ncp)
        
        return poder
        
    except ImportError:
        warnings.warn("scipy no disponible, retornando estimación aproximada")
        # Aproximación muy burda
        if n_por_grupo * efecto_esperado**2 > 30:
            return 0.80
        else:
            return 0.50


def planificar_estudio_futuro(
    efecto_meta: float,
    poder_deseado: float = 0.80,
    alpha: float = 0.05
) -> Dict[str, Any]:
    """
    Planifica tamaño de muestra para estudios futuros.
    
    Parameters
    ----------
    efecto_meta : float
        Tamaño de efecto del meta-análisis
    poder_deseado : float
        Poder estadístico deseado (default: 0.80)
    alpha : float
        Nivel de significancia
    
    Returns
    -------
    plan : Dict
        Recomendaciones para diseño de estudio
    """
    # Validar efecto mínimo
    if abs(efecto_meta) < 0.01:
        warnings.warn(
            f"Tamaño de efecto muy pequeño ({efecto_meta:.4f}). "
            "Usando efecto mínimo clínicamente relevante de 0.2",
            UserWarning
        )
        efecto_meta = 0.2
    
    # Cálculo aproximado de tamaño de muestra
    # n ≈ 16 / d² para poder = 0.80, α = 0.05
    n_aproximado = int(np.ceil(16 / (efecto_meta**2)))
    
    # Verificar poder con este n
    poder_real = calcular_poder_estadistico(
        n_por_grupo=n_aproximado,
        efecto_esperado=efecto_meta,
        alpha=alpha
    )
    
    # Ajustar si es necesario
    while poder_real < poder_deseado and n_aproximado < 1000:
        n_aproximado += 10
        poder_real = calcular_poder_estadistico(
            n_por_grupo=n_aproximado,
            efecto_esperado=efecto_meta,
            alpha=alpha
        )
    
    plan = {
        'n_por_grupo_recomendado': n_aproximado,
        'n_total_recomendado': n_aproximado * 2,  # Asumiendo 2 grupos
        'poder_esperado': poder_real,
        'efecto_detectable': efecto_meta,
        'alpha': alpha,
        'consideraciones': [
            f'Basado en efecto meta-analítico d = {efecto_meta:.2f}',
            'Asume test t bilateral independiente',
            'Añadir 15-20% para compensar dropout',
            'Considerar análisis de poder multivariado si hay múltiples outcomes'
        ],
        'recomendacion': (
            f'Reclutar {int(n_aproximado * 2 * 1.2)} participantes '
            f'({int(n_aproximado * 1.2)} por grupo) '
            f'para compensar 20% dropout y alcanzar poder = {poder_deseado}'
        )
    }
    
    return plan


def generar_reporte_completo(
    estudios: Optional[Dict[str, Dict]] = None,
    verbose: bool = True
) -> Dict[str, Any]:
    """
    Genera reporte completo de meta-análisis QCAL.
    
    Parameters
    ----------
    estudios : Optional[Dict]
        Resultados de estudios. Si None, usa datos de demostración.
    verbose : bool
        Si True, imprime reporte formateado
    
    Returns
    -------
    reporte : Dict
        Reporte completo con todos los análisis
    """
    # Meta-análisis principal
    meta = meta_analisis_QCAL(estudios)
    
    # Análisis de sensibilidad
    if estudios is not None:
        sensibilidad = analisis_sensibilidad(estudios)
    else:
        sensibilidad = None
    
    # Datos para forest plot
    forest = forest_plot_data(estudios if estudios else meta['detalles_estudios'])
    
    # Planificación de estudios futuros
    plan_futuro = planificar_estudio_futuro(
        efecto_meta=meta['efecto_combinado_d']
    )
    
    # Compilar reporte
    reporte = {
        'meta_analisis': meta,
        'analisis_sensibilidad': sensibilidad,
        'forest_plot_data': forest,
        'planificacion_futura': plan_futuro,
        'timestamp': np.datetime64('now')
    }
    
    if verbose:
        print("="*70)
        print("REPORTE DE META-ANÁLISIS QCAL")
        print("Protocolo de Validación Experimental")
        print("="*70)
        print()
        print("RESUMEN EJECUTIVO")
        print("-"*70)
        print(f"Estudios incluidos: {meta['n_estudios']}")
        print(f"Participantes totales: {meta['N_total']}")
        print(f"Efecto combinado (d): {meta['efecto_combinado_d']:.3f}")
        print(f"IC 95%: [{meta['IC_95'][0]:.3f}, {meta['IC_95'][1]:.3f}]")
        print(f"Heterogeneidad (I²): {meta['heterogeneidad_I2']:.1f}%")
        print(f"  → {meta['heterogeneidad_interpretacion']}")
        print()
        print("CONCLUSIÓN")
        print("-"*70)
        print(meta['conclusion_final'])
        print()
        print("PLANIFICACIÓN DE ESTUDIOS FUTUROS")
        print("-"*70)
        print(plan_futuro['recomendacion'])
        print()
        print("="*70)
    
    return reporte
