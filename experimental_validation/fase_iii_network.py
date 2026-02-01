#!/usr/bin/env python3
"""
FASE III: Validación a Nivel Colectivo - Propagación en Red Social

Este módulo implementa experimentos de red social para validar que los efectos
de coherencia QCAL se propagan a través de redes sociales, demostrando que
T_μν(Φ) tiene efectos no-locales a nivel colectivo.

Hipótesis Principal:
    H₃: Los efectos de la intervención con 141.7 Hz se propagan a través de
    redes sociales siguiendo dinámicas de acoplamiento del tensor T_μν.

Predicciones Falsables:
    P3.1: Individuos conectados muestran correlación en T₀₀
    P3.2: La propagación sigue un patrón de decaimiento exponencial
    P3.3: Topología small-world facilita propagación global
    P3.4: Efectos persisten 2-3 saltos desde nodo intervenido

Autor: José Manuel Mota Burruezo
Frecuencia: f₀ = 141.7001 Hz
"""

import numpy as np
from typing import Dict, List, Tuple, Optional
import warnings


def experimento_red_social(
    n_participantes: int = 100,
    n_intervenidos: int = 20,
    k_vecinos: int = 6,
    p_rewire: float = 0.1,
    seed: int = 42
) -> Tuple[object, str, callable]:
    """
    Diseña experimento de propagación en red social.
    
    Crea una red social artificial con topología small-world y asigna
    aleatoriamente nodos a grupo experimental vs. control.
    
    Parameters
    ----------
    n_participantes : int, optional
        Número total de participantes (default: 100)
    n_intervenidos : int, optional
        Número de nodos que reciben intervención 141.7 Hz (default: 20)
    k_vecinos : int, optional
        Número de vecinos en red regular inicial (default: 6)
    p_rewire : float, optional
        Probabilidad de re-cableado Watts-Strogatz (default: 0.1)
    seed : int, optional
        Semilla aleatoria para reproducibilidad
    
    Returns
    -------
    G : networkx.Graph
        Red social con atributos de nodo inicializados
    protocolo : str
        Descripción del protocolo experimental
    simular_propagacion : callable
        Función para simular dinámica temporal
        
    Notes
    -----
    La topología small-world combina:
    - Alto clustering local (comunidades cohesionadas)
    - Caminos cortos globales (conexiones de largo alcance)
    
    Esto modela redes sociales reales mejor que redes aleatorias o regulares.
    
    References
    ----------
    Ver problema_statement, Sección 3.1: "Protocolo C"
    """
    try:
        import networkx as nx
    except ImportError:
        raise ImportError(
            "NetworkX requerido para experimentos de red. "
            "Instalar con: pip install networkx"
        )
    
    np.random.seed(seed)
    
    # 1. Construcción de red small-world (Watts-Strogatz)
    G = nx.watts_strogatz_graph(
        n=n_participantes,
        k=k_vecinos,
        p=p_rewire,
        seed=seed
    )
    
    # 2. Asignación aleatoria de intervención
    nodos = list(G.nodes())
    nodos_intervencion = np.random.choice(
        nodos,
        size=n_intervenidos,
        replace=False
    )
    
    # 3. Inicializar atributos de nodo
    for nodo in G.nodes():
        # Grupo experimental vs. control
        G.nodes[nodo]['grupo'] = (
            'experimental' if nodo in nodos_intervencion else 'control'
        )
        
        # Estado inicial aleatorio (T₀₀ y Ψ baseline)
        G.nodes[nodo]['T00'] = np.random.uniform(0.3, 0.6)
        G.nodes[nodo]['Psi'] = np.random.uniform(0.7, 0.9)
        
        # Historial temporal (para análisis)
        G.nodes[nodo]['historia_T00'] = [G.nodes[nodo]['T00']]
        G.nodes[nodo]['historia_Psi'] = [G.nodes[nodo]['Psi']]
    
    # 4. Protocolo de interacción
    protocolo = f"""
    Diseño de Experimento de Red Social QCAL
    
    Red: Small-world (Watts-Strogatz)
    - N = {n_participantes} participantes
    - k = {k_vecinos} vecinos promedio
    - p = {p_rewire} probabilidad de re-cableado
    - Topología: alto clustering + caminos cortos
    
    Grupos:
    - Experimental: {n_intervenidos} nodos ({100*n_intervenidos/n_participantes:.1f}%)
      → Intervención: 141.7 Hz diario + sesiones grupales semanales
    - Control: {n_participantes - n_intervenidos} nodos ({100*(1-n_intervenidos/n_participantes):.1f}%)
      → Actividades placebo equivalentes
    
    Timeline:
    Semana 1-2: Calibración individual (todos)
      - Mediciones baseline: T₀₀, Ψ, cuestionarios
      - Mapeo de red social (interacciones diarias)
    
    Semana 3-10: Intervención (8 semanas)
      - Grupo experimental: 141.7 Hz diario (30 min) + sesión grupal semanal
      - Grupo control: Audio placebo + sesión grupal semanal
      - Mediciones continuas en cada interacción social
    
    Semana 11-12: Seguimiento sin intervención
      - Mediciones continuas
      - Análisis de persistencia de efectos
    
    Mediciones:
    - Cada interacción social: Φ pre/post (via smartphone app)
    - Semanal: T_μν completo (laboratorio), Ψ coherencia
    - Final: Topología de red (cambios en conexiones sociales)
    
    Hipótesis:
    1. T₀₀ de nodos experimentales ↓ más que controles
    2. Efectos se propagan a vecinos (1-2 saltos)
    3. Decaimiento exponencial: efecto ∝ exp(-λ·distancia)
    4. Red se auto-organiza: más conexiones hacia nodos de alta Ψ
    """
    
    # 5. Función de simulación de propagación
    def simular_propagacion(
        G_input: object,
        num_pasos: int = 100,
        factor_acoplamiento: float = 0.2,
        factor_disipacion: float = 0.9,
        factor_intervencion: float = 0.95
    ) -> List[Dict]:
        """
        Simula dinámica temporal de propagación en red.
        
        Parameters
        ----------
        G_input : networkx.Graph
            Red social con estado inicial
        num_pasos : int
            Número de pasos temporales a simular
        factor_acoplamiento : float
            Fuerza de influencia entre vecinos [0, 1]
        factor_disipacion : float
            Tasa de disipación natural [0, 1]
        factor_intervencion : float
            Efecto de la intervención 141.7 Hz
        
        Returns
        -------
        historia : List[Dict]
            Estado de todos los nodos en cada paso temporal
        """
        historia = []
        
        for paso in range(num_pasos):
            # Guardar estado actual
            estado_actual = {
                n: {
                    'T00': G_input.nodes[n]['T00'],
                    'Psi': G_input.nodes[n]['Psi'],
                    'grupo': G_input.nodes[n]['grupo']
                }
                for n in G_input.nodes()
            }
            historia.append(estado_actual)
            
            # Actualizar cada nodo basado en vecinos
            nuevos_valores_T00 = {}
            nuevos_valores_Psi = {}
            
            for nodo in G_input.nodes():
                vecinos = list(G_input.neighbors(nodo))
                
                if not vecinos:
                    # Nodo aislado (no debería ocurrir en small-world conectado)
                    nuevos_valores_T00[nodo] = G_input.nodes[nodo]['T00'] * factor_disipacion
                    nuevos_valores_Psi[nodo] = G_input.nodes[nodo]['Psi']
                    continue
                
                # Influencia de vecinos (acoplamiento T_μν)
                T00_vecinos = [G_input.nodes[v]['T00'] for v in vecinos]
                influencia = np.mean(T00_vecinos) * factor_acoplamiento
                
                # Actualización con disipación
                T00_actual = G_input.nodes[nodo]['T00']
                T00_nuevo = T00_actual * factor_disipacion + influencia
                
                # Intervención si es nodo experimental
                if G_input.nodes[nodo]['grupo'] == 'experimental':
                    T00_nuevo *= factor_intervencion  # Efecto de 141.7 Hz
                
                # Evitar valores negativos o explosivos
                T00_nuevo = np.clip(T00_nuevo, 0.0, 1.0)
                nuevos_valores_T00[nodo] = T00_nuevo
                
                # Actualizar coherencia (relación inversa con stress)
                # Ψ = 1 / (1 + T₀₀)
                Psi_nuevo = 1.0 / (1.0 + T00_nuevo)
                nuevos_valores_Psi[nodo] = Psi_nuevo
            
            # Aplicar actualizaciones (evitar race conditions)
            for nodo in G_input.nodes():
                G_input.nodes[nodo]['T00'] = nuevos_valores_T00[nodo]
                G_input.nodes[nodo]['Psi'] = nuevos_valores_Psi[nodo]
                
                # Guardar en historial
                G_input.nodes[nodo]['historia_T00'].append(nuevos_valores_T00[nodo])
                G_input.nodes[nodo]['historia_Psi'].append(nuevos_valores_Psi[nodo])
        
        return historia
    
    return G, protocolo, simular_propagacion


def analizar_efectos_red(
    historia: List[Dict],
    red: object
) -> Dict[str, any]:
    """
    Extrae métricas de propagación en red.
    
    Analiza cómo los efectos de la intervención se propagan desde nodos
    experimentales hacia el resto de la red a través de conexiones sociales.
    
    Parameters
    ----------
    historia : List[Dict]
        Historia temporal de estados de todos los nodos
    red : networkx.Graph
        Red social (para cálculo de distancias)
    
    Returns
    -------
    resultados : Dict
        - 'T00_reduccion_experimental': float
        - 'T00_reduccion_control': float
        - 'distancia_influencia_caracteristica': float
        - 'decay_lambda': float
        - 'interpretacion': str
        
    References
    ----------
    Ver problema_statement, Sección 3.1: "Análisis de resultados"
    """
    try:
        import networkx as nx
    except ImportError:
        raise ImportError("NetworkX requerido para análisis de red")
    
    from scipy.optimize import curve_fit
    
    # 1. Identificar nodos por grupo
    nodos_exp = [
        n for n in red.nodes()
        if red.nodes[n]['grupo'] == 'experimental'
    ]
    nodos_control = [
        n for n in red.nodes()
        if red.nodes[n]['grupo'] == 'control'
    ]
    
    # 2. Evolución temporal por grupo
    T00_exp_tiempo = [
        [historia[t][n]['T00'] for n in nodos_exp]
        for t in range(len(historia))
    ]
    T00_ctrl_tiempo = [
        [historia[t][n]['T00'] for n in nodos_control]
        for t in range(len(historia))
    ]
    
    # Reducción relativa (baseline → final)
    T00_reduccion_exp = (
        np.mean(T00_exp_tiempo[0]) / (np.mean(T00_exp_tiempo[-1]) + 1e-10)
    )
    T00_reduccion_ctrl = (
        np.mean(T00_ctrl_tiempo[0]) / (np.mean(T00_ctrl_tiempo[-1]) + 1e-10)
    )
    
    # 3. Distancia de influencia
    # Medir cómo el efecto decae con distancia en la red
    distancias_influencia = []
    
    for nodo_exp in nodos_exp:
        for nodo in red.nodes():
            if nodo != nodo_exp:
                try:
                    distancia = nx.shortest_path_length(red, nodo_exp, nodo)
                except nx.NetworkXNoPath:
                    continue  # Nodos no conectados (no debería ocurrir)
                
                # Calcular reducción de T₀₀ en este nodo
                T00_inicial = historia[0][nodo]['T00']
                T00_final = historia[-1][nodo]['T00']
                reduccion = (T00_inicial - T00_final) / (T00_inicial + 1e-10)
                
                distancias_influencia.append((distancia, reduccion))
    
    # 4. Modelo de decaimiento exponencial
    if distancias_influencia:
        distancias, reducciones = zip(*distancias_influencia)
        distancias = np.array(distancias, dtype=float)
        reducciones = np.array(reducciones, dtype=float)
        
        # Modelo: reducción(d) = A * exp(-λ * d)
        def modelo_decaimiento(d, A, lambda_):
            return A * np.exp(-lambda_ * d)
        
        try:
            # Ajustar modelo
            params, _ = curve_fit(
                modelo_decaimiento,
                distancias,
                reducciones,
                p0=[0.3, 0.5],  # Initial guess
                bounds=([0, 0], [1, 5]),  # Reasonable bounds
                maxfev=10000
            )
            A_opt, lambda_critico = params
            
            # Distancia característica: donde el efecto cae a 1/e
            distancia_caracteristica = 1.0 / lambda_critico
            
        except (RuntimeError, ValueError):
            # Si el ajuste falla, usar estimación simple
            warnings.warn("Ajuste exponencial falló, usando estimación simple")
            lambda_critico = 0.5
            distancia_caracteristica = 2.0
            A_opt = np.mean(reducciones)
    else:
        lambda_critico = 0.0
        distancia_caracteristica = np.inf
        A_opt = 0.0
    
    # 5. Análisis de persistencia
    # ¿Cuánto tiempo persisten los efectos después del cese de intervención?
    # (Esto requeriría simular fase de seguimiento)
    
    # 6. Cambios topológicos
    # En experimento real: medir si se forman nuevas conexiones
    # hacia nodos de alta coherencia
    
    resultados = {
        'T00_reduccion_experimental': T00_reduccion_exp,
        'T00_reduccion_control': T00_reduccion_ctrl,
        'ratio_efecto': T00_reduccion_exp / (T00_reduccion_ctrl + 1e-10),
        'lambda_decay': lambda_critico,
        'distancia_influencia_caracteristica': distancia_caracteristica,
        'amplitud_inicial': A_opt,
        'n_experimental': len(nodos_exp),
        'n_control': len(nodos_control),
        'n_pasos_simulados': len(historia),
        'interpretacion': (
            f'Efecto se propaga hasta {distancia_caracteristica:.1f} saltos en red. '
            f'Reducción experimental {T00_reduccion_exp:.2f}x vs '
            f'control {T00_reduccion_ctrl:.2f}x'
        )
    }
    
    return resultados


def analizar_clustering_coherencia(
    red: object,
    historia: List[Dict]
) -> Dict[str, any]:
    """
    Analiza si nodos de alta coherencia forman clusters.
    
    Verifica la hipótesis de auto-organización: la red evoluciona para
    maximizar conexiones entre nodos de alta coherencia.
    
    Parameters
    ----------
    red : networkx.Graph
        Red social
    historia : List[Dict]
        Historia temporal de estados
    
    Returns
    -------
    resultados : Dict
        Análisis de clustering por nivel de coherencia
    """
    try:
        import networkx as nx
    except ImportError:
        raise ImportError("NetworkX requerido")
    
    # Estado final
    estado_final = historia[-1]
    
    # Clasificar nodos por nivel de coherencia
    Psi_valores = [estado_final[n]['Psi'] for n in red.nodes()]
    umbral_alta_coherencia = np.percentile(Psi_valores, 75)
    
    nodos_alta_Psi = [
        n for n in red.nodes()
        if estado_final[n]['Psi'] >= umbral_alta_coherencia
    ]
    nodos_baja_Psi = [
        n for n in red.nodes()
        if estado_final[n]['Psi'] < umbral_alta_coherencia
    ]
    
    # Calcular clustering coefficient por grupo
    clustering_alta = nx.average_clustering(red, nodes=nodos_alta_Psi)
    clustering_baja = nx.average_clustering(red, nodes=nodos_baja_Psi)
    clustering_global = nx.average_clustering(red)
    
    # Asortatividad por coherencia
    # ¿Nodos de alta coherencia se conectan preferentemente entre sí?
    atributos_Psi = {n: estado_final[n]['Psi'] for n in red.nodes()}
    nx.set_node_attributes(red, atributos_Psi, 'Psi_final')
    
    try:
        asortatividad = nx.attribute_assortativity_coefficient(red, 'Psi_final')
    except:
        asortatividad = 0.0
    
    return {
        'clustering_alta_coherencia': clustering_alta,
        'clustering_baja_coherencia': clustering_baja,
        'clustering_global': clustering_global,
        'asortatividad_coherencia': asortatividad,
        'n_nodos_alta_coherencia': len(nodos_alta_Psi),
        'n_nodos_baja_coherencia': len(nodos_baja_Psi),
        'interpretacion': (
            f'Asortatividad Ψ = {asortatividad:.3f} '
            f'{"(positiva: alta-Ψ se conectan)" if asortatividad > 0 else "(negativa)"}'
        )
    }


def simular_experimento_completo(
    n_participantes: int = 100,
    n_intervenidos: int = 20,
    num_pasos: int = 100,
    verbose: bool = False
) -> Dict[str, any]:
    """
    Ejecuta simulación completa de experimento de red.
    
    Esta es una demostración de concepto que muestra los resultados
    esperados del experimento real.
    
    Parameters
    ----------
    n_participantes : int
        Tamaño de la red
    n_intervenidos : int
        Número de nodos con intervención 141.7 Hz
    num_pasos : int
        Pasos temporales de simulación
    verbose : bool
        Si True, imprime información detallada
    
    Returns
    -------
    resultados_completos : Dict
        Todos los análisis y métricas
    """
    # 1. Crear experimento
    red, protocolo, simular = experimento_red_social(
        n_participantes=n_participantes,
        n_intervenidos=n_intervenidos
    )
    
    if verbose:
        print("="*60)
        print("EXPERIMENTO DE RED SOCIAL QCAL")
        print("="*60)
        print(protocolo)
        print()
    
    # 2. Simular propagación
    if verbose:
        print("Simulando propagación temporal...")
    
    historia = simular(red, num_pasos=num_pasos)
    
    # 3. Análisis de efectos
    if verbose:
        print("Analizando efectos de red...")
    
    efectos = analizar_efectos_red(historia, red)
    
    # 4. Análisis de clustering
    clustering = analizar_clustering_coherencia(red, historia)
    
    # 5. Métricas topológicas
    try:
        import networkx as nx
        metricas_red = {
            'n_nodos': red.number_of_nodes(),
            'n_aristas': red.number_of_edges(),
            'grado_promedio': np.mean([d for n, d in red.degree()]),
            'clustering_coefficient': nx.average_clustering(red),
            'longitud_camino_promedio': nx.average_shortest_path_length(red),
            'small_world_coefficient': (
                nx.average_clustering(red) /
                nx.average_shortest_path_length(red)
            )
        }
    except:
        metricas_red = {}
    
    # 6. Compilar resultados
    resultados_completos = {
        'protocolo': protocolo,
        'efectos_propagacion': efectos,
        'clustering_coherencia': clustering,
        'metricas_topologicas': metricas_red,
        'historia_completa': historia,  # Para análisis detallado
        'red': red  # Grafo NetworkX
    }
    
    if verbose:
        print()
        print("="*60)
        print("RESULTADOS")
        print("="*60)
        print(f"\nReducción T₀₀:")
        print(f"  Experimental: {efectos['T00_reduccion_experimental']:.3f}x")
        print(f"  Control: {efectos['T00_reduccion_control']:.3f}x")
        print(f"  Ratio: {efectos['ratio_efecto']:.2f}")
        print(f"\nPropagación:")
        print(f"  Distancia característica: {efectos['distancia_influencia_caracteristica']:.1f} saltos")
        print(f"  Lambda decay: {efectos['lambda_decay']:.3f}")
        print(f"\nClustering:")
        print(f"  Alta coherencia: {clustering['clustering_alta_coherencia']:.3f}")
        print(f"  Baja coherencia: {clustering['clustering_baja_coherencia']:.3f}")
        print(f"  Asortatividad: {clustering['asortatividad_coherencia']:.3f}")
        print()
    
    return resultados_completos
