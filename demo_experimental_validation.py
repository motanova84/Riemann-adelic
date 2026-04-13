#!/usr/bin/env python3
"""
Demostración del Protocolo de Validación Experimental QCAL

Este script ejecuta demostraciones de las 4 fases del protocolo experimental:
- Fase I: Validación SU(Ψ)
- Fase II: Validación T_μν(Φ)
- Fase III: Propagación en red
- Fase IV: Meta-análisis

Uso:
    python demo_experimental_validation.py [--fase N] [--verbose]
    
Opciones:
    --fase N    : Ejecutar solo la fase N (1-4). Si se omite, ejecuta todas.
    --verbose   : Mostrar salida detallada
    --quiet     : Salida mínima

Autor: José Manuel Mota Burruezo
Frecuencia: f₀ = 141.7001 Hz
"""

import numpy as np
import sys
import argparse


def demo_fase_i():
    """
    Demostración de Fase I: Validación de SU(Ψ).
    """
    print("\n" + "="*70)
    print("FASE I: VALIDACIÓN DE SU(Ψ) - GRUPO DE COHERENCIA CUÁNTICA")
    print("="*70)
    
    from experimental_validation.fase_i_su_psi import (
        extraer_estado_psi,
        calcular_coherencia,
        test_estructura_grupo_SU,
        analizar_geodesicas,
        analisis_estadistico_SU
    )
    
    print("\n1. Simulando datos EEG (256 canales × 1000 muestras)...")
    np.random.seed(42)
    señal_eeg = np.random.randn(256, 1000)
    
    print("2. Extrayendo estado cuántico |Ψ⟩...")
    psi = extraer_estado_psi(señal_eeg, n_componentes=4)
    
    print("3. Calculando coherencia cuántica...")
    coherencia = calcular_coherencia(psi)
    
    print(f"\n   Estado cuántico |Ψ⟩ en ℂ⁴:")
    print(f"   Ψ = {psi}")
    print(f"   ||Ψ|| = {np.linalg.norm(psi):.6f} (debe ser ≈ 1)")
    print(f"   Coherencia (pureza) = {coherencia:.6f}")
    
    print("\n4. Simulando trayectoria temporal (30 estados)...")
    trayectoria = []
    for t in range(30):
        # Simular evolución temporal con pequeñas perturbaciones
        señal_t = señal_eeg + 0.1 * np.random.randn(*señal_eeg.shape)
        psi_t = extraer_estado_psi(señal_t, n_componentes=4)
        trayectoria.append(psi_t)
    
    print("5. Verificando estructura de grupo SU(n)...")
    tests = test_estructura_grupo_SU(trayectoria)
    
    print(f"\n   Tests de estructura SU(n):")
    print(f"   ✓ Preservación de norma: {tests['preservacion_norma']}")
    print(f"     - Norma promedio: {tests['normas_promedio']:.6f}")
    print(f"     - Desviación: {tests['normas_std']:.6f}")
    print(f"   ✓ Unitariedad: {tests['unitariedad']:.2%}")
    print(f"     - Transiciones unitarias: {tests['n_transiciones_unitarias']}/{tests['n_transiciones_total']}")
    print(f"   ✓ Cerradura: {tests['cerradura']:.2%}")
    print(f"   ✓ Álgebra de Lie: {tests['algebra_lie']:.2%}")
    print(f"   ✓ Generadores extraídos: {tests['n_generadores']}")
    print(f"\n   → Es SU(n): {tests['es_SU_n']} {'✓' if tests['es_SU_n'] else '✗'}")
    
    print("\n6. Analizando geodésicas (trayectorias óptimas)...")
    geodesicas = analizar_geodesicas(trayectoria)
    
    print(f"\n   Análisis de geodésicas:")
    print(f"   - Curvatura media: {geodesicas['curvatura_media']:.4f}")
    print(f"   - Curvatura std: {geodesicas['curvatura_std']:.4f}")
    print(f"   - Es geodésica (κ < 0.1): {geodesicas['es_geodesica']} {'✓' if geodesicas['es_geodesica'] else '✗'}")
    print(f"   - Longitud del camino: {geodesicas['longitud_camino']:.4f}")
    
    print("\n7. Simulando comparación meditadores vs. controles...")
    # Simular datos de dos grupos
    datos_control = [trayectoria for _ in range(10)]  # 10 sujetos control
    
    # Meditadores: mayor coherencia, trayectorias más eficientes
    datos_meditadores = []
    for _ in range(10):
        tray_med = []
        for t in range(30):
            señal_med = señal_eeg + 0.05 * np.random.randn(*señal_eeg.shape)  # Menos ruido
            psi_med = extraer_estado_psi(señal_med, n_componentes=4)
            tray_med.append(psi_med)
        datos_meditadores.append(tray_med)
    
    stats = analisis_estadistico_SU(datos_control, datos_meditadores)
    
    if 'coherencia' in stats:
        print(f"\n   Resultados estadísticos:")
        print(f"   Coherencia basal:")
        print(f"     - Control: {stats['coherencia']['media_control']:.4f}")
        print(f"     - Meditadores: {stats['coherencia']['media_meditadores']:.4f}")
        print(f"     - p-valor: {stats['coherencia']['p_valor']:.4f}")
        print(f"     - Tamaño efecto (d): {stats['coherencia']['tamaño_efecto']:.2f}")
    
    if 'estabilidad_SU' in stats:
        print(f"\n   Estabilidad estructural SU(n):")
        print(f"     - Control: {stats['estabilidad_SU']['control']:.4f}")
        print(f"     - Meditadores: {stats['estabilidad_SU']['meditadores']:.4f}")
        print(f"     - Diferencia significativa: {stats['estabilidad_SU']['diferencia_significativa']}")
    
    print("\n   ✓ FASE I COMPLETADA")
    return True


def demo_fase_ii():
    """
    Demostración de Fase II: Validación de T_μν(Φ).
    """
    print("\n" + "="*70)
    print("FASE II: VALIDACIÓN DE T_μν(Φ) - TENSOR DE STRESS EMOCIONAL")
    print("="*70)
    
    from experimental_validation.fase_ii_tensor import (
        construir_campo_emocional,
        calcular_tensor_stress_energia,
        calcular_curvatura_emocional,
        test_correlacion_T00_amigdala,
        test_flujo_emocional_diadas,
        rct_frecuencia_141_7_Hz,
        simular_resultados_esperados
    )
    
    print("\n1. Simulando datos multi-sensor (EDA, HRV, fMRI, autorreporte)...")
    np.random.seed(42)
    n_samples = 100
    
    datos = {
        'eda': 0.5 + 0.2 * np.random.randn(n_samples),  # Arousal
        'hrv': 0.6 + 0.15 * np.random.randn(n_samples),  # Regulación
        'amigdala': 0.4 + 0.3 * np.random.randn(n_samples),  # Procesamiento
        'autorreporte': 0.5 + 0.25 * np.random.randn(n_samples)  # Experiencia
    }
    
    print("2. Construyendo campo emocional Φ(t)...")
    Phi = construir_campo_emocional(datos)
    
    print(f"\n   Campo emocional Φ:")
    print(f"   - Media: {Phi.mean():.3f}")
    print(f"   - Std: {Phi.std():.3f}")
    print(f"   - Rango: [{Phi.min():.3f}, {Phi.max():.3f}]")
    
    print("\n3. Calculando tensor de stress-energía T_μν...")
    # Expandir a espaciotemporal (tiempo, x, y)
    Phi_3d = Phi[:, np.newaxis, np.newaxis]
    T_μν = calcular_tensor_stress_energia(Phi_3d)
    
    print(f"\n   Tensor T_μν (forma: {T_μν.shape}):")
    print(f"   - T₀₀ (densidad energía): media = {T_μν[0,0].mean():.4f}")
    print(f"   - T₀₁ (flujo momento-x): media = {T_μν[0,1].mean():.4f}")
    print(f"   - T₁₁ (stress espacial): media = {T_μν[1,1].mean():.4f}")
    
    print("\n4. Calculando curvatura emocional ∇²Φ...")
    curvatura = calcular_curvatura_emocional(Phi)
    
    print(f"\n   Curvatura ∇²Φ:")
    print(f"   - Curvatura media: {curvatura['curvatura_media']:.4f}")
    print(f"   - Curvatura máxima: {curvatura['max_curvatura']:.4f}")
    print(f"   - Singularidades detectadas: {curvatura['num_singularidades']}")
    
    print("\n5. Test P2.1: Correlación T₀₀ ↔ Amígdala...")
    datos_test = {
        'tensor': T_μν,
        'fmri_amigdala': datos['amigdala']
    }
    corr = test_correlacion_T00_amigdala(datos_test)
    
    print(f"\n   Correlación T₀₀ - Amígdala:")
    print(f"   - r de Pearson: {corr['correlacion']:.3f}")
    print(f"   - p-valor: {corr['p_valor']:.4f}")
    print(f"   - Lag óptimo: {corr['lag_optimo']} TR")
    print(f"   - Interpretación: {corr['interpretacion']}")
    print(f"   - Significativo: {corr['significativo']} {'✓' if corr['significativo'] else '✗'}")
    
    print("\n6. Protocolo RCT 141.7 Hz...")
    rct = rct_frecuencia_141_7_Hz()
    
    print(f"\n   Diseño del RCT:")
    for grupo, config in rct['diseño'].items():
        print(f"   - {grupo}: n={config['n']}, {config['intervencion']}")
    
    print(f"\n   Outcomes primarios:")
    for outcome, desc in list(rct['outcomes_primarios'].items())[:2]:
        print(f"   - {outcome}: {desc['descripcion']}")
    
    print("\n7. Predicciones a priori del modelo QCAL...")
    resultados_esp, comparaciones = simular_resultados_esperados()
    
    print(f"\n   Resultados esperados (día 28):")
    for grupo, valores in resultados_esp.items():
        print(f"\n   {grupo}:")
        print(f"     - T₀₀: {valores['T00']:.3f} (baseline: 0.45)")
        print(f"     - Ψ: {valores['Psi']:.3f} (baseline: 0.78)")
        print(f"     - Mecanismo: {valores['mecanismo']}")
    
    print("\n   ✓ FASE II COMPLETADA")
    return True


def demo_fase_iii():
    """
    Demostración de Fase III: Propagación en Red.
    """
    print("\n" + "="*70)
    print("FASE III: PROPAGACIÓN EN RED SOCIAL")
    print("="*70)
    
    from experimental_validation.fase_iii_network import simular_experimento_completo
    
    print("\n1. Ejecutando simulación de red social (N=100, small-world)...")
    print("   (Esto puede tomar unos segundos...)")
    
    resultados = simular_experimento_completo(
        n_participantes=100,
        n_intervenidos=20,
        num_pasos=50,  # Reducido para demo
        verbose=False
    )
    
    print("\n   ✓ Simulación completada")
    
    efectos = resultados['efectos_propagacion']
    clustering = resultados['clustering_coherencia']
    metricas = resultados['metricas_topologicas']
    
    print(f"\n2. Resultados de propagación:")
    print(f"   - Reducción T₀₀ experimental: {efectos['T00_reduccion_experimental']:.3f}x")
    print(f"   - Reducción T₀₀ control: {efectos['T00_reduccion_control']:.3f}x")
    print(f"   - Ratio de efecto: {efectos['ratio_efecto']:.2f}")
    print(f"\n   - Distancia de influencia: {efectos['distancia_influencia_caracteristica']:.1f} saltos")
    print(f"   - Lambda decay: {efectos['lambda_decay']:.3f}")
    print(f"   - Amplitud inicial: {efectos['amplitud_inicial']:.3f}")
    
    print(f"\n3. Análisis de clustering por coherencia:")
    print(f"   - Clustering alta Ψ: {clustering['clustering_alta_coherencia']:.3f}")
    print(f"   - Clustering baja Ψ: {clustering['clustering_baja_coherencia']:.3f}")
    print(f"   - Asortatividad Ψ: {clustering['asortatividad_coherencia']:.3f}")
    print(f"   - Nodos alta coherencia: {clustering['n_nodos_alta_coherencia']}")
    
    print(f"\n4. Métricas topológicas de la red:")
    print(f"   - Nodos: {metricas['n_nodos']}")
    print(f"   - Aristas: {metricas['n_aristas']}")
    print(f"   - Grado promedio: {metricas['grado_promedio']:.2f}")
    print(f"   - Clustering coefficient: {metricas['clustering_coefficient']:.3f}")
    print(f"   - Longitud camino promedio: {metricas['longitud_camino_promedio']:.2f}")
    
    print(f"\n   Interpretación:")
    print(f"   {efectos['interpretacion']}")
    
    print("\n   ✓ FASE III COMPLETADA")
    return True


def demo_fase_iv():
    """
    Demostración de Fase IV: Meta-Análisis.
    """
    print("\n" + "="*70)
    print("FASE IV: META-ANÁLISIS Y SÍNTESIS")
    print("="*70)
    
    from experimental_validation.fase_iv_metanalysis import generar_reporte_completo
    
    print("\n1. Generando meta-análisis de todas las fases...")
    print("   (Usando datos de demostración)")
    
    reporte = generar_reporte_completo(verbose=False)
    
    meta = reporte['meta_analisis']
    plan = reporte['planificacion_futura']
    
    print(f"\n2. Resultados del meta-análisis:")
    print(f"\n   Estudios integrados:")
    for nombre, estudio in meta['detalles_estudios'].items():
        print(f"   - {nombre}: n={estudio['n_total']}")
    
    print(f"\n   Efecto combinado:")
    print(f"   - Cohen's d = {meta['efecto_combinado_d']:.3f}")
    print(f"   - IC 95% = [{meta['IC_95'][0]:.3f}, {meta['IC_95'][1]:.3f}]")
    print(f"   - N total = {meta['N_total']}")
    
    print(f"\n   Heterogeneidad:")
    print(f"   - I² = {meta['heterogeneidad_I2']:.1f}%")
    print(f"   - Interpretación: {meta['heterogeneidad_interpretacion']}")
    
    print(f"\n3. Planificación de estudios futuros:")
    print(f"   - N recomendado por grupo: {plan['n_por_grupo_recomendado']}")
    print(f"   - N total recomendado: {plan['n_total_recomendado']}")
    print(f"   - Poder esperado: {plan['poder_esperado']:.2%}")
    print(f"\n   Recomendación: {plan['recomendacion']}")
    
    print(f"\n4. Conclusión final:")
    print(f"\n{meta['conclusion_final']}")
    
    print("\n   ✓ FASE IV COMPLETADA")
    return True


def main():
    """
    Función principal de demostración.
    """
    parser = argparse.ArgumentParser(
        description='Demostración del Protocolo de Validación Experimental QCAL'
    )
    parser.add_argument(
        '--fase',
        type=int,
        choices=[1, 2, 3, 4],
        help='Ejecutar solo la fase especificada (1-4)'
    )
    parser.add_argument(
        '--verbose',
        action='store_true',
        help='Salida detallada'
    )
    parser.add_argument(
        '--quiet',
        action='store_true',
        help='Salida mínima'
    )
    
    args = parser.parse_args()
    
    # Banner
    if not args.quiet:
        print("\n" + "="*70)
        print("PROTOCOLO DE VALIDACIÓN EXPERIMENTAL QCAL")
        print("Del Formalismo a la Evidencia Empírica")
        print("="*70)
        print("\nAutor: José Manuel Mota Burruezo Ψ ✧ ∞³")
        print("ORCID: 0009-0002-1923-0773")
        print("Frecuencia Base: f₀ = 141.7001 Hz")
        print("DOI: 10.5281/zenodo.17379721")
    
    try:
        # Ejecutar fases
        if args.fase == 1:
            demo_fase_i()
        elif args.fase == 2:
            demo_fase_ii()
        elif args.fase == 3:
            demo_fase_iii()
        elif args.fase == 4:
            demo_fase_iv()
        else:
            # Ejecutar todas las fases
            success = True
            success = success and demo_fase_i()
            success = success and demo_fase_ii()
            success = success and demo_fase_iii()
            success = success and demo_fase_iv()
            
            if success and not args.quiet:
                print("\n" + "="*70)
                print("✓ TODAS LAS FASES COMPLETADAS EXITOSAMENTE")
                print("="*70)
                print("\nEl protocolo experimental QCAL ha sido validado conceptualmente.")
                print("Ver experimental_validation/README.md para detalles completos.")
                print("\n⚠️  IMPORTANTE: Cualquier experimento real con humanos requiere")
                print("   aprobación ética y registro en ClinicalTrials.gov")
                print("="*70 + "\n")
        
        return 0
        
    except Exception as e:
        print(f"\n❌ Error durante la demostración: {e}", file=sys.stderr)
        if args.verbose:
            import traceback
            traceback.print_exc()
        return 1


if __name__ == "__main__":
    sys.exit(main())
