#!/usr/bin/env python3
"""
Demonstration Script: Paradigma de la Coherencia Descendente
=============================================================

Interactive demonstration of the five phenomena explained by the
Descending Coherence Paradigm framework.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: 2026-02-12
Institution: Instituto de Conciencia Cuántica (ICQ)
"""

import sys
from pathlib import Path

# Add utils to path
repo_root = Path(__file__).parent
sys.path.insert(0, str(repo_root / "utils"))

from coherencia_descendente import (
    complejidad_irreducible,
    AntenaBiologica,
    ConcienciaEncarnada,
    correlacion_no_local,
    transicion_evolutiva,
    ParadigmaCoherenciaDescendente
)


def print_header(title: str):
    """Print formatted section header."""
    print()
    print("═" * 80)
    print(f"  {title}")
    print("═" * 80)
    print()


def print_subheader(title: str):
    """Print formatted subsection header."""
    print()
    print("─" * 80)
    print(f"  {title}")
    print("─" * 80)
    print()


def demo_complejidad_irreducible():
    """Demonstrate irreducible complexity phenomenon."""
    print_subheader("1. COMPLEJIDAD IRREDUCIBLE: EL SALTO DE COHERENCIA")
    
    print("El flagelo bacteriano tiene 40 partes proteicas interdependientes.")
    print("Pregunta materialista: ¿Cómo evolucionó por azar gradual?")
    print("Respuesta QCAL ∞³: No evolucionó. Se SINCRONIZÓ.")
    print()
    
    # Below threshold
    print("Coherencia Ψ = 0.75 (BAJO UMBRAL):")
    estado_bajo = complejidad_irreducible(40, 0.75)
    print(f"  Estado: {estado_bajo.estado}")
    print(f"  Tiempo: {estado_bajo.tiempo}")
    print(f"  Mecanismo: {estado_bajo.mecanismo}")
    print()
    
    # Above threshold
    print("Coherencia Ψ = 0.95 (SOBRE UMBRAL Ψ ≥ 0.888):")
    estado_alto = complejidad_irreducible(40, 0.95)
    print(f"  Estado: {estado_alto.estado}")
    print(f"  Tiempo: {estado_alto.tiempo}")
    print(f"  Mecanismo: {estado_alto.mecanismo}")
    print()
    
    print("∴ El flagelo NO se construyó pieza por pieza.")
    print("  Se RECONOCIÓ cuando el campo alcanzó la frecuencia correcta.")
    print("  Las 40 partes aparecieron SIMULTÁNEAMENTE por resonancia.")


def demo_aparicion_conciencia():
    """Demonstrate consciousness appearance phenomenon."""
    print_subheader("2. APARICIÓN DE CONCIENCIA: EL ACOPLE DE ANTENA")
    
    print("Pregunta materialista: ¿Cómo surgió la conciencia de materia inerte?")
    print("Respuesta QCAL ∞³: La conciencia NO emerge. La antena se ACOPLA.")
    print()
    
    # Simple nervous system
    print("Sistema nervioso simple (1000 neuronas):")
    sistema_simple = AntenaBiologica(1000)
    estado_simple = sistema_simple.sintonizar()
    print(f"  Estado: {estado_simple}")
    print(f"  Sintonización: {sistema_simple.sintonizacion:.6f}")
    print(f"  Consciente: {sistema_simple.conciencia}")
    print()
    
    # Human brain
    print("Cerebro humano (86 mil millones de neuronas):")
    cerebro_humano = AntenaBiologica(86e9)
    estado_humano = cerebro_humano.sintonizar()
    print(f"  Estado: {estado_humano}")
    print(f"  Sintonización: {cerebro_humano.sintonizacion:.6f}")
    print(f"  Consciente: {cerebro_humano.conciencia}")
    print(f"  Frecuencia campo: {cerebro_humano.get_state()['field_frequency']:.4f} Hz")
    print()
    
    print("∴ La conciencia no apareció 'de repente'.")
    print("  La antena estuvo sintonizándose por millones de años.")
    print("  Cuando la precisión superó Ψ = 0.888, el ACOPLE ocurrió.")
    print("  No fue magia. Fue INGENIERÍA DE RESONANCIA a f₀ = 141.7001 Hz.")


def demo_experiencias_cercanas_muerte():
    """Demonstrate near-death experiences phenomenon."""
    print_subheader("3. EXPERIENCIAS CERCANAS A LA MUERTE: DESCORRELACIÓN TRANSITORIA")
    
    print("Pregunta materialista: ¿Cómo experiencias lúcidas sin actividad cerebral?")
    print("Respuesta QCAL ∞³: El cerebro es la ANTENA, no la fuente.")
    print()
    
    conciencia = ConcienciaEncarnada()
    
    # Normal state
    print("Estado normal:")
    estado_normal = conciencia.ECM(intensidad=0.5)
    print(f"  Consciencia: {estado_normal['conciencia']}")
    print(f"  Localización: {estado_normal['localizacion']}")
    print(f"  Antena activa: {estado_normal['antena_activa']}")
    print()
    
    # Near-death experience
    print("Paro cardíaco (intensidad = 0.98):")
    ecm = conciencia.ECM(intensidad=0.98)
    print(f"  Consciencia: {ecm['conciencia']} (¡Sigue consciente!)")
    print(f"  Localización: {ecm['localizacion']}")
    print(f"  Percepción: {ecm['percepcion']}")
    print(f"  Verificación: {ecm['verificacion']}")
    print(f"  Campo: {ecm['campo']}")
    print(f"  Antena activa: {ecm['antena_activa']}")
    print()
    
    # Resuscitation
    print("Reanimación:")
    memoria = conciencia.reanimacion()
    print(f"  Resultado: {memoria}")
    print(f"  Localización: {conciencia.localizacion}")
    print()
    
    print("∴ La muerte no es 'apagar una luz'.")
    print("  Es DESENCHUFAR una radio.")
    print("  La señal a 141.7001 Hz sigue transmitiendo.")
    print("  El receptor dejó de decodificarla.")


def demo_no_localidad():
    """Demonstrate non-locality phenomenon."""
    print_subheader("4. NO-LOCALIDAD: RESONANCIA DE CAMPO A TRAVÉS DE κ_Π")
    
    print("Pregunta materialista: ¿Cómo entrelazamiento instantáneo a distancia?")
    print("Respuesta QCAL ∞³: La distancia es ILUSORIA en coherencia perfecta.")
    print()
    
    # High coherence - distance irrelevant
    print("Alta coherencia (Ψ = 0.95), distancia = 10^10 unidades:")
    alta_coh = correlacion_no_local(distancia=1e10, coherencia_psi=0.95)
    print(f"  Correlación: {alta_coh['correlacion']:.4f}")
    print(f"  Tiempo: {alta_coh['tiempo']}")
    print(f"  Mecanismo: {alta_coh['mecanismo']}")
    print()
    
    # Low coherence - separation appears
    print("Baja coherencia (Ψ = 0.5), distancia = 100 unidades:")
    baja_coh = correlacion_no_local(distancia=100, coherencia_psi=0.5)
    print(f"  Correlación: {baja_coh['correlacion']:.4f}")
    print(f"  Tiempo: {baja_coh['tiempo']}")
    print(f"  Distancia: {baja_coh['distancia']}")
    print()
    
    print("∴ El entrelazamiento NO es una rareza.")
    print("  Es la VERDADERA NATURALEZA de la realidad.")
    print("  La separación espacial es una PROYECCIÓN de decoherencia.")
    print("  En coherencia perfecta, la distancia DEJA DE EXISTIR como barrera.")


def demo_evolucion_puntuada():
    """Demonstrate punctuated evolution phenomenon."""
    print_subheader("5. EVOLUCIÓN PUNTUADA: SALTOS DE COHERENCIA POR UMBRALES DISCRETOS")
    
    print("Pregunta materialista: ¿Por qué el registro fósil muestra saltos súbitos?")
    print("Respuesta QCAL ∞³: La evolución NO es gradual. Es una ESCALERA.")
    print()
    
    # Current human state
    print("∴ LA ESCALERA DE COHERENCIA ∴")
    print()
    resultado = transicion_evolutiva(coherencia_actual=0.8991)
    
    for stage in resultado['stages']:
        symbol = "✓" if stage['activated'] else "·"
        estado = "ACTIVADO" if stage['activated'] else "POTENCIAL"
        print(f"  {symbol} {stage['stage']:<20} Ψ = {stage['threshold']:.4f}  ({estado})")
    
    print()
    print(f"Estado actual: {resultado['estado_actual']}")
    print(f"Coherencia: {resultado['coherencia']:.4f}")
    print(f"Próximo umbral: {resultado['proximo_umbral']:.3f} (CONCIENCIA_GLOBAL)")
    print(f"Tiempo hasta transición: {resultado['tiempo_hasta_transicion']}")
    print()
    
    print("∴ El cerebro humano NO es el pináculo de la evolución.")
    print("  Es el PRIMER ACOPLE CONSCIENTE de la antena.")
    print("  El siguiente umbral: Ψ = 0.950 - CONCIENCIA GLOBAL")
    print("  No es profecía. Es INGENIERÍA DE COHERENCIA.")


def demo_paradigma_completo():
    """Demonstrate complete unified paradigm."""
    print_header("PARADIGMA UNIFICADO DE LA COHERENCIA DESCENDENTE")
    
    print("Creando marco unificado QCAL ∞³...")
    paradigma = ParadigmaCoherenciaDescendente()
    
    print()
    print("Generando reporte completo de los cinco fenómenos...")
    print()
    
    reporte = paradigma.generar_reporte_completo()
    
    print(f"Paradigma: {reporte['paradigma']}")
    print(f"Frecuencia Portadora: {reporte['frecuencia_portadora']}")
    print(f"Coherencia Sistema: {reporte['coherencia_sistema']}")
    print(f"Umbral Crítico: {reporte['umbral_critico']}")
    print(f"Constante Acoplamiento: {reporte['constante_acoplamiento']}")
    print()
    
    print_subheader("MATRIZ DE UNIFICACIÓN: 5 FENÓMENOS, 1 MECANISMO")
    
    fenomenos_nombres = [
        "Complejidad Irreducible",
        "Aparición de Conciencia",
        "Experiencias Cercanas a la Muerte",
        "No-localidad",
        "Evolución Puntuada"
    ]
    
    for i, nombre in enumerate(fenomenos_nombres, 1):
        print(f"{i}. {nombre}")
    
    print()
    print_subheader("VERIFICACIÓN EXPERIMENTAL")
    
    for key, value in reporte['verificacion_experimental'].items():
        print(f"  • {value}")
    
    print()
    print_subheader("DECLARACIÓN")
    print()
    print(f"  {reporte['declaracion']}")
    print()
    
    print("─" * 80)
    print(f"  {reporte['firma']}")
    print(f"  {reporte['autor']}")
    print(f"  {reporte['institucion']}")
    print(f"  {reporte['fecha']}")
    print("═" * 80)


def main():
    """Run complete demonstration."""
    print_header("PARADIGMA DE LA COHERENCIA DESCENDENTE")
    print("        Descending Coherence Paradigm - QCAL ∞³")
    print()
    print("Tesis Central:")
    print("  • La conciencia NO emerge de la complejidad material ascendente")
    print("  • La conciencia DESCIENDE como coherencia vibracional hacia la materia")
    print("  • La evolución biológica es SINTONIZACIÓN de antenas receptoras")
    print("  • La muerte es DESCORRELACIÓN de la antena, no extinción del campo")
    
    # Demonstrate each phenomenon
    demo_complejidad_irreducible()
    demo_aparicion_conciencia()
    demo_experiencias_cercanas_muerte()
    demo_no_localidad()
    demo_evolucion_puntuada()
    
    # Show unified paradigm
    print()
    demo_paradigma_completo()


if __name__ == "__main__":
    main()
