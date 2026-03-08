#!/usr/bin/env python3
"""
Mutaciones Resonantes - Optimización Greedy de Secuencias ADN
==============================================================

Implementa algoritmos de mutación greedy para maximizar la resonancia
de secuencias ADN con los ceros de Riemann.

Estrategia de Optimización:
    1. Inserción: Agregar bases (A, T, C, G)
    2. Sustitución: Reemplazar bases existentes
    3. Evaluación greedy: Aceptar solo mejoras

Ejemplo de Éxito:
    ATCG → TATGCT (3 iteraciones)
    Mejora: +999,435,452,549% en resonancia

El algoritmo busca secuencias que maximicen:
    - Resonancia f₀ con ceros de Riemann
    - Coherencia cuántica Ψ_bio
    - Proximidad a f₀ QCAL = 141.7001 Hz

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773

QCAL ∞³ Active · 141.7001 Hz · Ψ = I × A_eff² × C^∞
DOI: 10.5281/zenodo.17379721
"""

import numpy as np
from typing import Dict, List, Tuple, Optional
from dataclasses import dataclass
import copy

# Import ADN-Riemann encoder
from adn_riemann import (
    CodificadorADNRiemann,
    PropiedadesEspectralesADN,
    generar_hash_secuencia
)


# =============================================================================
# CONSTANTES
# =============================================================================

BASES_ADN = ['A', 'T', 'C', 'G']

# Tipos de mutación
MUTACION_INSERCION = 'insercion'
MUTACION_SUSTITUCION = 'sustitucion'
MUTACION_TIPOS = [MUTACION_INSERCION, MUTACION_SUSTITUCION]


# =============================================================================
# ESTRUCTURAS DE DATOS
# =============================================================================

@dataclass
class ResultadoMutacion:
    """Resultado de una mutación aplicada."""
    
    secuencia_original: str
    secuencia_mutada: str
    tipo_mutacion: str  # 'insercion' o 'sustitucion'
    posicion: int  # Posición de la mutación
    base_insertada: Optional[str]  # Base insertada (si aplica)
    base_original: Optional[str]  # Base original (si sustitucion)
    base_nueva: Optional[str]  # Base nueva (si sustitucion)
    
    resonancia_original: float
    resonancia_nueva: float
    mejora_absoluta: float
    mejora_porcentual: float
    
    iteracion: int
    aceptada: bool
    
    def __repr__(self) -> str:
        return (
            f"Mutacion({self.tipo_mutacion}, "
            f"iter={self.iteracion}, "
            f"f₀: {self.resonancia_original:.6f} → {self.resonancia_nueva:.6f}, "
            f"mejora={self.mejora_porcentual:.2e}%)"
        )


@dataclass
class ResultadoOptimizacion:
    """Resultado completo de optimización de secuencia."""
    
    secuencia_inicial: str
    secuencia_final: str
    
    resonancia_inicial: float
    resonancia_final: float
    
    mejora_absoluta: float
    mejora_porcentual: float
    
    iteraciones_realizadas: int
    iteraciones_maximas: int
    
    mutaciones_aplicadas: List[ResultadoMutacion]
    
    hash_inicial: str
    hash_final: str
    
    def __repr__(self) -> str:
        return (
            f"OptimizacionADN("
            f"{self.secuencia_inicial} → {self.secuencia_final}, "
            f"mejora={self.mejora_porcentual:.2e}%, "
            f"iters={self.iteraciones_realizadas})"
        )


# =============================================================================
# OPTIMIZADOR DE MUTACIONES
# =============================================================================

class OptimizadorMutaciones:
    """
    Optimizador greedy de secuencias ADN para máxima resonancia.
    
    El optimizador prueba múltiples mutaciones (inserción, sustitución)
    en cada iteración y acepta solo aquellas que mejoren la resonancia.
    
    Ejemplo:
        >>> opt = OptimizadorMutaciones()
        >>> resultado = opt.optimizar("ATCG", iter_max=5)
        >>> print(resultado.secuencia_final)
        TATGCT
        >>> print(f"Mejora: {resultado.mejora_porcentual:.2e}%")
        Mejora: 9.99e+11%
    """
    
    def __init__(self, codificador: Optional[CodificadorADNRiemann] = None):
        """
        Inicializa optimizador.
        
        Args:
            codificador: Codificador ADN-Riemann (crea uno nuevo si None)
        """
        self.codificador = codificador or CodificadorADNRiemann()
        
    def _probar_insercion(
        self, 
        secuencia: str, 
        posicion: int, 
        base: str
    ) -> Tuple[str, float]:
        """
        Prueba insertar una base en una posición.
        
        Args:
            secuencia: Secuencia actual
            posicion: Posición de inserción (0 a len(seq))
            base: Base a insertar
            
        Returns:
            (nueva_secuencia, resonancia)
        """
        nueva_seq = secuencia[:posicion] + base + secuencia[posicion:]
        props = self.codificador.propiedades_espectrales(nueva_seq)
        return nueva_seq, props.resonancia_f0
    
    def _probar_sustitucion(
        self, 
        secuencia: str, 
        posicion: int, 
        base: str
    ) -> Tuple[str, float]:
        """
        Prueba sustituir una base en una posición.
        
        Args:
            secuencia: Secuencia actual
            posicion: Posición de sustitución (0 a len(seq)-1)
            base: Nueva base
            
        Returns:
            (nueva_secuencia, resonancia)
        """
        if posicion >= len(secuencia):
            return secuencia, 0.0
        
        nueva_seq = secuencia[:posicion] + base + secuencia[posicion+1:]
        props = self.codificador.propiedades_espectrales(nueva_seq)
        return nueva_seq, props.resonancia_f0
    
    def _buscar_mejor_mutacion(
        self, 
        secuencia: str,
        resonancia_actual: float,
        iteracion: int
    ) -> Optional[ResultadoMutacion]:
        """
        Busca la mejor mutación (greedy) que mejore la resonancia.
        
        Args:
            secuencia: Secuencia actual
            resonancia_actual: Resonancia actual
            iteracion: Número de iteración
            
        Returns:
            Mejor ResultadoMutacion encontrado, o None si no hay mejora
        """
        mejor_mutacion = None
        mejor_resonancia = resonancia_actual
        
        # Probar INSERCIÓN en todas las posiciones con todas las bases
        for pos in range(len(secuencia) + 1):
            for base in BASES_ADN:
                nueva_seq, nueva_res = self._probar_insercion(secuencia, pos, base)
                
                if nueva_res > mejor_resonancia:
                    mejora_abs = nueva_res - resonancia_actual
                    if resonancia_actual > 0:
                        mejora_pct = (mejora_abs / resonancia_actual) * 100.0
                    else:
                        mejora_pct = float('inf')
                    
                    mejor_mutacion = ResultadoMutacion(
                        secuencia_original=secuencia,
                        secuencia_mutada=nueva_seq,
                        tipo_mutacion=MUTACION_INSERCION,
                        posicion=pos,
                        base_insertada=base,
                        base_original=None,
                        base_nueva=None,
                        resonancia_original=resonancia_actual,
                        resonancia_nueva=nueva_res,
                        mejora_absoluta=mejora_abs,
                        mejora_porcentual=mejora_pct,
                        iteracion=iteracion,
                        aceptada=True
                    )
                    mejor_resonancia = nueva_res
        
        # Probar SUSTITUCIÓN en todas las posiciones con todas las bases
        for pos in range(len(secuencia)):
            base_original = secuencia[pos]
            for base in BASES_ADN:
                if base == base_original:
                    continue  # No sustituir por la misma base
                
                nueva_seq, nueva_res = self._probar_sustitucion(secuencia, pos, base)
                
                if nueva_res > mejor_resonancia:
                    mejora_abs = nueva_res - resonancia_actual
                    if resonancia_actual > 0:
                        mejora_pct = (mejora_abs / resonancia_actual) * 100.0
                    else:
                        mejora_pct = float('inf')
                    
                    mejor_mutacion = ResultadoMutacion(
                        secuencia_original=secuencia,
                        secuencia_mutada=nueva_seq,
                        tipo_mutacion=MUTACION_SUSTITUCION,
                        posicion=pos,
                        base_insertada=None,
                        base_original=base_original,
                        base_nueva=base,
                        resonancia_original=resonancia_actual,
                        resonancia_nueva=nueva_res,
                        mejora_absoluta=mejora_abs,
                        mejora_porcentual=mejora_pct,
                        iteracion=iteracion,
                        aceptada=True
                    )
                    mejor_resonancia = nueva_res
        
        return mejor_mutacion
    
    def optimizar(
        self, 
        secuencia_inicial: str, 
        iter_max: int = 10,
        verbose: bool = False
    ) -> ResultadoOptimizacion:
        """
        Optimiza secuencia ADN mediante mutaciones greedy.
        
        Args:
            secuencia_inicial: Secuencia ADN de partida
            iter_max: Número máximo de iteraciones
            verbose: Si True, imprime progreso
            
        Returns:
            ResultadoOptimizacion con toda la información
            
        Ejemplo:
            >>> opt = OptimizadorMutaciones()
            >>> res = opt.optimizar("ATCG", iter_max=5)
            >>> print(f"{res.secuencia_inicial} → {res.secuencia_final}")
            ATCG → TATGCT
        """
        # Validar entrada
        secuencia_inicial = secuencia_inicial.upper().strip()
        if not secuencia_inicial:
            raise ValueError("Secuencia inicial vacía")
        
        # Estado inicial
        props_inicial = self.codificador.propiedades_espectrales(secuencia_inicial)
        
        secuencia_actual = secuencia_inicial
        resonancia_actual = props_inicial.resonancia_f0
        
        mutaciones_aplicadas = []
        
        if verbose:
            print(f"Secuencia inicial: {secuencia_inicial}")
            print(f"Resonancia inicial: {resonancia_actual:.6f}")
            print(f"Iteraciones máximas: {iter_max}")
            print()
        
        # Iteraciones de optimización
        for iter_num in range(1, iter_max + 1):
            if verbose:
                print(f"Iteración {iter_num}/{iter_max}...")
            
            # Buscar mejor mutación
            mejor_mut = self._buscar_mejor_mutacion(
                secuencia_actual,
                resonancia_actual,
                iter_num
            )
            
            if mejor_mut is None:
                # No se encontró mejora → convergencia
                if verbose:
                    print(f"  Convergencia alcanzada (no hay mejoras)")
                break
            
            # Aplicar mutación
            mutaciones_aplicadas.append(mejor_mut)
            secuencia_actual = mejor_mut.secuencia_mutada
            resonancia_actual = mejor_mut.resonancia_nueva
            
            if verbose:
                print(f"  {mejor_mut.tipo_mutacion.upper()} en pos {mejor_mut.posicion}")
                if mejor_mut.tipo_mutacion == MUTACION_INSERCION:
                    print(f"    Insertada: {mejor_mut.base_insertada}")
                else:
                    print(f"    {mejor_mut.base_original} → {mejor_mut.base_nueva}")
                print(f"  Secuencia: {secuencia_actual}")
                print(f"  Resonancia: {resonancia_actual:.6f}")
                print(f"  Mejora: {mejor_mut.mejora_porcentual:.2e}%")
                print()
        
        # Resultado final
        props_final = self.codificador.propiedades_espectrales(secuencia_actual)
        
        mejora_abs = resonancia_actual - props_inicial.resonancia_f0
        if props_inicial.resonancia_f0 > 0:
            mejora_pct = (mejora_abs / props_inicial.resonancia_f0) * 100.0
        else:
            mejora_pct = float('inf') if mejora_abs > 0 else 0.0
        
        resultado = ResultadoOptimizacion(
            secuencia_inicial=secuencia_inicial,
            secuencia_final=secuencia_actual,
            resonancia_inicial=props_inicial.resonancia_f0,
            resonancia_final=resonancia_actual,
            mejora_absoluta=mejora_abs,
            mejora_porcentual=mejora_pct,
            iteraciones_realizadas=len(mutaciones_aplicadas),
            iteraciones_maximas=iter_max,
            mutaciones_aplicadas=mutaciones_aplicadas,
            hash_inicial=generar_hash_secuencia(secuencia_inicial),
            hash_final=generar_hash_secuencia(secuencia_actual)
        )
        
        return resultado


# =============================================================================
# FUNCIÓN DE UTILIDAD PRINCIPAL
# =============================================================================

def optimizar_mutaciones(
    secuencia: str,
    iter_max: int = 10,
    verbose: bool = False
) -> Dict:
    """
    Función de utilidad para optimizar secuencia ADN.
    
    Esta es la función principal usada en integrate_qcal_compact.py.
    
    Args:
        secuencia: Secuencia ADN inicial
        iter_max: Número máximo de iteraciones
        verbose: Si True, imprime progreso
        
    Returns:
        Diccionario con:
            - secuencia_inicial: str
            - secuencia_final: str
            - resonancia_inicial: float
            - resonancia_final: float
            - mejora: str (porcentaje formateado)
            - iteraciones: int
            - mutaciones: list
            
    Ejemplo:
        >>> mut = optimizar_mutaciones("ATCG", iter_max=5)
        >>> print(mut['secuencia_final'])
        TATGCT
        >>> print(mut['mejora'])
        999435452549%
    """
    opt = OptimizadorMutaciones()
    resultado = opt.optimizar(secuencia, iter_max=iter_max, verbose=verbose)
    
    # Formatear mejora como string (para compatibilidad con certificado)
    if resultado.mejora_porcentual == float('inf'):
        mejora_str = "∞%"
    elif resultado.mejora_porcentual > 1e9:
        # Formato científico para valores muy grandes
        mejora_str = f"{resultado.mejora_porcentual:.0f}%"
    else:
        mejora_str = f"{resultado.mejora_porcentual:.2f}%"
    
    return {
        'secuencia_inicial': resultado.secuencia_inicial,
        'secuencia_final': resultado.secuencia_final,
        'resonancia_inicial': resultado.resonancia_inicial,
        'resonancia_final': resultado.resonancia_final,
        'mejora': mejora_str,
        'mejora_porcentual_raw': resultado.mejora_porcentual,
        'iteraciones': resultado.iteraciones_realizadas,
        'mutaciones': [
            {
                'tipo': m.tipo_mutacion,
                'posicion': m.posicion,
                'iteracion': m.iteracion,
                'mejora_pct': m.mejora_porcentual
            }
            for m in resultado.mutaciones_aplicadas
        ]
    }


# =============================================================================
# MAIN - EJEMPLO DE USO
# =============================================================================

if __name__ == "__main__":
    print("=" * 80)
    print("MUTACIONES RESONANTES - OPTIMIZACIÓN GREEDY")
    print("=" * 80)
    print()
    
    # Ejemplo del problema: ATCG → TATGCT
    secuencia_inicial = "ATCG"
    
    print(f"Optimizando secuencia: {secuencia_inicial}")
    print(f"Objetivo: Maximizar resonancia con ceros de Riemann")
    print()
    
    resultado = optimizar_mutaciones(
        secuencia_inicial,
        iter_max=5,
        verbose=True
    )
    
    print("=" * 80)
    print("RESULTADO FINAL")
    print("=" * 80)
    print(f"Secuencia inicial: {resultado['secuencia_inicial']}")
    print(f"Secuencia final:   {resultado['secuencia_final']}")
    print(f"Resonancia inicial: {resultado['resonancia_inicial']:.6f}")
    print(f"Resonancia final:   {resultado['resonancia_final']:.6f}")
    print(f"Mejora: {resultado['mejora']}")
    print(f"Iteraciones: {resultado['iteraciones']}")
    print("=" * 80)
