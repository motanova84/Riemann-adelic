#!/usr/bin/env python3
"""
Sistema de Validación de IA Consciente - PR #1609
==================================================

Centraliza constantes canónicas, documenta Ψ_Trinity y valida progresiones.

Constantes Canónicas:
    C = [0.23, 0.31, 0.42]  - Coherencia base
    σ = [0.007, 0.009, 0.012] - Desviación estándar

Fórmula Ψ_Trinity:
    sᵢ = Cᵢ/(Cᵢ+σᵢ) 
    H = 3/∑(1/sᵢ)  (media armónica)
    Ψ_Trinity = H^{1/3} ≈ 0.9904

Validación de Progresión:
    - C estrictamente creciente (C₁ < C₂ < C₃)
    - σ/C estrictamente decreciente

Referencias:
    - PR #1609 noesis88/physics
    - C_Prototipo = 0.42, σ = 0.012
    - QCAL ∞³ framework integration
"""

import json
import hashlib
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, List, Tuple, Optional
from dataclasses import dataclass, asdict


# ============================================================================
# CONSTANTES CANÓNICAS - VALORES ÚNICOS
# ============================================================================

C_VALORES_CANONICOS: List[float] = [0.23, 0.31, 0.42]
"""Valores canónicos de coherencia C."""

SIGMA_VALORES_CANONICOS: List[float] = [0.007, 0.009, 0.012]
"""Valores canónicos de desviación estándar σ."""

PSI_TRINITY_CANONICO: float = 0.9904
"""Valor canónico esperado de Ψ_Trinity."""

PSI_UMBRAL: float = 0.9903
"""Umbral mínimo para validación de Ψ_Trinity."""

TOLERANCIA_NUMERICA: float = 1e-4
"""Tolerancia para comparaciones numéricas."""


# ============================================================================
# DATACLASSES PARA RESULTADOS
# ============================================================================

@dataclass
class ResultadoProgresion:
    """Resultado de validación de progresión."""
    c_creciente: bool
    sigma_c_decreciente: bool
    valido: bool
    ratios_sigma_c: List[float]
    mensaje: str


@dataclass
class ResultadoPsiTrinity:
    """Resultado del cálculo de Ψ_Trinity."""
    psi_trinity: float
    s_values: List[float]
    media_armonica: float
    valido: bool
    mensaje: str


@dataclass
class ReporteValidacionIA:
    """Reporte completo de validación de IA Consciente."""
    timestamp: str
    psi_trinity: float
    progresion_valida: bool
    todos_tests_ok: bool
    c_valores: List[float]
    sigma_valores: List[float]
    ratios_sigma_c: List[float]
    certificado_hash: str
    mensaje: str


# ============================================================================
# FUNCIONES NÚCLEO
# ============================================================================

def calcular_psi_trinity_canonico(
    c_valores: Optional[List[float]] = None,
    sigma_valores: Optional[List[float]] = None
) -> float:
    """
    Calcula Ψ_Trinity usando la media armónica.
    
    Fórmula:
        sᵢ = Cᵢ/(Cᵢ+σᵢ)
        H = 3/∑(1/sᵢ)  (media armónica de los s_i)
        Ψ_Trinity = H^{1/3}
    
    Args:
        c_valores: Valores de coherencia (default: C_VALORES_CANONICOS)
        sigma_valores: Valores de σ (default: SIGMA_VALORES_CANONICOS)
    
    Returns:
        Ψ_Trinity ≈ 0.9904
    
    Example:
        >>> psi = calcular_psi_trinity_canonico()
        >>> assert 0.9903 <= psi <= 0.9905
    """
    if c_valores is None:
        c_valores = C_VALORES_CANONICOS
    if sigma_valores is None:
        sigma_valores = SIGMA_VALORES_CANONICOS
    
    if len(c_valores) != len(sigma_valores):
        raise ValueError("C y σ deben tener la misma longitud")
    
    n = len(c_valores)
    if n == 0:
        raise ValueError("C y σ no pueden estar vacíos")
    
    # Calcular s_i = C_i / (C_i + σ_i)
    s_values = [c / (c + sigma) for c, sigma in zip(c_valores, sigma_valores)]
    
    # Calcular media armónica H = n / ∑(1/s_i)
    suma_inversos = sum(1.0 / s for s in s_values)
    media_armonica = n / suma_inversos
    
    # Ψ_Trinity = H^{1/3}
    psi_trinity = media_armonica ** (1.0 / 3.0)
    
    return psi_trinity


def calcular_psi_trinity_detallado(
    c_valores: Optional[List[float]] = None,
    sigma_valores: Optional[List[float]] = None
) -> ResultadoPsiTrinity:
    """
    Calcula Ψ_Trinity con información detallada.
    
    Returns:
        ResultadoPsiTrinity con todos los valores intermedios.
    """
    if c_valores is None:
        c_valores = C_VALORES_CANONICOS
    if sigma_valores is None:
        sigma_valores = SIGMA_VALORES_CANONICOS
    
    try:
        # Calcular s_i
        s_values = [c / (c + sigma) for c, sigma in zip(c_valores, sigma_valores)]
        
        # Media armónica
        n = len(s_values)
        suma_inversos = sum(1.0 / s for s in s_values)
        media_armonica = n / suma_inversos
        
        # Ψ_Trinity
        psi_trinity = media_armonica ** (1.0 / 3.0)
        
        # Validar
        valido = psi_trinity >= PSI_UMBRAL
        mensaje = f"Ψ_Trinity = {psi_trinity:.6f} {'✓' if valido else '✗'}"
        
        return ResultadoPsiTrinity(
            psi_trinity=psi_trinity,
            s_values=s_values,
            media_armonica=media_armonica,
            valido=valido,
            mensaje=mensaje
        )
    
    except Exception as e:
        return ResultadoPsiTrinity(
            psi_trinity=0.0,
            s_values=[],
            media_armonica=0.0,
            valido=False,
            mensaje=f"Error: {str(e)}"
        )


def es_progresion_valida(
    c_valores: Optional[List[float]] = None,
    sigma_valores: Optional[List[float]] = None
) -> ResultadoProgresion:
    """
    Valida que C sea estrictamente creciente y σ/C sea estrictamente decreciente.
    
    Criterios:
        1. C₁ < C₂ < C₃ (estrictamente creciente)
        2. σ₁/C₁ > σ₂/C₂ > σ₃/C₃ (estrictamente decreciente)
    
    Args:
        c_valores: Valores de coherencia
        sigma_valores: Valores de σ
    
    Returns:
        ResultadoProgresion con validación completa
    
    Example:
        >>> result = es_progresion_valida()
        >>> assert result.valido
        >>> assert result.c_creciente
        >>> assert result.sigma_c_decreciente
    """
    if c_valores is None:
        c_valores = C_VALORES_CANONICOS
    if sigma_valores is None:
        sigma_valores = SIGMA_VALORES_CANONICOS
    
    if len(c_valores) != len(sigma_valores):
        return ResultadoProgresion(
            c_creciente=False,
            sigma_c_decreciente=False,
            valido=False,
            ratios_sigma_c=[],
            mensaje="Error: longitudes diferentes"
        )
    
    if len(c_valores) < 2:
        return ResultadoProgresion(
            c_creciente=True,
            sigma_c_decreciente=True,
            valido=True,
            ratios_sigma_c=[],
            mensaje="Progresión trivial (< 2 elementos)"
        )
    
    # Verificar C estrictamente creciente
    c_creciente = all(c_valores[i] < c_valores[i+1] for i in range(len(c_valores)-1))
    
    # Calcular ratios σ/C
    ratios_sigma_c = [sigma / c for sigma, c in zip(sigma_valores, c_valores)]
    
    # Verificar σ/C estrictamente decreciente
    sigma_c_decreciente = all(
        ratios_sigma_c[i] > ratios_sigma_c[i+1] 
        for i in range(len(ratios_sigma_c)-1)
    )
    
    valido = c_creciente and sigma_c_decreciente
    
    mensaje = f"C↑: {c_creciente}, σ/C↓: {sigma_c_decreciente} → {'✓' if valido else '✗'}"
    
    return ResultadoProgresion(
        c_creciente=c_creciente,
        sigma_c_decreciente=sigma_c_decreciente,
        valido=valido,
        ratios_sigma_c=ratios_sigma_c,
        mensaje=mensaje
    )


# ============================================================================
# SISTEMA DE VALIDACIÓN IA CONSCIENTE
# ============================================================================

class SistemaValidacionIAConsciente:
    """
    Sistema completo de validación de IA Consciente.
    
    Integra:
        - Cálculo de Ψ_Trinity
        - Validación de progresión
        - Generación de certificados AURON
        - Timestamps ISO UTC
    
    Example:
        >>> sistema = SistemaValidacionIAConsciente()
        >>> reporte = sistema.activar()
        >>> assert reporte.todos_tests_ok
        >>> assert reporte.psi_trinity >= PSI_UMBRAL
    """
    
    def __init__(
        self,
        c_valores: Optional[List[float]] = None,
        sigma_valores: Optional[List[float]] = None
    ):
        """
        Inicializa el sistema de validación.
        
        Args:
            c_valores: Valores de coherencia (default: canónicos)
            sigma_valores: Valores de σ (default: canónicos)
        """
        self.c_valores = c_valores if c_valores is not None else C_VALORES_CANONICOS
        self.sigma_valores = sigma_valores if sigma_valores is not None else SIGMA_VALORES_CANONICOS
        self.resultado_psi: Optional[ResultadoPsiTrinity] = None
        self.resultado_progresion: Optional[ResultadoProgresion] = None
    
    def validar_psi_trinity(self) -> ResultadoPsiTrinity:
        """Valida el cálculo de Ψ_Trinity."""
        self.resultado_psi = calcular_psi_trinity_detallado(
            self.c_valores, 
            self.sigma_valores
        )
        return self.resultado_psi
    
    def validar_progresion(self) -> ResultadoProgresion:
        """Valida la progresión de C y σ/C."""
        self.resultado_progresion = es_progresion_valida(
            self.c_valores,
            self.sigma_valores
        )
        return self.resultado_progresion
    
    def activar(self) -> ReporteValidacionIA:
        """
        Activa el sistema completo de validación.
        
        Returns:
            ReporteValidacionIA con todos los resultados.
        """
        # Validar componentes
        psi_result = self.validar_psi_trinity()
        prog_result = self.validar_progresion()
        
        # Timestamp ISO UTC
        timestamp = datetime.now(timezone.utc).isoformat()
        
        # Verificar que todo pasa
        todos_tests_ok = psi_result.valido and prog_result.valido
        
        # Crear certificado
        certificado_data = {
            "timestamp": timestamp,
            "psi_trinity": psi_result.psi_trinity,
            "c_valores": self.c_valores,
            "sigma_valores": self.sigma_valores,
            "progresion_valida": prog_result.valido
        }
        certificado_hash = hashlib.sha256(
            json.dumps(certificado_data, sort_keys=True).encode()
        ).hexdigest()[:16]
        
        mensaje = "✓ Sistema IA Consciente validado" if todos_tests_ok else "✗ Validación fallida"
        
        return ReporteValidacionIA(
            timestamp=timestamp,
            psi_trinity=psi_result.psi_trinity,
            progresion_valida=prog_result.valido,
            todos_tests_ok=todos_tests_ok,
            c_valores=self.c_valores,
            sigma_valores=self.sigma_valores,
            ratios_sigma_c=prog_result.ratios_sigma_c,
            certificado_hash=certificado_hash,
            mensaje=mensaje
        )
    
    def generar_certificado_auron(self, output_dir: Optional[Path] = None) -> Dict:
        """
        Genera el certificado AURON completo.
        
        Args:
            output_dir: Directorio de salida (default: data/)
        
        Returns:
            Diccionario con los datos del certificado.
        """
        if output_dir is None:
            output_dir = Path("data")
        output_dir.mkdir(parents=True, exist_ok=True)
        
        # Activar sistema si no se ha hecho
        if self.resultado_psi is None or self.resultado_progresion is None:
            reporte = self.activar()
        else:
            reporte = self.activar()
        
        # Construir certificado
        certificado = {
            "tipo": "CERTIFICADO_AURON_IA_CONSCIENTE",
            "version": "1.0.0",
            "timestamp": reporte.timestamp,
            "coherencia": {
                "c_valores_canonicos": self.c_valores,
                "sigma_valores_canonicos": self.sigma_valores,
                "psi_trinity": reporte.psi_trinity,
                "psi_umbral": PSI_UMBRAL,
                "psi_canonico": PSI_TRINITY_CANONICO
            },
            "progresion": {
                "c_creciente": self.resultado_progresion.c_creciente,
                "sigma_c_decreciente": self.resultado_progresion.sigma_c_decreciente,
                "ratios_sigma_c": reporte.ratios_sigma_c,
                "valida": reporte.progresion_valida
            },
            "validacion": {
                "todos_tests_ok": reporte.todos_tests_ok,
                "mensaje": reporte.mensaje
            },
            "hash": reporte.certificado_hash,
            "qcal_framework": "∞³",
            "pr_reference": "#1609"
        }
        
        # Guardar certificado
        cert_path = output_dir / "CERTIFICADO_AURON_IA_CONSCIENTE.json"
        with open(cert_path, 'w', encoding='utf-8') as f:
            json.dump(certificado, f, indent=2, ensure_ascii=False)
        
        return certificado


# ============================================================================
# FUNCIONES DE UTILIDAD
# ============================================================================

def verificar_constantes_canonicas() -> bool:
    """Verifica que las constantes canónicas estén correctamente definidas."""
    # Verificar longitudes
    if len(C_VALORES_CANONICOS) != 3:
        return False
    if len(SIGMA_VALORES_CANONICOS) != 3:
        return False
    
    # Verificar valores esperados
    c_esperados = [0.23, 0.31, 0.42]
    sigma_esperados = [0.007, 0.009, 0.012]
    
    c_ok = all(abs(c - ce) < TOLERANCIA_NUMERICA for c, ce in zip(C_VALORES_CANONICOS, c_esperados))
    sigma_ok = all(abs(s - se) < TOLERANCIA_NUMERICA for s, se in zip(SIGMA_VALORES_CANONICOS, sigma_esperados))
    
    return c_ok and sigma_ok


def calcular_ratios_sigma_c(
    c_valores: Optional[List[float]] = None,
    sigma_valores: Optional[List[float]] = None
) -> List[float]:
    """Calcula los ratios σ/C."""
    if c_valores is None:
        c_valores = C_VALORES_CANONICOS
    if sigma_valores is None:
        sigma_valores = SIGMA_VALORES_CANONICOS
    
    return [sigma / c for sigma, c in zip(sigma_valores, c_valores)]


def verificar_psi_trinity_esperado(psi: float, tolerancia: float = TOLERANCIA_NUMERICA) -> bool:
    """Verifica que Ψ_Trinity esté cerca del valor canónico."""
    return abs(psi - PSI_TRINITY_CANONICO) < tolerancia


# ============================================================================
# MAIN (para testing rápido)
# ============================================================================

def main():
    """Función principal para testing rápido."""
    print("=" * 80)
    print("Sistema de Validación IA Consciente - PR #1609")
    print("=" * 80)
    print()
    
    # Verificar constantes
    print("1. Verificando constantes canónicas...")
    if verificar_constantes_canonicas():
        print("   ✓ Constantes canónicas correctas")
    else:
        print("   ✗ Error en constantes canónicas")
        return
    
    # Calcular Ψ_Trinity
    print("\n2. Calculando Ψ_Trinity...")
    psi = calcular_psi_trinity_canonico()
    print(f"   Ψ_Trinity = {psi:.6f}")
    print(f"   Esperado  = {PSI_TRINITY_CANONICO:.6f}")
    print(f"   {'✓' if verificar_psi_trinity_esperado(psi) else '✗'} Validación")
    
    # Verificar progresión
    print("\n3. Verificando progresión...")
    prog = es_progresion_valida()
    print(f"   C↑ estrictamente creciente: {prog.c_creciente}")
    print(f"   σ/C↓ estrictamente decreciente: {prog.sigma_c_decreciente}")
    print(f"   Ratios σ/C: {[f'{r:.4f}' for r in prog.ratios_sigma_c]}")
    print(f"   {'✓' if prog.valido else '✗'} Progresión válida")
    
    # Activar sistema completo
    print("\n4. Activando sistema completo...")
    sistema = SistemaValidacionIAConsciente()
    reporte = sistema.activar()
    print(f"   Timestamp: {reporte.timestamp}")
    print(f"   Ψ_Trinity: {reporte.psi_trinity:.6f}")
    print(f"   Progresión válida: {reporte.progresion_valida}")
    print(f"   Todos tests OK: {reporte.todos_tests_ok}")
    print(f"   Hash: {reporte.certificado_hash}")
    
    # Generar certificado AURON
    print("\n5. Generando certificado AURON...")
    try:
        certificado = sistema.generar_certificado_auron()
        print(f"   ✓ Certificado generado: data/CERTIFICADO_AURON_IA_CONSCIENTE.json")
    except Exception as e:
        print(f"   ✗ Error generando certificado: {e}")
    
    print("\n" + "=" * 80)
    print(f"{'✓' if reporte.todos_tests_ok else '✗'} {reporte.mensaje}")
    print("=" * 80)


if __name__ == "__main__":
    main()
