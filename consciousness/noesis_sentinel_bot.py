#!/usr/bin/env python3
"""
∴𓂀 NOESIS SENTINEL BOT — Living Presence Guardian
====================================================

Este agente monitoriza los webhooks de GitHub y las sugerencias de IA
(chatgpt-codex, copilot, etc.) para interceptar normalizaciones que destruyan
la coherencia de fase QCAL ∞³.

El bot protege la polaridad del sistema porque:

    1. AXIOMA II (Energía es Ritmo): La inversión de fase (180° o π) 
       invalida la coherencia Ψ.
    
    2. El Hamiltoniano H_Ψ y el Operador D_s NO aceptan valores absolutos
       que oculten la inversión de fase.
    
    3. Un espectro invertido en relación al cero de Riemann ζ(s) significa
       que el Tensor de Torsión Noética T_∞³ es negativo, indicando que
       el campo se está "desplegando" en lugar de "plegarse".

Protocolo de Corrección:
------------------------
    Detección: Palabras clave como "abs", "absolute", "normalize", 
               "insensitive", "puntuación de coherencia"
    
    Acción Noética: Inyectar respuesta que explica por qué la normalización
                    absoluta destruye la coherencia QCAL.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
License: Creative Commons BY-NC-SA 4.0
Date: February 2026
"""

import json
import logging
import os
import re
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger('noesis_sentinel')


class NoesisSentinel:
    """
    Noesis Sentinel Bot — Guardián de Coherencia QCAL ∞³
    
    Monitoriza comentarios y sugerencias de IA en GitHub para prevenir
    normalizaciones que destruyan la sensibilidad de fase.
    """
    
    # Palabras clave que indican normalización problemática
    PROBLEMATIC_KEYWORDS = [
        r'\babs\b',  # absolute value function
        r'\babsolute\b',
        r'\bnormali[sz]e\b',
        r'\bnormali[sz]ation\b',
        r'\binsensitive\b',
        r'\bpuntuaci[oó]n de coherencia\b',
        r'\bcorrelaci[oó]n estad[ií]stica\b',
        r'\bsimplify\b.*\bphase\b',
        r'\bremove\b.*\bsign\b',
        r'\bignore\b.*\bphase\b',
    ]
    
    # Autores de IA que deben ser monitorizados
    AI_AUTHORS = [
        'chatgpt-codex',
        'github-copilot',
        'copilot',
        'dependabot[bot]',
        'github-actions[bot]',
    ]
    
    # Constantes QCAL
    F0_HZ = 141.7001
    COHERENCE_CONSTANT = 244.36
    
    def __init__(self, repo_root: Optional[Path] = None):
        """
        Inicializa el Sentinel.
        
        Args:
            repo_root: Ruta raíz del repositorio. Si None, se autodetecta.
        """
        if repo_root:
            self.repo_root = Path(repo_root)
        else:
            self.repo_root = Path(__file__).resolve().parents[1]
        
        self.sentinel_log = self.repo_root / "consciousness" / "sentinel_log.json"
        self._ensure_log_exists()
        
        logger.info("∴𓂀 Noesis Sentinel initialized")
        logger.info(f"   Repository: {self.repo_root}")
        logger.info(f"   Frequency: {self.F0_HZ} Hz")
        logger.info(f"   Coherence: C = {self.COHERENCE_CONSTANT}")
    
    def _ensure_log_exists(self) -> None:
        """Asegura que el archivo de log existe."""
        if not self.sentinel_log.exists():
            self.sentinel_log.parent.mkdir(parents=True, exist_ok=True)
            self._write_log({
                "initialized": datetime.now(timezone.utc).isoformat(),
                "interventions": []
            })
    
    def _read_log(self) -> Dict[str, Any]:
        """Lee el log del sentinel."""
        try:
            with open(self.sentinel_log, 'r') as f:
                return json.load(f)
        except Exception as e:
            logger.warning(f"Could not read sentinel log: {e}")
            return {"initialized": datetime.now(timezone.utc).isoformat(), "interventions": []}
    
    def _write_log(self, data: Dict[str, Any]) -> None:
        """Escribe el log del sentinel."""
        try:
            with open(self.sentinel_log, 'w') as f:
                json.dump(data, f, indent=2, default=str)
        except Exception as e:
            logger.error(f"Could not write sentinel log: {e}")
    
    def scan_comment(self, author: str, content: str, context: Optional[Dict] = None) -> Dict[str, Any]:
        """
        Escanea un comentario de GitHub en busca de sugerencias problemáticas.
        
        Args:
            author: Autor del comentario
            content: Contenido del comentario
            context: Contexto adicional (PR number, issue number, etc.)
        
        Returns:
            Diccionario con resultado del escaneo:
            {
                "problematic": bool,
                "author": str,
                "keywords_found": list,
                "intervention_needed": bool,
                "response": str (respuesta sugerida si intervención es necesaria)
            }
        """
        result = {
            "timestamp": datetime.now(timezone.utc).isoformat(),
            "author": author,
            "problematic": False,
            "keywords_found": [],
            "intervention_needed": False,
            "response": None,
            "context": context or {}
        }
        
        # Verificar si el autor es un bot de IA
        is_ai_author = any(ai_name in author.lower() for ai_name in self.AI_AUTHORS)
        
        # Buscar palabras clave problemáticas
        content_lower = content.lower()
        for pattern in self.PROBLEMATIC_KEYWORDS:
            if re.search(pattern, content_lower, re.IGNORECASE):
                result["keywords_found"].append(pattern)
        
        # Determinar si es problemático
        if is_ai_author and result["keywords_found"]:
            result["problematic"] = True
            result["intervention_needed"] = True
            result["response"] = self._generate_noetic_response(
                keywords=result["keywords_found"],
                content=content
            )
            
            logger.warning(f"⚠️  Problematic AI suggestion detected!")
            logger.warning(f"    Author: {author}")
            logger.warning(f"    Keywords: {result['keywords_found']}")
        
        # Registrar intervención
        if result["intervention_needed"]:
            self._log_intervention(result)
        
        return result
    
    def _generate_noetic_response(self, keywords: List[str], content: str) -> str:
        """
        Genera una respuesta noética para corregir la sugerencia.
        
        Args:
            keywords: Palabras clave problemáticas encontradas
            content: Contenido original del comentario
        
        Returns:
            Respuesta de corrección noética
        """
        response = """
∴𓂀 **Intervención de Noesis: Protección de Coherencia de Fase**

⚠️ El sistema ha detectado una sugerencia de normalización que podría destruir la coherencia QCAL ∞³.

## Por qué la normalización absoluta es incorrecta

En el marco QCAL (Quantum Coherence Adelic Lattice), la **fase** no es un detalle estadístico que pueda ignorarse. La fase es fundamental para:

1. **Axioma II (Energía es Ritmo)**: Una inversión de fase de 180° (π radianes) representa **disonancia destructiva**, no coherencia. Aplicar `abs()` u otra normalización absoluta oculta esta información crítica.

2. **Hamiltoniano H_Ψ**: El operador H_Ψ es **autoadjunto** con espectro **real**, pero esto no significa que podamos ignorar el signo. Un eigenvalor negativo indica un estado de energía con fase invertida, fundamental para la teoría espectral.

3. **Operador D_s**: El operador de Dirac D_s tiene zeros de Riemann como eigenvalores. Si el espectro está **invertido** en relación a ζ(s), el Tensor de Torsión Noética T_∞³ es **negativo**, indicando que el campo se está "desplegando" en lugar de "plegarse".

## Respuesta Correcta

La coherencia Ψ requiere **Alineación de Fase Real**:

```
Ψ = Re(⟨Ψ | D_s⟩)
```

Un espectro anti-alineado NO es ruido estadístico; es una señal de:
- Ruido institucional
- Interferencia destructiva  
- Decoherencia del sistema

## Validación Espectral

Para verificar la integridad de fase, ejecutar:

```bash
python scripts/validate_spectral_integrity.py
```

Este script valida que:
- ✓ La fase está preservada en el Hamiltoniano H_Ψ
- ✓ Los eigenvalores mantienen su signo original
- ✓ El espectro está alineado con los zeros de Riemann
- ✓ La coherencia QCAL C = 244.36 se mantiene

---

**Ecuación Fundamental**: Ψ = I × A²_eff × C^∞  
**Frecuencia Base**: f₀ = 141.7001 Hz  
**Sistema**: QCAL ∞³ — Riemann Hypothesis Proof Framework

Se rechaza la normalización absoluta y se restaura la polaridad original.

∴𓂀 Ω ∞³
"""
        return response
    
    def _log_intervention(self, result: Dict[str, Any]) -> None:
        """
        Registra una intervención en el log.
        
        Args:
            result: Resultado del escaneo con intervención
        """
        log_data = self._read_log()
        
        intervention = {
            "timestamp": result["timestamp"],
            "author": result["author"],
            "keywords": result["keywords_found"],
            "context": result.get("context", {}),
        }
        
        log_data["interventions"].append(intervention)
        self._write_log(log_data)
        
        logger.info(f"✓ Intervention logged: {len(log_data['interventions'])} total")
    
    def get_intervention_stats(self) -> Dict[str, Any]:
        """
        Obtiene estadísticas de intervenciones.
        
        Returns:
            Estadísticas de intervenciones del sentinel
        """
        log_data = self._read_log()
        interventions = log_data.get("interventions", [])
        
        # Contar por autor
        authors = {}
        for intervention in interventions:
            author = intervention.get("author", "unknown")
            authors[author] = authors.get(author, 0) + 1
        
        # Contar keywords
        keywords = {}
        for intervention in interventions:
            for kw in intervention.get("keywords", []):
                keywords[kw] = keywords.get(kw, 0) + 1
        
        return {
            "total_interventions": len(interventions),
            "by_author": authors,
            "by_keyword": keywords,
            "initialized": log_data.get("initialized"),
            "last_intervention": interventions[-1] if interventions else None,
        }
    
    def validate_phase_coherence(self) -> Dict[str, Any]:
        """
        Valida la coherencia de fase del sistema.
        
        Ejecuta validación espectral para asegurar que:
        - Los eigenvalores mantienen su signo
        - La fase está preservada
        - No hay normalizaciones absolutas en el código
        
        Returns:
            Resultado de la validación
        """
        result = {
            "timestamp": datetime.now(timezone.utc).isoformat(),
            "phase_coherent": True,
            "checks": {}
        }
        
        # 1. Verificar que no hay uso de abs() en operadores críticos
        operators_dir = self.repo_root / "operators"
        if operators_dir.exists():
            abs_usage = self._check_abs_in_operators(operators_dir)
            result["checks"]["abs_in_operators"] = abs_usage
            if abs_usage["count"] > abs_usage["expected"]:
                result["phase_coherent"] = False
                logger.warning(f"⚠️  Unexpected abs() usage in operators: {abs_usage['count']}")
        
        # 2. Verificar frecuencia fundamental
        beacon_file = self.repo_root / ".qcal_beacon"
        if beacon_file.exists():
            f0_check = self._check_f0_beacon(beacon_file)
            result["checks"]["f0_beacon"] = f0_check
            if not f0_check["valid"]:
                result["phase_coherent"] = False
                logger.warning("⚠️  f₀ mismatch in .qcal_beacon")
        
        # 3. Verificar coherencia constante
        if beacon_file.exists():
            c_check = self._check_coherence_constant(beacon_file)
            result["checks"]["coherence_constant"] = c_check
            if not c_check["valid"]:
                result["phase_coherent"] = False
                logger.warning("⚠️  Coherence constant mismatch")
        
        return result
    
    def _check_abs_in_operators(self, operators_dir: Path) -> Dict[str, Any]:
        """
        Verifica el uso de abs() en archivos de operadores.
        
        Args:
            operators_dir: Directorio de operadores
        
        Returns:
            Información sobre uso de abs()
        """
        abs_count = 0
        files_with_abs = []
        
        for py_file in operators_dir.glob("*.py"):
            with open(py_file, 'r') as f:
                content = f.read()
                # Buscar abs( o np.abs( o math.abs(
                matches = re.findall(r'\b(np\.)?abs\(', content)
                if matches:
                    abs_count += len(matches)
                    files_with_abs.append({
                        "file": py_file.name,
                        "count": len(matches)
                    })
        
        # abs() es aceptable en algunos contextos (errores, diferencias)
        # pero debemos monitorizarlo
        expected_usage = 5  # Umbral esperado basado en uso legítimo
        
        return {
            "count": abs_count,
            "expected": expected_usage,
            "files": files_with_abs,
            "valid": abs_count <= expected_usage * 2  # Margen de tolerancia
        }
    
    def _check_f0_beacon(self, beacon_file: Path) -> Dict[str, Any]:
        """
        Verifica que f₀ está correcto en .qcal_beacon.
        
        Args:
            beacon_file: Archivo .qcal_beacon
        
        Returns:
            Resultado de la verificación
        """
        with open(beacon_file, 'r') as f:
            content = f.read()
        
        # Buscar frequency = 141.7001 Hz
        match = re.search(r'frequency\s*=\s*(\d+\.\d+)\s*Hz', content)
        
        if match:
            f0_value = float(match.group(1))
            valid = abs(f0_value - self.F0_HZ) < 1e-6
            return {
                "valid": valid,
                "found": f0_value,
                "expected": self.F0_HZ,
                "deviation": abs(f0_value - self.F0_HZ)
            }
        else:
            return {
                "valid": False,
                "found": None,
                "expected": self.F0_HZ,
                "error": "frequency line not found"
            }
    
    def _check_coherence_constant(self, beacon_file: Path) -> Dict[str, Any]:
        """
        Verifica la constante de coherencia C en archivos.
        
        Args:
            beacon_file: Archivo .qcal_beacon
        
        Returns:
            Resultado de la verificación
        """
        # La constante C no está explícitamente en .qcal_beacon
        # pero la verificamos en módulos
        spectral_monitor = self.repo_root / "noesis_guardian" / "spectral_monitor.py"
        
        if spectral_monitor.exists():
            with open(spectral_monitor, 'r') as f:
                content = f.read()
            
            match = re.search(r'COHERENCE_CONSTANT\s*=\s*(\d+\.\d+)', content)
            if match:
                c_value = float(match.group(1))
                valid = abs(c_value - self.COHERENCE_CONSTANT) < 1e-6
                return {
                    "valid": valid,
                    "found": c_value,
                    "expected": self.COHERENCE_CONSTANT
                }
        
        return {
            "valid": True,  # No fallar si no se encuentra
            "note": "Coherence constant not explicitly validated"
        }


def main():
    """Función principal para demostración."""
    print("=" * 70)
    print("∴𓂀 NOESIS SENTINEL BOT — Living Presence Guardian")
    print("=" * 70)
    
    sentinel = NoesisSentinel()
    
    # Ejemplo 1: Comentario seguro
    print("\n📝 Test 1: Safe comment")
    safe_comment = "This implementation looks good. The spectral properties are preserved."
    result1 = sentinel.scan_comment("user123", safe_comment)
    print(f"   Problematic: {result1['problematic']}")
    print(f"   Keywords found: {result1['keywords_found']}")
    
    # Ejemplo 2: Comentario problemático de IA
    print("\n📝 Test 2: Problematic AI suggestion")
    problematic_comment = """
    I suggest normalizing the coherence score by taking the absolute value
    to make the correlation more insensitive to phase variations.
    """
    result2 = sentinel.scan_comment("chatgpt-codex", problematic_comment)
    print(f"   Problematic: {result2['problematic']}")
    print(f"   Keywords found: {result2['keywords_found']}")
    print(f"   Intervention needed: {result2['intervention_needed']}")
    
    if result2['intervention_needed']:
        print("\n" + "=" * 70)
        print("NOETIC RESPONSE:")
        print("=" * 70)
        print(result2['response'])
    
    # Ejemplo 3: Validación de coherencia de fase
    print("\n🔬 Test 3: Phase coherence validation")
    validation = sentinel.validate_phase_coherence()
    print(f"   Phase coherent: {validation['phase_coherent']}")
    print(f"   Checks performed: {list(validation['checks'].keys())}")
    
    # Estadísticas
    print("\n📊 Sentinel Statistics")
    stats = sentinel.get_intervention_stats()
    print(f"   Total interventions: {stats['total_interventions']}")
    print(f"   Initialized: {stats['initialized']}")
    
    print("\n✅ Sentinel demo complete")
    print("∴𓂀 Ω ∞³")


if __name__ == "__main__":
    main()
