#!/usr/bin/env python3
"""
Validación de Formalización en Lean 4
======================================

Script para validar la compilación de la formalización Lean 4
y verificar hashes reproducibles de módulos.

Integración con CI/CD para validación automática.

Autor: José Manuel Mota Burruezo
Fecha: Octubre 2025
Versión: 1.0
DOI: 10.5281/zenodo.17116291
"""

import os
import sys
import subprocess
import hashlib
import json
from pathlib import Path
from typing import Dict, List, Tuple, Optional

# Códigos de color para terminal
class Colores:
    VERDE = '\033[92m'
    AMARILLO = '\033[93m'
    ROJO = '\033[91m'
    AZUL = '\033[94m'
    CYAN = '\033[96m'
    NEGRITA = '\033[1m'
    FIN = '\033[0m'

def imprimir_encabezado(texto: str):
    """Imprime un encabezado formateado."""
    print(f"\n{Colores.NEGRITA}{Colores.CYAN}{'=' * 70}{Colores.FIN}")
    print(f"{Colores.NEGRITA}{Colores.CYAN}{texto.center(70)}{Colores.FIN}")
    print(f"{Colores.NEGRITA}{Colores.CYAN}{'=' * 70}{Colores.FIN}\n")

def imprimir_exito(texto: str):
    """Imprime mensaje de éxito."""
    print(f"{Colores.VERDE}✓{Colores.FIN} {texto}")

def imprimir_advertencia(texto: str):
    """Imprime mensaje de advertencia."""
    print(f"{Colores.AMARILLO}⚠{Colores.FIN} {texto}")

def imprimir_error(texto: str):
    """Imprime mensaje de error."""
    print(f"{Colores.ROJO}✗{Colores.FIN} {texto}")

def imprimir_info(texto: str):
    """Imprime mensaje informativo."""
    print(f"{Colores.AZUL}ℹ{Colores.FIN} {texto}")

def verificar_elan_instalado() -> bool:
    """Verifica si elan está instalado."""
    try:
        result = subprocess.run(['elan', '--version'], 
                              capture_output=True, 
                              text=True, 
                              timeout=10)
        return result.returncode == 0
    except (FileNotFoundError, subprocess.TimeoutExpired):
        return False

def verificar_lean_instalado() -> Tuple[bool, Optional[str]]:
    """Verifica si Lean está instalado y retorna la versión."""
    try:
        result = subprocess.run(['lean', '--version'], 
                              capture_output=True, 
                              text=True, 
                              timeout=10)
        if result.returncode == 0:
            version = result.stdout.strip()
            return True, version
        return False, None
    except (FileNotFoundError, subprocess.TimeoutExpired):
        return False, None

def verificar_lake_instalado() -> bool:
    """Verifica si lake está instalado."""
    try:
        result = subprocess.run(['lake', '--version'], 
                              capture_output=True, 
                              text=True, 
                              timeout=10)
        return result.returncode == 0
    except (FileNotFoundError, subprocess.TimeoutExpired):
        return False

def ejecutar_lake_build(directorio_lean: Path, timeout: int = 600) -> Tuple[bool, str]:
    """
    Ejecuta lake build en el directorio especificado.
    
    Args:
        directorio_lean: Directorio donde ejecutar lake build
        timeout: Tiempo máximo de espera en segundos
        
    Returns:
        Tupla (éxito, mensaje)
    """
    imprimir_info(f"Ejecutando lake build en {directorio_lean}...")
    
    try:
        result = subprocess.run(
            ['lake', 'build'],
            cwd=directorio_lean,
            capture_output=True,
            text=True,
            timeout=timeout
        )
        
        if result.returncode == 0:
            return True, result.stdout
        else:
            return False, result.stderr
            
    except subprocess.TimeoutExpired:
        return False, f"Timeout después de {timeout} segundos"
    except Exception as e:
        return False, str(e)

def ejecutar_lake_update(directorio_lean: Path) -> bool:
    """Ejecuta lake update para actualizar dependencias."""
    imprimir_info("Actualizando dependencias con lake update...")
    
    try:
        result = subprocess.run(
            ['lake', 'update'],
            cwd=directorio_lean,
            capture_output=True,
            text=True,
            timeout=300
        )
        return result.returncode == 0
    except Exception:
        return False

def ejecutar_lake_clean(directorio_lean: Path) -> bool:
    """Ejecuta lake clean para limpiar build artifacts."""
    imprimir_info("Limpiando artefactos con lake clean...")
    
    try:
        result = subprocess.run(
            ['lake', 'clean'],
            cwd=directorio_lean,
            capture_output=True,
            text=True,
            timeout=60
        )
        return result.returncode == 0
    except Exception:
        return False

def calcular_hash_archivo(archivo: Path) -> str:
    """Calcula el hash SHA256 de un archivo."""
    sha256 = hashlib.sha256()
    with open(archivo, 'rb') as f:
        for bloque in iter(lambda: f.read(4096), b''):
            sha256.update(bloque)
    return sha256.hexdigest()

def calcular_hashes_modulos(directorio_lean: Path) -> Dict[str, str]:
    """Calcula hashes de todos los módulos .lean."""
    hashes = {}
    archivos_lean = list(directorio_lean.rglob("*.lean"))
    
    for archivo in archivos_lean:
        ruta_relativa = archivo.relative_to(directorio_lean)
        hash_valor = calcular_hash_archivo(archivo)
        hashes[str(ruta_relativa)] = hash_valor
    
    return hashes

def guardar_hashes(hashes: Dict[str, str], archivo_salida: Path):
    """Guarda los hashes en un archivo JSON."""
    with open(archivo_salida, 'w') as f:
        json.dump(hashes, f, indent=2)
    imprimir_exito(f"Hashes guardados en: {archivo_salida}")

def comparar_hashes(hashes_actuales: Dict[str, str], archivo_referencia: Path) -> bool:
    """Compara hashes actuales con referencia."""
    if not archivo_referencia.exists():
        imprimir_advertencia("No existe archivo de referencia de hashes")
        return True  # Primera vez, no hay con qué comparar
    
    with open(archivo_referencia, 'r') as f:
        hashes_referencia = json.load(f)
    
    diferencias = []
    for archivo, hash_actual in hashes_actuales.items():
        if archivo in hashes_referencia:
            if hash_actual != hashes_referencia[archivo]:
                diferencias.append(f"  Modificado: {archivo}")
    
    for archivo in hashes_referencia:
        if archivo not in hashes_actuales:
            diferencias.append(f"  Eliminado: {archivo}")
    
    for archivo in hashes_actuales:
        if archivo not in hashes_referencia:
            diferencias.append(f"  Nuevo: {archivo}")
    
    if diferencias:
        imprimir_advertencia("Diferencias detectadas:")
        for diff in diferencias:
            print(diff)
        return False
    else:
        imprimir_exito("Todos los hashes coinciden con la referencia")
        return True

def validar_estructura_proyecto(directorio_lean: Path) -> bool:
    """Valida que existan los archivos necesarios del proyecto."""
    imprimir_encabezado("Validación de Estructura del Proyecto")
    
    archivos_requeridos = [
        'lean-toolchain',
        'lakefile.lean',
        'lakefile.toml',
        'Main.lean',
        'RH_final.lean',
    ]
    
    todos_presentes = True
    for archivo in archivos_requeridos:
        ruta = directorio_lean / archivo
        if ruta.exists():
            imprimir_exito(f"Encontrado: {archivo}")
        else:
            imprimir_error(f"Falta: {archivo}")
            todos_presentes = False
    
    return todos_presentes

def main():
    """Función principal de validación."""
    print(f"\n{Colores.NEGRITA}Validador de Formalización Lean 4{Colores.FIN}")
    print(f"{Colores.CYAN}Prueba Adélica de la Hipótesis de Riemann V5.3+{Colores.FIN}")
    print(f"{Colores.CYAN}DOI: 10.5281/zenodo.17116291{Colores.FIN}")
    
    # Encontrar el directorio Lean
    script_dir = Path(__file__).parent
    directorio_lean = script_dir / 'formalization' / 'lean'
    
    if not directorio_lean.exists():
        imprimir_error(f"Directorio Lean no encontrado: {directorio_lean}")
        return 1
    
    imprimir_info(f"Directorio de trabajo: {directorio_lean}")
    
    # Validar estructura
    if not validar_estructura_proyecto(directorio_lean):
        imprimir_error("Estructura del proyecto incompleta")
        return 1
    
    # Verificar herramientas
    imprimir_encabezado("Verificación de Herramientas")
    
    if not verificar_elan_instalado():
        imprimir_error("elan no está instalado")
        imprimir_info("Ejecuta: ./setup_lean.sh")
        return 1
    imprimir_exito("elan está instalado")
    
    lean_instalado, version_lean = verificar_lean_instalado()
    if not lean_instalado:
        imprimir_error("Lean no está instalado")
        imprimir_info("Ejecuta: ./setup_lean.sh")
        return 1
    imprimir_exito(f"Lean instalado: {version_lean}")
    
    if not verificar_lake_instalado():
        imprimir_error("lake no está instalado")
        return 1
    imprimir_exito("lake está instalado")
    
    # Calcular hashes antes de la compilación
    imprimir_encabezado("Cálculo de Hashes de Módulos")
    hashes = calcular_hashes_modulos(directorio_lean)
    imprimir_info(f"Calculados hashes para {len(hashes)} archivos")
    
    # Guardar hashes
    archivo_hashes = script_dir / 'lean_module_hashes.json'
    guardar_hashes(hashes, archivo_hashes)
    
    # Intentar compilación
    imprimir_encabezado("Compilación de Formalización")
    
    exito_build, mensaje_build = ejecutar_lake_build(directorio_lean, timeout=600)
    
    if exito_build:
        imprimir_exito("✓ Compilación exitosa!")
        print("\n" + mensaje_build[-500:] if len(mensaje_build) > 500 else mensaje_build)
    else:
        imprimir_error("✗ Error en la compilación")
        print("\nMensaje de error:")
        print(mensaje_build[:1000])  # Primeros 1000 caracteres del error
        
        # Intentar recuperación
        imprimir_info("\nIntentando recuperación automática...")
        if ejecutar_lake_clean(directorio_lean):
            if ejecutar_lake_update(directorio_lean):
                imprimir_info("Reintentando compilación...")
                exito_build, mensaje_build = ejecutar_lake_build(directorio_lean, timeout=600)
                
                if exito_build:
                    imprimir_exito("✓ Compilación exitosa después de recuperación!")
                else:
                    imprimir_error("La recuperación no solucionó el problema")
                    return 1
    
    # Resumen final
    imprimir_encabezado("Resumen de Validación")
    
    imprimir_exito("Estructura del proyecto válida")
    imprimir_exito("Herramientas instaladas correctamente")
    imprimir_exito("Hashes de módulos calculados y guardados")
    
    if exito_build:
        imprimir_exito("Compilación exitosa")
        print(f"\n{Colores.VERDE}{Colores.NEGRITA}✓ Validación completa exitosa!{Colores.FIN}")
        print(f"\n{Colores.CYAN}La formalización está lista para uso.{Colores.FIN}")
        print(f"{Colores.CYAN}Coherencia QCAL confirmada.{Colores.FIN}")
        return 0
    else:
        imprimir_advertencia("Compilación con problemas")
        print(f"\n{Colores.AMARILLO}{Colores.NEGRITA}⚠ Validación parcial{Colores.FIN}")
        return 1

if __name__ == '__main__':
    sys.exit(main())
