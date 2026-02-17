#!/usr/bin/env python3
"""
NOESIS DIAGNOSTIC - Verifica por qué no se eliminan sorrys
"""

import subprocess
import json
from pathlib import Path
import sys

def check_sorries():
    """Cuenta sorrys directamente con grep"""
    try:
        result = subprocess.run(
            ["grep", "-r", "sorry", "--include=*.lean", "formalization/lean/"],
            capture_output=True,
            text=True
        )
        return result.stdout.count('\n')
    except Exception as e:
        print(f"❌ Error contando sorries: {e}")
        return 0

def check_trivial_candidates():
    """Busca candidatos triviales no resueltos (estimación aproximada)"""
    try:
        # Primero buscar todos los sorries
        result1 = subprocess.run(
            ["grep", "-r", "sorry", "--include=*.lean", "formalization/lean/"],
            capture_output=True,
            text=True
        )
        
        # Luego filtrar los que tienen patrones triviales en el contexto
        # Nota: Esta es una estimación - puede incluir falsos positivos si el
        # patrón está en un comentario o contexto diferente en la misma línea
        trivial_patterns = ['rfl', 'trivial', 'simp', 'norm_num']
        candidates = 0
        
        for line in result1.stdout.split('\n'):
            if 'sorry' in line:
                line_lower = line.lower()
                for pattern in trivial_patterns:
                    if pattern in line_lower:
                        candidates += 1
                        break
        
        return candidates
    except Exception as e:
        print(f"❌ Error buscando candidatos triviales: {e}")
        return 0

def main():
    print("🔍 NOESIS DIAGNOSTIC - Verificando sistema...")
    print()
    
    # 1. Verificar conteo de sorrys
    sorries = check_sorries()
    print(f"📊 Sorries totales: {sorries}")
    
    # 2. Verificar candidatos triviales
    trivial_candidates = check_trivial_candidates()
    print(f"⚠️ Candidatos triviales no resueltos: {trivial_candidates}")
    
    # 3. Verificar archivo de aprendizaje
    learning = Path('.auron_learning.json')
    if learning.exists():
        try:
            with open(learning) as f:
                data = json.load(f)
            print(f"🧠 Patrones aprendidos: {len(data.get('patterns', {}))}")
            total_success = data.get('total_success', 0)
            total_attempts = data.get('total_attempts', 1)
            if total_attempts > 0:
                success_rate = (total_success / total_attempts) * 100
                print(f"📈 Tasa éxito acumulada: {total_success}/{total_attempts} ({success_rate:.1f}%)")
            else:
                print(f"📈 Sin intentos registrados aún")
        except Exception as e:
            print(f"❌ Error leyendo archivo de aprendizaje: {e}")
    else:
        print("❌ Archivo de aprendizaje no encontrado")
    
    # 4. Verificar AMDA report
    amda = Path('amda_report_v2.json')
    if amda.exists():
        try:
            with open(amda) as f:
                data = json.load(f)
            by_category = data.get('category_distribution', {})
            print(f"📊 Clasificación actual:")
            for cat, stats in sorted(by_category.items(), key=lambda x: x[1].get('count', 0), reverse=True):
                count = stats.get('count', 0)
                percentage = stats.get('percentage', 0)
                print(f"   - {cat}: {count} ({percentage:.1f}%)")
        except Exception as e:
            print(f"❌ Error leyendo reporte AMDA: {e}")
    else:
        print("❌ Reporte AMDA no encontrado")
    
    print()
    print("🔧 RECOMENDACIONES:")
    
    if trivial_candidates > 0:
        print(f"   • Resolver {trivial_candidates} candidatos triviales manualmente como prueba")
    
    if learning.exists():
        try:
            with open(learning) as f:
                data = json.load(f)
            if len(data.get('patterns', {})) < 10:
                print("   • Pocos patrones aprendidos - revisar clasificación AMDA")
        except:
            pass
    
    if sorries > 2000:
        print("   • Sistema no progresa - revisar lógica de transformación")
    
    if not amda.exists():
        print("   • Ejecutar AMDA primero para generar reporte de análisis")
    
    return 0

if __name__ == "__main__":
    sys.exit(main())
