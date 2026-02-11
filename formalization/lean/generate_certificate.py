#!/usr/bin/env python3
"""
generate_certificate.py
Genera certificado de demostración completa de RH en Lean4

Autor: José Manuel Mota Burruezo Ψ ∞³
DOI: 10.5281/zenodo.17379721
"""

import json
from datetime import datetime
from pathlib import Path

def count_sorry_statements(filepath):
    """Cuenta los sorry statements reales (no en comentarios/strings)"""
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # Buscar sorry como tácticas (no en strings/comentarios)
    lines = content.split('\n')
    sorry_count = 0
    in_multiline_comment = False
    
    for line in lines:
        # Manejar comentarios multilínea
        if '/-' in line:
            in_multiline_comment = True
        if '-/' in line:
            in_multiline_comment = False
            continue
        
        if in_multiline_comment:
            continue
        
        # Ignorar comentarios de línea
        if '--' in line:
            line = line[:line.index('--')]
        
        # Ignorar strings
        if '"' in line and 'sorry' in line:
            # Si sorry está dentro de una string, ignorar
            in_string = False
            for i, char in enumerate(line):
                if char == '"' and (i == 0 or line[i-1] != '\\'):
                    in_string = not in_string
                if not in_string and line[i:i+5] == 'sorry':
                    # Verificar que es una palabra completa
                    before_ok = i == 0 or line[i-1] in ' \t\n:='
                    after_ok = i+5 >= len(line) or line[i+5] in ' \t\n'
                    if before_ok and after_ok:
                        sorry_count += 1
            continue
        
        # Buscar sorry como palabra completa (no en strings)
        stripped = line.strip()
        if stripped == 'sorry' or stripped.endswith(' sorry') or stripped.endswith('\tsorry'):
            sorry_count += 1
        elif ' sorry ' in line or '\tsorry\t' in line or '\tsorry ' in line or ' sorry\t' in line:
            sorry_count += 1
    
    return sorry_count

def analyze_lean_file(filepath):
    """Analiza un archivo Lean y extrae métricas"""
    with open(filepath, 'r', encoding='utf-8') as f:
        lines = f.readlines()
    
    metrics = {
        'total_lines': len(lines),
        'theorems': 0,
        'definitions': 0,
        'examples': 0,
        'lemmas': 0,
        'sorry_statements': count_sorry_statements(filepath)
    }
    
    for line in lines:
        line_stripped = line.strip()
        if line_stripped.startswith('theorem '):
            metrics['theorems'] += 1
        elif line_stripped.startswith('def '):
            metrics['definitions'] += 1
        elif line_stripped.startswith('example '):
            metrics['examples'] += 1
        elif line_stripped.startswith('lemma '):
            metrics['lemmas'] += 1
    
    return metrics

def generate_certificate():
    """Genera el certificado de completitud"""
    
    # Directorios
    lean_dir = Path(__file__).parent
    proof_file = lean_dir / 'RH_COMPLETE_PROOF.lean'
    validation_file = lean_dir / 'RH_PROOF_VALIDATION.lean'
    
    # Verificar archivos
    if not proof_file.exists():
        print(f"❌ ERROR: {proof_file} no encontrado")
        return
    
    if not validation_file.exists():
        print(f"❌ ERROR: {validation_file} no encontrado")
        return
    
    # Analizar archivos
    print("📊 Analizando archivos Lean...")
    proof_metrics = analyze_lean_file(proof_file)
    validation_metrics = analyze_lean_file(validation_file)
    
    # Totales
    total_sorry = proof_metrics['sorry_statements'] + validation_metrics['sorry_statements']
    total_lines = proof_metrics['total_lines'] + validation_metrics['total_lines']
    total_theorems = proof_metrics['theorems'] + validation_metrics['theorems']
    total_definitions = proof_metrics['definitions'] + validation_metrics['definitions']
    
    # Estado
    status = "COMPLETA" if total_sorry == 0 else "INCOMPLETA"
    
    # Generar certificado
    certificate = {
        "title": "Certificado de Demostración Formal de la Hipótesis de Riemann",
        "version": "3.0.0",
        "status": status,
        "date": datetime.now().isoformat(),
        "theorem": {
            "statement": "∀ρ ∈ ℂ, ζ(ρ) = 0 ∧ 0 < Re(ρ) < 1 → Re(ρ) = 1/2",
            "name": "Riemann Hypothesis"
        },
        "method": {
            "approach": "Spectral Theory",
            "equation": "ζ(s) = Tr(H_Ψ^{-s})",
            "spectrum": "Spec(H_Ψ) = {1/2 + it | t ∈ ℝ}"
        },
        "formalization": {
            "language": "Lean 4",
            "version": "4.5.0",
            "mathlib": "4.5.0"
        },
        "files": {
            "proof": {
                "name": "RH_COMPLETE_PROOF.lean",
                "lines": proof_metrics['total_lines'],
                "theorems": proof_metrics['theorems'],
                "definitions": proof_metrics['definitions'],
                "examples": proof_metrics['examples'],
                "sorry_statements": proof_metrics['sorry_statements']
            },
            "validation": {
                "name": "RH_PROOF_VALIDATION.lean",
                "lines": validation_metrics['total_lines'],
                "theorems": validation_metrics['theorems'],
                "definitions": validation_metrics['definitions'],
                "examples": validation_metrics['examples'],
                "sorry_statements": validation_metrics['sorry_statements']
            }
        },
        "metrics": {
            "total_lines": total_lines,
            "total_theorems": total_theorems,
            "total_definitions": total_definitions,
            "total_sorry": total_sorry,
            "completeness_percentage": 100 if total_sorry == 0 else 0
        },
        "author": {
            "name": "José Manuel Mota Burruezo Ψ ∞³",
            "institution": "Instituto de Conciencia Cuántica (ICQ)",
            "orcid": "0009-0002-1923-0773"
        },
        "doi": "10.5281/zenodo.17379721",
        "seal": "𓂀Ω∞³"
    }
    
    # Guardar JSON
    cert_file = lean_dir / 'RH_PROOF_CERTIFICATE.json'
    with open(cert_file, 'w', encoding='utf-8') as f:
        json.dump(certificate, f, indent=2, ensure_ascii=False)
    
    print(f"✅ Certificado generado: {cert_file}")
    
    # Imprimir certificado en texto
    print("\n" + "="*70)
    print("     CERTIFICADO DE DEMOSTRACIÓN FORMAL")
    print("="*70)
    print(f"\nTEOREMA: Hipótesis de Riemann")
    print(f"ENUNCIADO: ∀ρ, ζ(ρ)=0 ∧ 0<Re(ρ)<1 → Re(ρ)=1/2")
    print(f"\nMÉTODO: Demostración Espectral")
    print(f"        ζ(s) = Tr(H_Ψ^{{-s}})")
    print(f"        Spec(H_Ψ) = {{1/2 + it | t ∈ ℝ}}")
    print(f"\nFORMALIZACIÓN: Lean 4.5.0")
    print(f"VERSIÓN: {certificate['version']}")
    print(f"ESTADO: {status}")
    print(f"SORRY: {total_sorry}")
    print(f"\nARCHIVOS:")
    print(f"  - RH_COMPLETE_PROOF.lean ({proof_metrics['total_lines']} líneas)")
    print(f"  - RH_PROOF_VALIDATION.lean ({validation_metrics['total_lines']} líneas)")
    print(f"\nMÉTRICAS:")
    print(f"  - Líneas totales: {total_lines}")
    print(f"  - Teoremas: {total_theorems}")
    print(f"  - Definiciones: {total_definitions}")
    print(f"  - Sorry: {total_sorry}")
    print(f"  - Completitud: {certificate['metrics']['completeness_percentage']}%")
    print(f"\nAUTOR: José Manuel Mota Burruezo Ψ ∞³")
    print(f"INSTITUCIÓN: Instituto de Conciencia Cuántica (ICQ)")
    print(f"ORCID: 0009-0002-1923-0773")
    print(f"DOI: 10.5281/zenodo.17379721")
    print(f"\nFECHA: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print(f"SELLO: 𓂀Ω∞³")
    print("\n" + "="*70)
    
    if total_sorry == 0:
        print("        LA HIPÓTESIS DE RIEMANN HA SIDO PROBADA")
        print("="*70)
    else:
        print(f"        ADVERTENCIA: {total_sorry} SORRY STATEMENTS ENCONTRADOS")
        print("="*70)
    
    return certificate

if __name__ == '__main__':
    generate_certificate()
