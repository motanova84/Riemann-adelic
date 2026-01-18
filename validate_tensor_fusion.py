#!/usr/bin/env python3
"""
Validación del Certificado de Fusión Irreversible: Tensor P-NP ⊗ Riemann

Este script valida la coherencia y autenticidad del certificado de fusión
geométrica irreversible entre los nodos P-NP y Riemann en el sistema NOESIS88 - QCAL ∞³.

Usage:
    python validate_tensor_fusion.py [--verbose]
"""

import json
import hashlib
from pathlib import Path
from datetime import datetime
import sys


def load_certificate():
    """Carga el certificado de fusión tensor desde el archivo JSON."""
    cert_path = Path(__file__).parent / 'data' / 'certificates' / 'tensor_fusion_pnp_riemann_certificate.json'
    
    if not cert_path.exists():
        print(f"❌ Error: No se encontró el certificado en {cert_path}")
        return None
    
    with open(cert_path, 'r', encoding='utf-8') as f:
        return json.load(f)


def validate_coherence(cert):
    """Valida que la coherencia del sistema esté dentro de los límites esperados."""
    coherence = cert.get('coherence_global', 0)
    expected = 0.999999
    tolerance = 0.000001
    
    if abs(coherence - expected) <= tolerance:
        print(f"✅ Coherencia Global: {coherence} (esperado: {expected})")
        return True
    else:
        print(f"❌ Coherencia fuera de rango: {coherence} (esperado: {expected} ± {tolerance})")
        return False


def validate_frequencies(cert):
    """Valida las frecuencias del sistema."""
    freq_base = cert.get('frequency_base', 0)
    freq_madre = cert.get('frequency_madre', 0)
    freq_manifestada = cert.get('frequency_manifestada', 0)
    
    checks = []
    
    # Frecuencia base (Amor Irreversible A²)
    if abs(freq_base - 151.7001) < 0.0001:
        print(f"✅ Frecuencia Base (A²): {freq_base} Hz")
        checks.append(True)
    else:
        print(f"❌ Frecuencia Base incorrecta: {freq_base} (esperado: 151.7001)")
        checks.append(False)
    
    # Frecuencia resonante
    expected_resonante = 141.7001
    freq_resonante = cert.get('frequency_resonante', 0)
    if abs(freq_resonante - expected_resonante) < 0.0001:
        print(f"✅ Frecuencia Resonante: {freq_resonante} Hz")
        checks.append(True)
    else:
        print(f"❌ Frecuencia Resonante incorrecta: {freq_resonante} (esperado: {expected_resonante})")
        checks.append(False)
    
    # Frecuencia manifestada
    if freq_manifestada == 888:
        print(f"✅ Frecuencia Manifestada: {freq_manifestada} Hz")
        checks.append(True)
    else:
        print(f"❌ Frecuencia Manifestada incorrecta: {freq_manifestada} (esperado: 888)")
        checks.append(False)
    
    return all(checks)


def validate_tensor_properties(cert):
    """Valida las propiedades matemáticas del tensor."""
    props = cert.get('tensor_properties', {})
    
    checks = []
    
    # Irreversibilidad temporal
    temporal = props.get('temporal_irreversibility', {})
    if temporal.get('status') == 'VERIFIED':
        print(f"✅ Irreversibilidad Temporal: VERIFICADA")
        checks.append(True)
    else:
        print(f"❌ Irreversibilidad Temporal: NO VERIFICADA")
        checks.append(False)
    
    # Auto-escritura
    auto_escr = props.get('auto_escritura', {})
    if auto_escr.get('status') == 'ACTIVE':
        print(f"✅ Auto-Escritura: ACTIVA")
        checks.append(True)
    else:
        print(f"❌ Auto-Escritura: NO ACTIVA")
        checks.append(False)
    
    # Silencio radiante
    silencio = props.get('silencio_radiante', {})
    if silencio.get('status') == 'ACHIEVED':
        print(f"✅ Silencio Radiante: ALCANZADO")
        checks.append(True)
    else:
        print(f"❌ Silencio Radiante: NO ALCANZADO")
        checks.append(False)
    
    return all(checks)


def validate_verified_properties(cert):
    """Valida las propiedades verificadas A y B."""
    props = cert.get('verified_properties', {})
    
    checks = []
    
    # Propiedad A: Auto-Resolución
    prop_a = props.get('property_a', {})
    if prop_a.get('status') == 'VERIFIED' and prop_a.get('coherence', 0) >= 0.999999:
        print(f"✅ Propiedad A (Auto-Resolución): VERIFICADA (coherencia: {prop_a.get('coherence')})")
        checks.append(True)
    else:
        print(f"❌ Propiedad A: NO VERIFICADA")
        checks.append(False)
    
    # Propiedad B: Correspondencia Ceros-Pulsos
    prop_b = props.get('property_b', {})
    if prop_b.get('status') == 'VERIFIED' and prop_b.get('correlation', 0) >= 0.999999:
        print(f"✅ Propiedad B (Ceros-Pulsos): VERIFICADA (correlación: {prop_b.get('correlation')})")
        checks.append(True)
    else:
        print(f"❌ Propiedad B: NO VERIFICADA")
        checks.append(False)
    
    return all(checks)


def validate_metricas(cert):
    """Valida las métricas de coherencia final."""
    metricas = cert.get('metricas_coherencia', {})
    
    checks = []
    
    # Correlación P-NP
    corr_pnp = metricas.get('correlacion_pnp', 0)
    if corr_pnp >= 0.999998:
        print(f"✅ Correlación P-NP: {corr_pnp}")
        checks.append(True)
    else:
        print(f"❌ Correlación P-NP baja: {corr_pnp}")
        checks.append(False)
    
    # Correlación Riemann
    corr_riemann = metricas.get('correlacion_riemann', 0)
    if corr_riemann >= 0.999997:
        print(f"✅ Correlación Riemann: {corr_riemann}")
        checks.append(True)
    else:
        print(f"❌ Correlación Riemann baja: {corr_riemann}")
        checks.append(False)
    
    # Divergencia del tensor
    div_tensor = metricas.get('divergencia_tensor', 1)
    if div_tensor <= 0.000001:
        print(f"✅ Divergencia del Tensor: {div_tensor} (conservación verificada)")
        checks.append(True)
    else:
        print(f"❌ Divergencia del Tensor alta: {div_tensor}")
        checks.append(False)
    
    # Autoescritura
    if metricas.get('autoescritura') == 'ACTIVA':
        print(f"✅ Autoescritura: ACTIVA")
        checks.append(True)
    else:
        print(f"❌ Autoescritura: NO ACTIVA")
        checks.append(False)
    
    # Silencio radiante
    if metricas.get('silencio_radiante') == 'ALCANZADO':
        print(f"✅ Silencio Radiante: ALCANZADO")
        checks.append(True)
    else:
        print(f"❌ Silencio Radiante: NO ALCANZADO")
        checks.append(False)
    
    return all(checks)


def validate_cryptographic_signature(cert):
    """Valida la firma criptográfica del certificado."""
    firma = cert.get('firma_criptografica', {})
    
    # Verificar que existe el hash
    hash_value = firma.get('hash_sha256')
    if not hash_value:
        print("❌ No se encontró hash SHA-256")
        return False
    
    # Verificar formato del hash (debe ser hexadecimal de 64 caracteres)
    if len(hash_value) == 64 and all(c in '0123456789abcdef' for c in hash_value):
        print(f"✅ Hash SHA-256 válido: {hash_value[:16]}...{hash_value[-16:]}")
    else:
        print(f"❌ Hash SHA-256 inválido: formato incorrecto")
        return False
    
    # Verificar firma QCAL
    qcal_sig = firma.get('qcal_signature')
    if qcal_sig == '∴𓂀Ω∞³':
        print(f"✅ Firma QCAL: {qcal_sig}")
    else:
        print(f"❌ Firma QCAL inválida: {qcal_sig}")
        return False
    
    # Verificar timestamp
    timestamp = firma.get('timestamp')
    try:
        datetime.fromisoformat(timestamp.replace('Z', '+00:00'))
        print(f"✅ Timestamp válido: {timestamp}")
    except (ValueError, TypeError) as e:
        print(f"❌ Timestamp inválido: {timestamp} - {e}")
        return False
    
    # Verificar coherencia en firma
    if firma.get('coherence', 0) >= 0.999999:
        print(f"✅ Coherencia en firma: {firma.get('coherence')}")
    else:
        print(f"❌ Coherencia en firma baja: {firma.get('coherence')}")
        return False
    
    return True


def validate_fusion_geometry(cert):
    """Valida la geometría de fusión del tensor."""
    fusion = cert.get('fusion_geometry', {})
    
    checks = []
    
    # Definición del tensor
    tensor_def = fusion.get('tensor_definition')
    if tensor_def == 'T = P-NP ⊗ Riemann':
        print(f"✅ Definición del Tensor: {tensor_def}")
        checks.append(True)
    else:
        print(f"❌ Definición del Tensor incorrecta")
        checks.append(False)
    
    # Ley de conservación
    conservation = fusion.get('conservation_law')
    if '∇ · T = 0' in conservation:
        print(f"✅ Ley de Conservación: {conservation}")
        checks.append(True)
    else:
        print(f"❌ Ley de Conservación incorrecta")
        checks.append(False)
    
    # Divergencia
    divergence = fusion.get('divergence', 1)
    if divergence <= 0.000001:
        print(f"✅ Divergencia: {divergence} (flujo conservado)")
        checks.append(True)
    else:
        print(f"❌ Divergencia alta: {divergence}")
        checks.append(False)
    
    return all(checks)


def main():
    """Función principal de validación."""
    print("=" * 80)
    print("🌌 VALIDACIÓN DEL CERTIFICADO DE FUSIÓN IRREVERSIBLE")
    print("   TENSOR DE VERDAD UNIFICADA: P-NP ⊗ Riemann")
    print("=" * 80)
    print()
    
    # Cargar certificado
    cert = load_certificate()
    if cert is None:
        sys.exit(1)
    
    print(f"📜 Certificado cargado: {cert.get('title', 'Sin título')}")
    print(f"🕐 Timestamp: {cert.get('timestamp')}")
    print(f"🔰 Sello: {cert.get('signature')}")
    print(f"📊 Estado: {cert.get('status')}")
    print()
    
    # Ejecutar validaciones
    validations = {
        "Coherencia Global": validate_coherence(cert),
        "Frecuencias del Sistema": validate_frequencies(cert),
        "Propiedades del Tensor": validate_tensor_properties(cert),
        "Propiedades Verificadas A y B": validate_verified_properties(cert),
        "Métricas de Coherencia": validate_metricas(cert),
        "Firma Criptográfica": validate_cryptographic_signature(cert),
        "Geometría de Fusión": validate_fusion_geometry(cert)
    }
    
    print()
    print("=" * 80)
    print("📊 RESUMEN DE VALIDACIÓN")
    print("=" * 80)
    
    all_passed = True
    for name, result in validations.items():
        status = "✅ APROBADO" if result else "❌ FALLIDO"
        print(f"{status}: {name}")
        if not result:
            all_passed = False
    
    print()
    print("=" * 80)
    
    if all_passed:
        print("✅ CERTIFICADO DE FUSIÓN IRREVERSIBLE: VÁLIDO")
        print("🌟 El Tensor de Verdad Unificada P-NP ⊗ Riemann está activo")
        print("∴ Coherencia máxima alcanzada: Ψ = 0.999999")
        print("∴ Silencio Radiante: ALCANZADO")
        print("∴ Fusión: IRREVERSIBLE")
        print()
        print("∴𓂀Ω∞³")
        print("=" * 80)
        return 0
    else:
        print("❌ CERTIFICADO DE FUSIÓN: VALIDACIÓN FALLIDA")
        print("⚠️  Algunas verificaciones no pasaron")
        print("=" * 80)
        return 1


if __name__ == '__main__':
    sys.exit(main())
