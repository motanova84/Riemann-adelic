#!/usr/bin/env python3
"""
Diagnóstico de Fallos de Servidores MCP
========================================

Diagnostica por qué los servidores MCP fallan al conectarse y
proporciona recomendaciones para corregir la configuración.

Causa raíz habitual: los servidores están configurados para conectarse
a endpoints de GitHub en lugar de a servidores locales (localhost:PUERTO).
"""

import json
import sys
from urllib.parse import urlparse
import requests
from pathlib import Path
from typing import Dict, Any, List


def _is_safe_endpoint(url: str) -> bool:
    """
    Verifica que la URL sea http/https y apunte a localhost o 127.0.0.1.

    Args:
        url: URL a validar.

    Returns:
        True si la URL es segura para conectarse.
    """
    try:
        parsed = urlparse(url)
        if parsed.scheme not in ("http", "https"):
            return False
        host = parsed.hostname or ""
        return host in ("localhost", "127.0.0.1", "::1")
    except Exception:
        return False


def diagnose_server(server_name: str, config: Dict[str, Any]) -> bool:
    """
    Diagnostica por qué un servidor MCP falló.

    Args:
        server_name: Nombre del servidor a diagnosticar.
        config: Configuración del servidor (puede estar vacía).

    Returns:
        True si el servidor responde correctamente, False en caso contrario.
    """
    print(f"\n🔍 Diagnosticando {server_name}...")

    # Verificar configuración
    if "endpoint" in config:
        endpoint = config["endpoint"]
        print(f"   Endpoint configurado: {endpoint}")

        # Validar que el endpoint sea un servidor local seguro
        if not _is_safe_endpoint(endpoint):
            print("   ❌ Endpoint no es localhost - posible configuración incorrecta")
            print("      Use localhost:PUERTO en lugar de endpoints externos")
            return False

        # Probar conectividad
        try:
            response = requests.get(endpoint, timeout=5)
            print(f"   Código respuesta: {response.status_code}")

            if response.status_code == 200:
                content_type = response.headers.get("content-type", "")
                if "html" in content_type:
                    print("   ⚠️  Recibió HTML, esperaba JSON")
                    print("   ❌ Configuración incorrecta")
                    return False
                else:
                    print("   ✅ Endpoint responde correctamente")
                    return True
            elif response.status_code == 404:
                print("   ❌ Endpoint no encontrado (404)")
                return False
            elif response.status_code == 403:
                print("   ❌ Acceso prohibido (403) - ¿Token inválido?")
                return False
            else:
                print(f"   ❌ Error HTTP {response.status_code}")
                return False

        except requests.exceptions.ConnectionError:
            print("   ❌ No se puede conectar al endpoint")
            return False
        except requests.exceptions.Timeout:
            print("   ❌ Timeout de conexión")
            return False
        except Exception as exc:
            print(f"   ❌ Error inesperado: {exc}")
            return False

    # Si tiene command/args es un servidor local (configuración correcta)
    if "command" in config and "args" in config:
        print("   ✅ Configurado como servidor local (command/args)")
        return True

    print("   ⚠️  Sin configuración de endpoint ni command/args")
    return False


def main() -> int:
    """
    Diagnostica todos los servidores MCP configurados.

    Returns:
        0 si todos los servidores están correctamente configurados, 1 en caso contrario.
    """
    print("=" * 60)
    print("🔧 DIAGNÓSTICO DE FALLOS DE SERVIDORES MCP")
    print("=" * 60)

    # Intentar cargar configuración
    config_file = Path("mcp_config.json")
    if config_file.exists():
        with config_file.open(encoding="utf-8") as f:
            full_config = json.load(f)
        configs = full_config.get("mcpServers", full_config)
        print(f"✅ Configuración cargada desde {config_file}")
    else:
        configs = {}
        print("⚠️  Archivo de configuración no encontrado")

    # Obtener lista de servidores desde la configuración cuando esté disponible;
    # caer en la lista conocida de servidores que reportaron fallos si no.
    if configs:
        servers_to_check: List[str] = list(configs.keys())
    else:
        servers_to_check = [
            "campo-qcal",
            "icq-web",
            "institutoconciencia",
            "p-np",
            "origen",
            "economia-qcal-nodo-semilla",
            "riemann-adelic",
            "ramsey",
            "noesis88",
            "adelic-bsd",
            "el-infinito",
            "instconciencia",
            "dramaturgo",
            "catedral-mathesis",
            "github-mcp-server",
            "sistema-nexus-prime",
            "gw250114-141hz-analysis",
        ]

    results: Dict[str, bool] = {}
    for server in servers_to_check:
        config = configs.get(server, {})
        is_ok = diagnose_server(server, config)
        results[server] = is_ok

    total = len(servers_to_check)
    success_count = sum(1 for v in results.values() if v)

    # Resumen
    print("\n" + "=" * 60)
    print("📊 RESUMEN DE DIAGNÓSTICO")
    print("=" * 60)
    print(f"✅ Funcionan correctamente: {success_count}/{total}")
    print(f"❌ Requieren configuración: {total - success_count}/{total}")

    # Recomendaciones
    print("\n" + "=" * 60)
    print("🎯 RECOMENDACIONES")
    print("=" * 60)
    print("""
    1. Verificar que los endpoints apunten a servidores locales
       Ejemplo: http://localhost:PUERTO

    2. Si usan GitHub, asegurar:
       - Token válido en variables de entorno
       - Permisos correctos del token
       - Repositorio existe y es accesible

    3. Configurar correctamente en mcp_config.json usando
       command/args para servidores locales:
       {
         "mcpServers": {
           "servidor": {
             "command": "python",
             "args": ["-m", "modulo.mcp_server"],
             "env": { "PORT": "8000" }
           }
         }
       }

    4. Para github-mcp-server, exportar el token antes de iniciar:
       export GITHUB_TOKEN=tu_token_aqui
    """)

    return 0 if success_count == total else 1


if __name__ == "__main__":
    sys.exit(main())
