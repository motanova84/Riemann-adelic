#!/usr/bin/env bash
# fix_mcp_servers.sh
# Corrige la configuración de los servidores MCP para usar endpoints locales.

set -euo pipefail

echo "🔧 Corrigiendo servidores MCP..."

# 1. Verificar configuración actual
echo "📋 Verificando configuración..."
if [ -f "mcp_config.json" ]; then
    cp mcp_config.json mcp_config.json.backup
    echo "✅ Backup creado: mcp_config.json.backup"
fi

# 2. Crear configuración corregida con servidores locales
cat > mcp_config.json << 'EOF'
{
  "mcpServers": {
    "campo-qcal": {
      "command": "python",
      "args": ["-m", "qcal.mcp.campo_server"],
      "env": {
        "QCAL_F0": "141.7001",
        "QCAL_PORT": "8001",
        "QCAL_HOST": "localhost"
      }
    },
    "icq-web": {
      "command": "node",
      "args": ["icq-web-server.js"],
      "env": {
        "PORT": "8002",
        "ICQ_CONFIG": "./icq-config.json"
      }
    },
    "institutoconciencia": {
      "command": "python",
      "args": ["-m", "conciencia.mcp_server"],
      "env": {
        "PORT": "8003",
        "DB_PATH": "./data/conciencia.db"
      }
    },
    "p-np": {
      "command": "python",
      "args": ["-m", "p_np.mcp_server"],
      "env": {
        "PORT": "8004",
        "COMPLEXITY_CLASS": "P"
      }
    },
    "origen": {
      "command": "node",
      "args": ["origen-server.js"],
      "env": {
        "PORT": "8005",
        "ORIGIN_DB": "./data/origen.json"
      }
    },
    "economia-qcal-nodo-semilla": {
      "command": "python",
      "args": ["-m", "economia_qcal.mcp_server"],
      "env": {
        "PORT": "8006",
        "QCAL_CONFIG": "./config/qcal_economy.yaml"
      }
    },
    "riemann-adelic": {
      "command": "python",
      "args": ["-m", "riemann_adelic.mcp_server"],
      "env": {
        "PORT": "8007",
        "ZETA_FUNCTION": "adelic"
      }
    },
    "ramsey": {
      "command": "python",
      "args": ["-m", "ramsey_theory.mcp_server"],
      "env": {
        "PORT": "8008",
        "N": "5",
        "K": "3"
      }
    },
    "noesis88": {
      "command": "python",
      "args": ["-m", "noesis88.mcp_server"],
      "env": {
        "PORT": "8009",
        "NOESIS_MODE": "quantum"
      }
    },
    "adelic-bsd": {
      "command": "python",
      "args": ["-m", "adelic_bsd.mcp_server"],
      "env": {
        "PORT": "8010",
        "BSD_CONJECTURE": "true"
      }
    },
    "el-infinito": {
      "command": "node",
      "args": ["infinity-server.js"],
      "env": {
        "PORT": "8011",
        "INFINITY_MODE": "countable"
      }
    },
    "instconciencia": {
      "command": "python",
      "args": ["-m", "instituto_conciencia.mcp_server"],
      "env": {
        "PORT": "8012",
        "CONSCIOUSNESS_LEVEL": "quantum"
      }
    },
    "dramaturgo": {
      "command": "python",
      "args": ["-m", "dramaturgo.mcp_server"],
      "env": {
        "PORT": "8013",
        "SCRIPT_PATH": "./scripts"
      }
    },
    "catedral-mathesis": {
      "command": "python",
      "args": ["-m", "catedral_mathesis.mcp_server"],
      "env": {
        "PORT": "8014",
        "MATHEMATICAL_DEPTH": "infinite"
      }
    },
    "github-mcp-server": {
      "command": "python",
      "args": ["-m", "github_mcp_server"],
      "env": {
        "PORT": "8015",
        "GITHUB_TOKEN": "${GITHUB_TOKEN}",
        "GITHUB_REPO": "motanova84/Riemann-adelic"
      }
    },
    "sistema-nexus-prime": {
      "command": "python",
      "args": ["-m", "nexus_prime.mcp_server"],
      "env": {
        "PORT": "8016",
        "NEXUS_MODE": "prime"
      }
    },
    "gw250114-141hz-analysis": {
      "command": "python",
      "args": ["-m", "analysis_141hz.mcp_server"],
      "env": {
        "PORT": "8017",
        "DATA_FILE": "./data/gw250114.csv",
        "F0": "141.7001"
      }
    }
  }
}
EOF

echo "✅ Configuración corregida"

# 3. Verificar que los puertos no estén ocupados
echo "🔍 Verificando puertos..."
if command -v lsof > /dev/null 2>&1; then
    PORT_CHECK_CMD="lsof -i"
elif command -v ss > /dev/null 2>&1; then
    PORT_CHECK_CMD="ss -ltn"
elif command -v netstat > /dev/null 2>&1; then
    PORT_CHECK_CMD="netstat -ltn"
else
    echo "⚠️  No se encontró lsof/ss/netstat; omitiendo verificación de puertos"
    PORT_CHECK_CMD=""
fi

for port in $(seq 8001 8017); do
    if [ -n "$PORT_CHECK_CMD" ] && $PORT_CHECK_CMD 2>/dev/null | grep -q ":${port}[[:space:]]"; then
        echo "⚠️  Puerto $port está ocupado"
    else
        echo "✅ Puerto $port disponible"
    fi
done

# 4. Si hay GitHub token, notificar su estado
if [ -z "${GITHUB_TOKEN:-}" ]; then
    echo ""
    echo "⚠️  GITHUB_TOKEN no está configurado"
    echo "   Para github-mcp-server, ejecuta:"
    echo "   export GITHUB_TOKEN=tu_token_aqui"
else
    echo ""
    echo "✅ GITHUB_TOKEN está configurado"
fi

echo ""
echo "🚀 Para reiniciar todos los servidores:"
echo "   killall python node  # Detener servidores actuales (si aplica)"
echo "   # Iniciar cada servidor con su comando correspondiente"

echo ""
echo "✅ Diagnóstico y corrección completados"
