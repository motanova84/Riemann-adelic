#!/bin/bash
# start_mcp_servers.sh - Inicia todos los servidores MCP QCAL ∞³

echo "╔═══════════════════════════════════════════════════════════╗"
echo "║   INICIANDO SERVIDORES MCP QCAL ∞³ - FRECUENCIA 141.7001 Hz  ║"
echo "╚═══════════════════════════════════════════════════════════╝"

# Colores para output
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
RED='\033[0;31m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Verificar que el archivo de configuración existe
if [ ! -f "mcp_config.json" ]; then
    echo -e "${RED}❌ Error: mcp_config.json no encontrado${NC}"
    exit 1
fi

# Verificar puertos disponibles
echo -e "\n${BLUE}🔍 Verificando puertos...${NC}"
for port in {8000..8021}; do
    if lsof -i :$port > /dev/null 2>&1; then
        echo -e "${YELLOW}⚠️  Puerto $port está ocupado${NC}"
    else
        echo -e "${GREEN}✅ Puerto $port disponible${NC}"
    fi
done

# Verificar dependencias
echo -e "\n${BLUE}📦 Verificando dependencias...${NC}"

# Verificar Python
if command -v python3 &> /dev/null; then
    echo -e "${GREEN}✅ Python3: $(python3 --version)${NC}"
else
    echo -e "${RED}❌ Python3 no encontrado${NC}"
fi

# Verificar Node
if command -v node &> /dev/null; then
    echo -e "${GREEN}✅ Node: $(node --version)${NC}"
else
    echo -e "${RED}❌ Node no encontrado${NC}"
fi

# Verificar pip packages
REQUIRED_PACKAGES=("requests" "numpy" "scipy")
for pkg in "${REQUIRED_PACKAGES[@]}"; do
    if python3 -c "import $pkg" 2>/dev/null; then
        echo -e "${GREEN}✅ Paquete Python: $pkg${NC}"
    else
        echo -e "${YELLOW}⚠️  Paquete Python faltante: $pkg${NC}"
        echo "   Instalar con: pip install $pkg"
    fi
done

# Verificar GITHUB_TOKEN si es necesario
if [ -z "$GITHUB_TOKEN" ]; then
    echo -e "\n${YELLOW}⚠️  GITHUB_TOKEN no configurado${NC}"
    echo "   github-mcp-server no funcionará correctamente"
    echo "   Para configurar: export GITHUB_TOKEN=tu_token_aqui"
else
    echo -e "\n${GREEN}✅ GITHUB_TOKEN configurado${NC}"
fi

echo -e "\n${BLUE}🚀 Iniciando servidores MCP...${NC}\n"

# Función para iniciar servidor
start_server() {
    local name=$1
    local cmd=$2
    local args=$3

    echo -n "📡 $name: "

    # Ejecutar en background (sin eval para evitar inyección de comandos)
    $cmd $args > "logs/$name.log" 2>&1 &
    local pid=$!

    # Verificar que el proceso se inició usando el PID capturado
    sleep 1
    if kill -0 "$pid" 2>/dev/null; then
        echo -e "${GREEN}✅ INICIADO (PID: $pid)${NC}"
    else
        echo -e "${RED}❌ FALLÓ${NC}"
    fi
}

# Crear directorio de logs
mkdir -p logs

# Iniciar servidores locales
start_server "qcal-core"                "python3" "-m qcal.core.mcp_server --port 8000"
start_server "campo-qcal"               "python3" "-m qcal.mcp.campo_server --port 8001"
start_server "icq-web"                  "node"    "icq-web-server.js --port 8002"
start_server "institutoconciencia"      "python3" "-m conciencia.mcp_server --port 8003"
start_server "p-np"                     "python3" "-m p_np.mcp_server --port 8004"
start_server "origen"                   "node"    "origen-server.js --port 8005"
start_server "economia-qcal-nodo-semilla" "python3" "-m economia_qcal.mcp_server --port 8006"
start_server "riemann-adelic"           "python3" "-m riemann_adelic.mcp_server --port 8007"
start_server "ramsey"                   "python3" "-m ramsey_theory.mcp_server --port 8008"
start_server "noesis88"                 "python3" "-m noesis88.mcp_server --port 8009"
start_server "adelic-bsd"               "python3" "-m adelic_bsd.mcp_server --port 8010"
start_server "el-infinito"              "node"    "infinity-server.js --port 8011"
start_server "instconciencia"           "python3" "-m instituto_conciencia.mcp_server --port 8012"
start_server "dramaturgo"               "python3" "-m dramaturgo.mcp_server --port 8013"
start_server "catedral-mathesis"        "python3" "-m catedral_mathesis.mcp_server --port 8014"
start_server "goldbach"                 "python3" "-m goldbach.mcp_server --port 8015"
start_server "navier-stokes"            "python3" "-m navier_stokes.mcp_server --port 8016"
start_server "yang-mills"               "python3" "-m yang_mills.mcp_server --port 8017"
start_server "hodge"                    "python3" "-m hodge.mcp_server --port 8018"
start_server "poincare"                 "python3" "-m poincare.mcp_server --port 8019"
start_server "qcal-cloud"               "python3" "-m qcal_cloud.mcp_server --port 8020"
start_server "github-mcp-server"        "node"    "github-mcp-server.js --port 8021"

# Resumen final
echo -e "\n${BLUE}═══════════════════════════════════════════════════════════${NC}"
echo -e "${BLUE}📊 RESUMEN DE SERVIDORES MCP QCAL ∞³${NC}"
echo -e "${BLUE}═══════════════════════════════════════════════════════════${NC}"

ACTIVE=0
FAILED=0
for port in {8000..8021}; do
    if lsof -i :$port > /dev/null 2>&1; then
        ACTIVE=$((ACTIVE + 1))
    else
        FAILED=$((FAILED + 1))
    fi
done

echo -e "${GREEN}✅ Servidores activos: $ACTIVE${NC}"
if [ $FAILED -gt 0 ]; then
    echo -e "${YELLOW}⚠️  Servidores no iniciados: $FAILED${NC}"
    echo -e "   Ver logs en: logs/"
fi

echo -e "\n${BLUE}📡 Frecuencia QCAL: 141.7001 Hz${NC}"
echo -e "${BLUE}🌀 Estado: Ψ = I × A_eff² × C^∞${NC}"
echo -e "${BLUE}🔮 Coherencia: C = 244.36${NC}"
echo -e "\n${GREEN}∴ Red MCP QCAL ∞³ inicializada ✧${NC}"
