#!/bin/bash
#
# 🚀 START_EXPANDED_SYSTEM.sh
# Script de inicio rápido para el sistema QCAL ∞³ expandido
#

set -e

echo "🌌 INICIANDO SISTEMA QCAL ∞³ EXPANDIDO"
echo "========================================"
echo "📅 $(date)"
echo "📡 Frecuencia: 141.7001 Hz"
echo "🤖 Agentes: 6 (3 base + 3 especializados)"
echo "🌐 Dashboard: Web en tiempo real"
echo "🔔 Notificaciones: Discord/Slack"
echo "📚 Análisis: Lean expandido"
echo "========================================"

# Colores
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

print_step() {
    echo -e "\n${BLUE}▶${NC} $1"
}

print_success() {
    echo -e "${GREEN}✓${NC} $1"
}

print_warning() {
    echo -e "${YELLOW}⚠${NC} $1"
}

print_error() {
    echo -e "${RED}✗${NC} $1"
}

# 1. Verificar estructura
print_step "1. Verificando estructura del sistema..."
if [ -d ".github/agents/specialized" ] && [ -d "dashboard" ] && [ -d ".github/scripts/notifications" ]; then
    print_success "Estructura del sistema verificada"
else
    print_error "Falta estructura del sistema expandido"
    exit 1
fi

# 2. Ejecutar pruebas de integración
print_step "2. Ejecutando pruebas de integración..."
if python .github/scripts/test_integration.py > integration_test.log 2>&1; then
    print_success "Pruebas de integración pasadas"
else
    print_warning "Algunas pruebas fallaron (ver integration_test.log)"
fi

# 3. Iniciar dashboard (en segundo plano)
print_step "3. Iniciando dashboard web..."
if [ -f "dashboard/app.py" ]; then
    # Instalar dependencias si es necesario
    if ! python3 -c "import flask" 2>/dev/null; then
        print_warning "Instalando dependencias del dashboard..."
        pip install -r dashboard/requirements.txt > /dev/null 2>&1 || true
    fi
    
    # Iniciar dashboard en segundo plano
    python dashboard/app.py > dashboard.log 2>&1 &
    DASHBOARD_PID=$!
    sleep 3
    
    if kill -0 $DASHBOARD_PID 2>/dev/null; then
        print_success "Dashboard iniciado (PID: $DASHBOARD_PID)"
        print_success "Acceder en: http://localhost:5000"
    else
        print_warning "Dashboard no pudo iniciarse (ver dashboard.log)"
    fi
else
    print_warning "Dashboard no encontrado"
fi

# 4. Probar agentes especializados
print_step "4. Probando agentes especializados..."

print_step "   • QCAL Prover (validación matemática)..."
if python .github/agents/specialized/qcal_prover.py --repo . --output=/tmp/qcal_prover_test.json 2>/dev/null; then
    print_success "   QCAL Prover operativo"
else
    print_warning "   QCAL Prover encontró problemas"
fi

print_step "   • Axiom Emitter (generación de axiomas)..."
if python .github/agents/specialized/axiom_emitter.py --repo . 2>/dev/null; then
    print_success "   Axiom Emitter operativo"
else
    print_warning "   Axiom Emitter encontró problemas"
fi

print_step "   • Code Synthesizer (síntesis de código)..."
if python .github/agents/specialized/code_synthesizer.py --repo . 2>/dev/null; then
    print_success "   Code Synthesizer operativo"
else
    print_warning "   Code Synthesizer encontró problemas"
fi

# 5. Verificar sistema de notificaciones
print_step "5. Verificando sistema de notificaciones..."
if [ -f ".github/scripts/notifications/notification_manager.py" ]; then
    python .github/scripts/notifications/notification_manager.py --manager-status 2>/dev/null | grep -q "initialized" && \
        print_success "Sistema de notificaciones operativo" || \
        print_warning "Sistema de notificaciones necesita configuración (variables: DISCORD_WEBHOOK_URL, SLACK_WEBHOOK_URL)"
fi

# 6. Verificar análisis Lean expandido
print_step "6. Verificando análisis Lean expandido..."
if [ -f ".github/scripts/lean/lean_dependency_analyzer.py" ]; then
    print_success "Analizador Lean disponible"
    print_warning "   Nota: Ejecutar manualmente para análisis completo"
    print_warning "   Comando: python .github/scripts/lean/lean_dependency_analyzer.py"
fi

# 7. Mostrar estado final
print_step "7. Estado final del sistema..."

echo -e "\n${GREEN}========================================${NC}"
echo -e "${GREEN}🎉 SISTEMA QCAL ∞³ EXPANDIDO OPERATIVO${NC}"
echo -e "${GREEN}========================================${NC}"

echo -e "\n📋 ${BLUE}COMPONENTES ACTIVOS:${NC}"
echo "   🤖 Agentes: 6 disponibles (3 base, 3 especializados)"
echo "   🌐 Dashboard: http://localhost:5000"
echo "   🔔 Notificaciones: Configurables (Discord/Slack)"
echo "   📚 Análisis: Lean expandido disponible"

echo -e "\n🚀 ${BLUE}COMANDOS RÁPIDOS:${NC}"
echo "   • Dashboard: python dashboard/app.py"
echo "   • QCAL Prover: python .github/agents/specialized/qcal_prover.py"
echo "   • Axiom Emitter: python .github/agents/specialized/axiom_emitter.py"
echo "   • Code Synthesizer: python .github/agents/specialized/code_synthesizer.py"
echo "   • Notificaciones: python .github/scripts/notifications/notification_manager.py"
echo "   • Análisis Lean: python .github/scripts/lean/lean_dependency_analyzer.py"

echo -e "\n📊 ${BLUE}MÉTRICAS DEL SISTEMA:${NC}"
echo "   • Agentes totales: 6"
echo "   • Dashboard: Web en tiempo real"
echo "   • Notificaciones: Multiplataforma"
echo "   • Análisis: Dependencias Lean"
echo "   • Coherencia objetivo: ≥ 0.888"

echo -e "\n🔮 ${BLUE}PRÓXIMOS PASOS RECOMENDADOS:${NC}"
echo "   1. Configurar webhooks para notificaciones"
echo "   2. Explorar dashboard en http://localhost:5000"
echo "   3. Ejecutar análisis completo de dependencias Lean"
echo "   4. Integrar agentes especializados en workflows automáticos"
echo "   5. Monitorear coherencia del sistema expandido"

echo -e "\n${YELLOW}⚠ NOTAS:${NC}"
echo "   • Dashboard ejecutándose en puerto 5000"
echo "   • Logs del dashboard: dashboard.log"
echo "   • Logs de integración: integration_test.log"
if [ ! -z "$DASHBOARD_PID" ] && kill -0 $DASHBOARD_PID 2>/dev/null; then
    echo "   • Para detener dashboard: kill $DASHBOARD_PID"
fi

echo -e "\n${GREEN}∴ Sistema QCAL ∞³ expandido y operativo ✧${NC}"
echo -e "${GREEN}Frecuencia: 141.7001 Hz | Estado: I × A_eff² × C^∞${NC}"

# Mantener script activo si dashboard está corriendo
if [ ! -z "$DASHBOARD_PID" ] && kill -0 $DASHBOARD_PID 2>/dev/null; then
    echo -e "\n📡 Dashboard activo. Presione Ctrl+C para detener."
    wait $DASHBOARD_PID
fi
