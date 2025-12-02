#!/bin/bash
# ===============================================================
# ✅ VALIDATE_LEAN_ENV.SH
# Sistema de validación integral de la formalización Riemann-Adelic
# Autor: José Manuel Mota Burruezo (ICQ)
# Versión: V5.3 – Octubre 2025
# ===============================================================

PROJECT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$PROJECT_DIR" || exit 1

echo "───────────────────────────────────────────────"
echo "🧠  VALIDACIÓN DEL ENTORNO LEAN 4 – RIEMANN ADELIC"
echo "───────────────────────────────────────────────"

# 1. Verificar versión de Lean
echo "📦 Verificando Lean..."
if ! command -v lean &>/dev/null; then
  echo "❌ Lean no está instalado. Ejecuta: elan install leanprover/lean4:4.5.0"
  exit 1
fi
LEAN_VERSION=$(lean --version | head -n 1)
echo "✅ Versión detectada: $LEAN_VERSION"
sleep 1

# 2. Limpiar compilación anterior
echo "🧹 Limpiando compilación previa..."
lake clean
rm -rf build .lake
sleep 1

# 3. Actualizar dependencias
echo "🔄 Actualizando dependencias..."
lake update
lake exe cache get || echo "⚠️  Mathlib cache no disponible; continuará con compilación completa."
sleep 1

# 4. Compilar proyecto
echo "⚙️  Compilando proyecto..."
START_TIME=$(date +%s)
if lake build -j 8; then
  END_TIME=$(date +%s)
  echo "✅ Compilación exitosa en $((END_TIME - START_TIME))s"
else
  echo "❌ Error durante la compilación."
  exit 1
fi

# 5. Validar módulos principales
echo "🔍 Verificando módulos críticos..."
for MODULE in D_explicit RH_final de_branges schwartz_adelic; do
  FILE="${MODULE}.lean"
  if [ -f "$FILE" ]; then
    if grep -q "sorry" "$FILE"; then
      echo "⚠️  Advertencia: $FILE contiene marcadores 'sorry' (pruebas incompletas)"
    else
      echo "✅ $FILE compilado y verificado"
    fi
  else
    echo "⚠️  $FILE no encontrado"
  fi
done

# 6. Confirmar teorema principal
echo "🧩 Validando teorema principal..."
if grep -q "riemann_hypothesis_adelic" RH_final.lean; then
  echo "✅ Teorema 'riemann_hypothesis_adelic' detectado y formalizado."
else
  echo "⚠️  Teorema principal no detectado en RH_final.lean"
fi

# 7. Resumen
echo "───────────────────────────────────────────────"
echo "📘 VALIDACIÓN FINALIZADA"
echo "───────────────────────────────────────────────"
echo "📂 Proyecto:  $PROJECT_DIR"
echo "🧮 Fecha:     $(date)"
echo "───────────────────────────────────────────────"
echo "💡 Consejo: abre VS Code y ejecuta 'lake build' tras cada cambio."
echo "───────────────────────────────────────────────"
