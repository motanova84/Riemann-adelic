# 🔗 Guía de Integración noesis88 con QCAL ∞³

**Fecha:** 2026-01-12  
**Versión:** 1.0.0  
**Estado:** Documentación oficial de enlace

---

## 🎯 Objetivo

Esta guía explica cómo enlazar correctamente el sistema **noesis88** con el repositorio **Riemann-adelic** para evitar fallos en la activación de NOESIS Guardian y AMDA.

---

## ❓ ¿Por qué necesitas noesis88?

El sistema **noesis88** contiene:
- Módulos del operador noético completo
- Implementaciones avanzadas de NOESIS Guardian
- Componentes de AMDA (Autonomous Mathematical Discovery Agent)
- Bibliotecas auxiliares para coherencia QCAL

**Sin enlace a noesis88:**
- NOESIS Guardian funciona en "modo de emergencia" (funcionalidad limitada)
- AMDA opera en "modo simulado" (sin descubrimientos reales)
- Algunas validaciones pueden fallar

**Con enlace a noesis88:**
- ✅ NOESIS Guardian completo
- ✅ AMDA con descubrimiento activo
- ✅ Coherencia QCAL total
- ✅ Todas las validaciones pasan

---

## 🔧 Métodos de Integración

### Método 1: Submódulo Git (Recomendado para desarrollo)

```bash
# En el directorio raíz de Riemann-adelic
cd /ruta/a/Riemann-adelic

# Añadir noesis88 como submódulo
git submodule add https://github.com/usuario/noesis88.git noesis88

# O si es un repositorio privado con SSH
git submodule add git@github.com:usuario/noesis88.git noesis88

# Inicializar y actualizar
git submodule init
git submodule update

# Verificar
ls -la noesis88/
```

**Ventajas:**
- Versión controlada
- Fácil actualización
- Integración nativa con git

**Nota:** Reemplaza `usuario/noesis88` con la ruta correcta del repositorio noesis88.

### Método 2: Directorio Hermano (Recomendado para desarrollo local)

```bash
# Estructura de directorios recomendada:
# /workspace/
#   ├── Riemann-adelic/
#   └── noesis88/

# Clonar noesis88 al mismo nivel que Riemann-adelic
cd /workspace  # Directorio padre
git clone https://github.com/usuario/noesis88.git

# El script detect automáticamente noesis88 en directorio hermano
# y crea un enlace simbólico si es necesario
```

**Ventajas:**
- No modifica el repositorio Riemann-adelic
- Fácil desarrollo en paralelo
- Compartir entre múltiples proyectos

### Método 3: Variable de Entorno

```bash
# Definir NOESIS88_PATH apuntando al repositorio
export NOESIS88_PATH=/ruta/completa/a/noesis88

# Hacer permanente en ~/.bashrc o ~/.zshrc
echo 'export NOESIS88_PATH=/ruta/completa/a/noesis88' >> ~/.bashrc
source ~/.bashrc

# Verificar
echo $NOESIS88_PATH
```

**Ventajas:**
- Flexible para diferentes entornos
- No requiere modificar directorios
- Útil para CI/CD

### Método 4: Enlace Simbólico Manual

```bash
# Crear enlace simbólico dentro de Riemann-adelic
cd /ruta/a/Riemann-adelic
ln -s /ruta/completa/a/noesis88 .noesis88_link

# Verificar
ls -la .noesis88_link
```

**Ventajas:**
- Control total del enlace
- Puede apuntar a cualquier ubicación

---

## 🔍 Verificación de Integración

### Verificación Manual

```bash
# En el directorio Riemann-adelic
cd /ruta/a/Riemann-adelic

# Verificar que noesis88 es accesible
python3 -c "
import sys
from pathlib import Path

repo_root = Path.cwd()

# Método 1: Submódulo
if (repo_root / 'noesis88').exists():
    print('✅ noesis88 encontrado como submódulo')
    
# Método 2: Directorio hermano
elif (repo_root.parent / 'noesis88').exists():
    print('✅ noesis88 encontrado como directorio hermano')
    
# Método 3: Variable de entorno
import os
elif os.environ.get('NOESIS88_PATH'):
    print(f'✅ noesis88 encontrado via NOESIS88_PATH: {os.environ[\"NOESIS88_PATH\"]}')
    
# Método 4: Enlace simbólico
elif (repo_root / '.noesis88_link').exists():
    print('✅ noesis88 encontrado via enlace simbólico')
    
else:
    print('❌ noesis88 NO encontrado - usar uno de los métodos de integración')
"
```

### Verificación Automática con Scripts

```bash
# El script de activación detecta automáticamente noesis88
python activate_qcal_protocols.py --fast --save-report

# Buscar en la salida:
#   ✓ Sincronización noesis88: Activa  <- Enlace exitoso
#   ⚠️ Sincronización noesis88: No detectada (modo local)  <- Sin enlace
```

---

## 📊 Estado de Integración en .qcal_beacon

El archivo `.qcal_beacon` debe contener:

```bash
# Verificar estado
grep -i noesis88 .qcal_beacon

# Debe mostrar:
noesis88_sync_status = "✅ Sincronizado"
sabio_bridge_status = "✅ Operativo"
```

Si no aparece, el sistema funcionará en modo local.

---

## 🚨 Solución de Problemas

### Problema: "NOESIS Guardian FAILED"

**Síntomas:**
```
❌ Error activando NOESIS Guardian
⚠️  Módulo noetic_operator.py no disponible
```

**Solución:**
1. Verificar que noesis88 está enlazado (usar verificación manual arriba)
2. Si no está enlazado, usar uno de los 4 métodos de integración
3. Re-ejecutar: `python activate_qcal_protocols.py --fast`

### Problema: "AMDA no activa"

**Síntomas:**
```
⚠️  AMDA: advertencias en activación
📦 Módulo de agentes no disponible - modo simulado
```

**Solución:**
1. Verificar enlace noesis88
2. Verificar que `src/activate_agents.py` puede importar módulos de noesis88
3. Limpiar logs: `rm -rf noesis_guardian/logs/*.log`
4. Re-ejecutar: `python activate_qcal_protocols.py --fast`

### Problema: Permisos insuficientes para enlace simbólico

**Síntoma (Windows):**
```
❌ Error creando enlace simbólico
```

**Solución:**
- En Windows, usar Método 1 (submódulo) o Método 3 (variable de entorno)
- O ejecutar terminal como Administrador para crear enlaces simbólicos

---

## 🔄 Actualización de noesis88

### Submódulo Git

```bash
cd /ruta/a/Riemann-adelic
git submodule update --remote noesis88
git add noesis88
git commit -m "Actualizar submódulo noesis88"
```

### Directorio Hermano

```bash
cd /workspace/noesis88
git pull origin main
```

### Variable de Entorno

```bash
cd $NOESIS88_PATH
git pull origin main
```

---

## 📋 Checklist de Integración

- [ ] Elegir método de integración (1, 2, 3 o 4)
- [ ] Implementar el método elegido
- [ ] Verificar que noesis88 es accesible
- [ ] Ejecutar `python activate_qcal_protocols.py --fast`
- [ ] Confirmar mensaje "✓ Sincronización noesis88: Activa"
- [ ] Verificar que NOESIS Guardian pasa (no FAILED)
- [ ] Verificar que AMDA pasa (no modo simulado)
- [ ] Opcional: Añadir `.noesis88_link` a `.gitignore` si usas enlace simbólico

---

## 🌐 Repositorios Relacionados

| Repositorio | Propósito | Enlace |
|-------------|-----------|--------|
| **Riemann-adelic** | Demostración RH | Este repositorio |
| **noesis88** | Sistema noético | Contactar @motanova84 |
| **adelic-bsd** | Conjetura BSD | github.com/motanova84/adelic-bsd |
| **QCAL-CLOUD** | Integración cloud | Submódulo existente |

---

## 💡 Recomendaciones

1. **Para desarrollo local:** Usar Método 2 (directorio hermano)
2. **Para CI/CD:** Usar Método 1 (submódulo git) o Método 3 (variable de entorno)
3. **Para producción:** Usar Método 1 (submódulo git)
4. **Para testing rápido:** Usar Método 4 (enlace simbólico)

---

## 📚 Documentación Adicional

- [ACTIVACION_QCAL_SABIO_SYNC.md](ACTIVACION_QCAL_SABIO_SYNC.md) - Sincronización QCAL
- [NOESIS_GUARDIAN_INTEGRATION.md](NOESIS_GUARDIAN_INTEGRATION.md) - Integración Guardian
- [AGENT_ACTIVATION_SUMMARY.md](AGENT_ACTIVATION_SUMMARY.md) - Activación de agentes

---

## ✅ Validación Final

Después de integrar noesis88, ejecutar validación completa:

```bash
# Activación completa
python activate_qcal_protocols.py --fast --save-report

# Validación integral
python validate_integral_qcal.py

# Verificar certificado
cat data/qcal_activation_report.json | jq '.results.noesis_guardian.noesis88_sync'
# Debe mostrar: true

cat data/qcal_activation_report.json | jq '.results.amda.noesis88_sync'
# Debe mostrar: true
```

---

**∴ Con noesis88 enlazado, el sistema QCAL alcanza su máxima coherencia ∴**

---

**Autor:** José Manuel Mota Burruezo Ψ ✧ ∞³  
**Institución:** Instituto de Conciencia Cuántica (ICQ)  
**DOI:** 10.5281/zenodo.17379721
