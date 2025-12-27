# Plagiarism Monitoring System

Sistema automatizado de monitoreo para detectar plagio y uso no autorizado de la investigación sobre la Hipótesis de Riemann (Versión V5 — Coronación).

## 📋 Descripción General

Este sistema genera "huellas digitales" (fingerprints) de los artefactos clave del proyecto y monitorea múltiples fuentes en busca de copias no autorizadas, paráfrasis o uso indebido. El monitoreo se ejecuta automáticamente mediante GitHub Actions y puede ejecutarse manualmente cuando sea necesario.

## 🎯 Características

- **Generación de Fingerprints**: SHA256, fuzzy hashing y fingerprints de snippets LaTeX
- **Monitoreo de GitHub**: Búsqueda de código y repositorios que puedan contener copias
- **Monitoreo de Crossref**: Detección de citas y referencias no autorizadas
- **Verificación de URLs**: Comprobación de similitud de contenido en URLs específicas
- **Alertas Automatizadas**: Sistema de alertas por severidad (alta, media, baja)
- **Evidencia Legal**: Registro de hallazgos con timestamps y metadatos

## 📁 Estructura de Archivos

```
monitoring/
├── README.md                    # Este archivo
├── config.json                  # Configuración del sistema
├── fingerprints.json           # Huellas digitales (generado automáticamente)
├── fingerprints_create.py      # Genera fingerprints de archivos clave
├── search_github.py            # Monitorea GitHub por código duplicado
├── search_crossref.py          # Monitorea Crossref por citas
├── check_url_similarity.py     # Verifica URLs específicas
├── run_monitor.py              # Script principal de orquestación
├── evidence/                   # Evidencia de infracciones (auto-generado)
└── alerts/                     # Reportes de alertas (auto-generado)
```

## 🚀 Uso Rápido

### Ejecutar Monitoreo Completo

```bash
# Desde la raíz del repositorio
python3 monitoring/run_monitor.py
```

Este comando:
1. Actualiza los fingerprints de todos los archivos clave
2. Busca en GitHub código y repositorios similares
3. Verifica Crossref para citas y trabajos similares
4. Genera un reporte consolidado en `monitoring/alerts/`

### Generar Solo Fingerprints

```bash
python3 monitoring/fingerprints_create.py
```

### Monitorear Solo GitHub

```bash
python3 monitoring/search_github.py
```

### Monitorear Solo Crossref

```bash
python3 monitoring/search_crossref.py
```

### Verificar URLs Específicas

```bash
python3 monitoring/check_url_similarity.py https://example.com/suspicious-url
```

## ⚙️ Configuración

### Variables de Entorno

Para obtener mejores resultados, configura las siguientes variables de entorno:

```bash
# GitHub Token (obligatorio para búsquedas extensivas)
export GITHUB_TOKEN="ghp_your_token_here"
```

#### Obtener un GitHub Token:

1. Ve a GitHub Settings → Developer settings → Personal access tokens
2. Genera un nuevo token (classic) con scopes: `public_repo`, `read:org`
3. Copia el token y añádelo como variable de entorno o secret de GitHub Actions

### Archivo de Configuración

Edita `monitoring/config.json` para personalizar:

- Queries de búsqueda
- Umbrales de similitud
- Servicios a monitorear
- Configuración de notificaciones

```json
{
  "monitoring": {
    "enabled": true,
    "github": true,
    "crossref": true,
    "web_search": false
  },
  "thresholds": {
    "exact_match": 100,
    "high_similarity": 80,
    "medium_similarity": 50,
    "low_similarity": 30
  }
}
```

## 🤖 Automatización con GitHub Actions

El sistema se ejecuta automáticamente cada noche mediante GitHub Actions. Ver `.github/workflows/monitor.yml`.

### Configurar Secrets en GitHub

1. Ve a tu repositorio → Settings → Secrets and variables → Actions
2. Añade los siguientes secrets:
   - `MONITOR_GITHUB_TOKEN`: Tu personal access token de GitHub
   - (Opcional) `SLACK_WEBHOOK_URL`: Para notificaciones a Slack
   - (Opcional) `NOTIFICATION_EMAIL`: Para alertas por correo

### Workflow Schedule

El workflow se ejecuta:
- **Diariamente** a las 02:00 UTC
- **Manualmente** mediante workflow_dispatch
- **En cada push** a la rama principal (solo genera fingerprints)

## 📊 Interpretación de Resultados

### Niveles de Severidad

- **HIGH** 🔴: Coincidencia exacta de hash o múltiples snippets encontrados
- **MEDIUM** 🟡: Similitud significativa o snippets individuales encontrados
- **LOW** 🟢: Menciones o similitudes menores

### Archivos de Salida

Los reportes se guardan en `monitoring/alerts/` con timestamps:

- `monitoring_report_YYYYMMDD_HHMMSS.json`: Reporte consolidado
- `github_alerts_YYYYMMDD_HHMMSS.json`: Alertas de GitHub
- `crossref_monitoring_YYYYMMDD_HHMMSS.json`: Resultados de Crossref
- `url_check_YYYYMMDD_HHMMSS.json`: Verificaciones de URLs

## 🔍 Fuentes Monitoreadas

### Actualmente Implementadas

1. **GitHub**
   - Búsqueda de código (Code Search API)
   - Búsqueda de repositorios
   - README y archivos de documentación

2. **Crossref**
   - Metadatos de DOI
   - Búsqueda por título
   - Detección de citas

### Planificadas (Futuras Mejoras)

- Zenodo y otros repositorios de investigación
- arXiv (preprints)
- Google Scholar (alertas)
- ResearchGate, Academia.edu
- Common Crawl Index
- Bing/Google Custom Search APIs

## 🛡️ Qué se Monitorea

### Fingerprints Generados

1. **Archivos Completos**:
   - `paper/main.pdf` (SHA256)
   - `paper/main.tex` (SHA256)
   - `paper_standalone.tex` (SHA256)
   - `RIEMANNJMMB84.pdf` (SHA256)

2. **Snippets LaTeX Clave**:
   - Ecuación de energía de vacío: `E_{vac}(R_\Psi) = \alpha/R_\Psi^4`
   - Operador adélico: `\mathcal{D}_{\text{adélico}}`
   - Teorema espectral: `Spec(\mathcal{D}) \subset i\mathbb{R}`
   - Hipótesis de Riemann
   - Simetría discreta: `\alpha_\Psi`

3. **Metadatos**:
   - DOI: `10.5281/zenodo.17116291`
   - CITATION.cff
   - README.md (header)

## 📝 Respuesta ante Infracciones

### Procedimiento Recomendado

1. **Revisión Manual**: Verifica cada alerta para confirmar infracción
2. **Recopilación de Evidencia**:
   - Captura de pantalla
   - Copia del contenido HTML
   - Información WHOIS del dominio
   - Headers HTTP
   - Timestamp
3. **Contacto Inicial**: Email al administrador del sitio/repositorio
4. **DMCA Takedown**: Si no hay respuesta, preparar solicitud DMCA
5. **Legal**: Para infracciones graves, consultar asesor legal

### Plantillas Disponibles

Ver el directorio `monitoring/templates/` (próximamente) para:
- Carta de cese y desista
- Solicitud DMCA para GitHub
- Email de contacto inicial

## 🔐 Consideraciones de Seguridad y Privacidad

- Respeta `robots.txt` de los sitios web
- Cumple con rate limits de APIs
- No compartas tokens o credenciales en el código
- Guarda evidencia de forma segura y privada
- Los archivos en `monitoring/evidence/` están en `.gitignore`

## 📚 Dependencias

### Requeridas (ya en requirements.txt)
- `requests`: Para consultas HTTP y APIs
- Python 3.8+

### Opcionales (para funcionalidades avanzadas)
```bash
pip install ssdeep        # Fuzzy hashing
pip install simhash       # Similarity hashing
pip install pdfminer.six  # Extracción de texto de PDF
pip install beautifulsoup4 # Web scraping
pip install pyppeteer     # Screenshots automáticos
```

## 🤝 Contribuciones

Si deseas mejorar el sistema de monitoreo:

1. Añade nuevas fuentes de monitoreo
2. Mejora los algoritmos de detección
3. Implementa notificaciones adicionales
4. Optimiza el rendimiento

## 📄 Licencia

Este sistema de monitoreo es parte del proyecto Riemann-Adelic y está protegido bajo las mismas licencias:
- Código: MIT License
- Contenido matemático: CC BY-NC-SA 4.0

## 🆘 Soporte

Para preguntas sobre el sistema de monitoreo:
- Abre un issue en GitHub
- Contacta: institutoconsciencia@proton.me

## ⚖️ Legal

Este sistema está diseñado para:
- ✅ Proteger la propiedad intelectual legítima
- ✅ Detectar uso no autorizado
- ✅ Prevenir plagio académico
- ❌ NO para acosar o amenazar
- ❌ NO para violar privacidad

Úsalo de forma ética y responsable.

---

**Última actualización**: 2025-10-16  
**Versión del sistema**: 1.0  
**Mantenedor**: José Manuel Mota Burruezo
