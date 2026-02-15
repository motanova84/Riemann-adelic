# Guía Rápida - Next.js Development Server

## 🚀 Inicio Rápido

### Instalación
```bash
npm install
```

### Ejecutar Servidor de Desarrollo
```bash
npm run dev
```

Abre [http://localhost:3000](http://localhost:3000) en tu navegador.

### Puertos Alternativos
```bash
# Usar yarn
yarn dev

# Usar pnpm
pnpm dev

# Usar bun
bun dev
```

## ✏️ Edición en Tiempo Real

Modifica `app/page.tsx` y observa los cambios automáticamente en el navegador.

## 🎨 Estructura de Archivos

- `app/page.tsx` - Página principal (START HERE)
- `app/layout.tsx` - Layout raíz con fuentes
- `app/globals.css` - Estilos globales
- `tailwind.config.js` - Configuración de Tailwind

## 📦 Comandos Útiles

```bash
npm run dev     # Desarrollo (hot reload)
npm run build   # Build de producción
npm start       # Servidor de producción
npm run lint    # Verificar código
```

## 🔤 Fuentes Optimizadas

Este proyecto usa **next/font** para optimizar y cargar **Geist**, una moderna familia de fuentes.

Las fuentes están configuradas en `app/layout.tsx`:
- `GeistSans` - Tipografía principal
- `GeistMono` - Código y monospace

## 📖 Documentación Completa

Ver [NEXTJS_README.md](NEXTJS_README.md) para documentación detallada.

## 🌐 Recursos Next.js

- [Documentación](https://nextjs.org/docs)
- [Tutorial Interactivo](https://nextjs.org/learn)
- [Ejemplos](https://github.com/vercel/next.js/tree/canary/examples)
