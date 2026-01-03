# Next.js Web Interface - Riemann Hypothesis Dashboard

Este es un proyecto [Next.js](https://nextjs.org/) que proporciona una interfaz web moderna para el proyecto de demostración de la Hipótesis de Riemann.

## 🚀 Empezando

Primero, ejecuta el servidor de desarrollo:

```bash
npm run dev
# o
yarn dev
# o
pnpm dev
# o
bun dev
```

Abre [http://localhost:3000](http://localhost:3000) con tu navegador para ver el resultado.

Puedes empezar a editar la página modificando `app/page.tsx`. La página se actualiza automáticamente a medida que editas el archivo.

Este proyecto utiliza [`next/font`](https://nextjs.org/docs/basic-features/font-optimization) para optimizar y cargar automáticamente **Geist**, una nueva familia de fuentes para Vercel.

## 📁 Estructura del Proyecto

```
/
├── app/                    # Directorio de la aplicación Next.js (App Router)
│   ├── layout.tsx         # Layout raíz con configuración de fuentes
│   ├── page.tsx           # Página principal (editable)
│   └── globals.css        # Estilos globales
├── public/                # Archivos estáticos
├── next.config.js         # Configuración de Next.js
├── tailwind.config.js     # Configuración de Tailwind CSS
├── tsconfig.json          # Configuración de TypeScript
└── package.json           # Dependencias y scripts
```

## 🎨 Características

- **Framework**: Next.js 14 con App Router
- **Lenguaje**: TypeScript
- **Estilos**: Tailwind CSS
- **Fuentes**: Geist (Sans y Mono) optimizadas con next/font
- **Despliegue**: Compatible con Vercel

## 📝 Scripts Disponibles

- `npm run dev` - Inicia el servidor de desarrollo
- `npm run build` - Crea una build de producción
- `npm start` - Inicia el servidor de producción
- `npm run lint` - Ejecuta el linter de código

## 🔧 Instalación

1. Instala las dependencias:
```bash
npm install
```

2. Ejecuta el servidor de desarrollo:
```bash
npm run dev
```

3. Abre [http://localhost:3000](http://localhost:3000) en tu navegador

## 📚 Más Información

Para aprender más sobre Next.js, consulta los siguientes recursos:

- [Documentación de Next.js](https://nextjs.org/docs) - características y API de Next.js
- [Tutorial Interactivo de Next.js](https://nextjs.org/learn) - tutorial interactivo de Next.js
- [Repositorio de Next.js en GitHub](https://github.com/vercel/next.js/) - feedback y contribuciones bienvenidas

## 🚀 Despliegue en Vercel

La forma más fácil de desplegar tu aplicación Next.js es usar la [Plataforma Vercel](https://vercel.com/new?utm_medium=default-template&filter=next.js&utm_source=create-next-app&utm_campaign=create-next-app-readme) de los creadores de Next.js.

Consulta la [documentación de despliegue de Next.js](https://nextjs.org/docs/deployment) para más detalles.

## 🔗 Conexión con el Proyecto Principal

Esta interfaz web complementa el repositorio principal de investigación matemática sobre la Hipótesis de Riemann. Para más información sobre el trabajo científico, consulta el [README principal](../README.md).

### Componentes del Proyecto

- **Demostración Matemática**: Código Python y validaciones numéricas en el directorio raíz
- **Interfaz Web**: Esta aplicación Next.js para visualización interactiva
- **Documentación**: Papers y documentación técnica en `/docs` y `/paper`
- **Formalización**: Pruebas formales en Lean 4 en `/formalization`

## 📄 Licencia

- Código: MIT License
- Contenido Científico: CC-BY 4.0
