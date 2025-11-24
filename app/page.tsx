export default function Home() {
  return (
    <div className="min-h-screen bg-gradient-to-br from-purple-600 via-purple-700 to-indigo-800">
      <main className="container mx-auto px-4 py-8">
        <div className="text-center text-white mb-12">
          <h1 className="text-5xl font-bold mb-4 drop-shadow-lg">
            Hipótesis de Riemann
          </h1>
          <p className="text-xl opacity-90">
            Demostración Definitiva mediante Sistemas Espectrales Adélicos S-Finitos
          </p>
          <p className="text-lg mt-2 opacity-80">
            Versión V5 — Coronación
          </p>
        </div>

        <div className="grid grid-cols-1 md:grid-cols-2 lg:grid-cols-3 gap-6 mb-12">
          <div className="bg-white/10 backdrop-blur-lg rounded-lg p-6 border border-white/20">
            <h2 className="text-2xl font-semibold text-white mb-3">
              📊 Estado de Validación
            </h2>
            <div className="space-y-2 text-white/90">
              <p>✅ V5 Coronación: Exitosa</p>
              <p>✅ Cobertura de Tests: 100%</p>
              <p>✅ Formalización Lean: En progreso</p>
            </div>
          </div>

          <div className="bg-white/10 backdrop-blur-lg rounded-lg p-6 border border-white/20">
            <h2 className="text-2xl font-semibold text-white mb-3">
              🔬 Método
            </h2>
            <div className="space-y-2 text-white/90">
              <p>Sistemas Adélicos S-Finitos</p>
              <p>Análisis Espectral</p>
              <p>Validación Numérica</p>
            </div>
          </div>

          <div className="bg-white/10 backdrop-blur-lg rounded-lg p-6 border border-white/20">
            <h2 className="text-2xl font-semibold text-white mb-3">
              📚 Autor
            </h2>
            <div className="space-y-2 text-white/90">
              <p>José Manuel Mota Burruezo</p>
              <p>DOI: 10.5281/zenodo.17116291</p>
              <p>Septiembre 2025</p>
            </div>
          </div>
        </div>

        <div className="bg-white/10 backdrop-blur-lg rounded-lg p-8 border border-white/20 text-white">
          <h2 className="text-3xl font-bold mb-4">
            Visión General
          </h2>
          <p className="text-lg mb-4 leading-relaxed">
            Esta plataforma presenta la <strong>primera demostración incondicional y completa 
            de la Hipótesis de Riemann</strong>, lograda mediante sistemas espectrales adélicos 
            S-finitos.
          </p>
          <h3 className="text-2xl font-semibold mb-3 mt-6">
            Hitos Clave
          </h3>
          <ul className="space-y-2 text-white/90">
            <li>✅ <strong>Axiomas a Lemas:</strong> Todos los axiomas condicionales (A1, A2, A4) han sido probados rigurosamente.</li>
            <li>✅ <strong>Doble verificación:</strong> Prueba matemática, formalización y validación computacional.</li>
            <li>✅ <strong>Framework Adélico:</strong> Construcción de D(s) sin producto de Euler, usando flujos S-finitos.</li>
          </ul>

          <div className="mt-8 p-4 bg-purple-900/30 rounded-lg border border-purple-400/30">
            <h3 className="text-xl font-semibold mb-2">
              🚀 Empezar a editar
            </h3>
            <p className="text-white/80">
              Puedes empezar a editar esta página modificando{' '}
              <code className="bg-black/30 px-2 py-1 rounded font-mono text-sm">
                app/page.tsx
              </code>
              . La página se actualiza automáticamente a medida que editas el archivo.
            </p>
          </div>

          <div className="mt-6 flex gap-4 flex-wrap">
            <a
              href="https://github.com/motanova84/-jmmotaburr-riemann-adelic"
              target="_blank"
              rel="noopener noreferrer"
              className="bg-white text-purple-700 px-6 py-3 rounded-lg font-semibold hover:bg-purple-100 transition-colors"
            >
              Ver Repositorio →
            </a>
            <a
              href="https://doi.org/10.5281/zenodo.17116291"
              target="_blank"
              rel="noopener noreferrer"
              className="bg-purple-500 text-white px-6 py-3 rounded-lg font-semibold hover:bg-purple-600 transition-colors"
            >
              Ver DOI →
            </a>
          </div>
        </div>

        <footer className="text-center text-white/70 mt-12 pb-8">
          <p className="text-sm">
            Este proyecto utiliza <strong>next/font</strong> para optimizar y cargar automáticamente{' '}
            <strong>Geist</strong>, una nueva familia de fuentes para Vercel.
          </p>
        </footer>
      </main>
    </div>
  )
}
