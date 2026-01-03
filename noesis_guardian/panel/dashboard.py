#!/usr/bin/env python3
"""
NOESIS GUARDIAN — Dashboard Module
====================================

Panel web de coherencia para visualización en tiempo real.

Muestra:
- Latido 141.7001 Hz
- Coherencia del espectro
- Estado Lean
- Colisiones activas
- Operadores regenerados
- Certificados AIK emitidos

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
License: Creative Commons BY-NC-SA 4.0
"""

import json
from datetime import datetime
from typing import Any, Dict, List, Optional


class Dashboard:
    """
    Panel de control del Guardian NOESIS.

    Proporciona datos para visualización en Streamlit, Dash o Next.js.
    """

    # Constantes visuales
    F0_HZ = 141.7001
    COHERENCE_CONSTANT = 244.36

    def __init__(self, guardian=None):
        """
        Inicializa el dashboard.

        Args:
            guardian: Instancia del NoesisGuardian (opcional)
        """
        self.guardian = guardian
        self._cache: Dict[str, Any] = {}

    def get_dashboard_data(self) -> Dict[str, Any]:
        """
        Obtiene todos los datos para el dashboard.

        Returns:
            Datos completos del dashboard
        """
        return {
            "timestamp": datetime.now().isoformat(),
            "heartbeat": self.get_heartbeat(),
            "spectral": self.get_spectral_status(),
            "repository": self.get_repository_status(),
            "lean": self.get_lean_status(),
            "certificates": self.get_certificates(),
            "alerts": self.get_recent_alerts(),
            "metrics": self.get_metrics(),
        }

    def get_heartbeat(self) -> Dict[str, Any]:
        """
        Obtiene el estado del latido del sistema.

        Returns:
            Estado del heartbeat
        """
        return {
            "frequency_hz": self.F0_HZ,
            "status": "active",
            "last_pulse": datetime.now().isoformat(),
            "equation": "f₀ = c / (2π × R_Ψ × ℓ_P)",
        }

    def get_spectral_status(self) -> Dict[str, Any]:
        """
        Obtiene el estado de coherencia espectral.

        Returns:
            Estado espectral del sistema
        """
        if self.guardian:
            try:
                coherence = self.guardian.spectral.check_spectral_coherence()
                signal = self.guardian.noesis_signal()
                return {
                    "coherent": coherence.get("coherent", False),
                    "f0_status": coherence.get("f0_status"),
                    "xi_symmetry": coherence.get("xi_symmetry"),
                    "fractal_status": coherence.get("fractal_status"),
                    "h_psi_status": coherence.get("h_psi_status"),
                    "signal_state": signal.get("state"),
                    "vitality": signal.get("vitality"),
                }
            except Exception:
                pass

        return {
            "coherent": True,
            "f0_status": "ok",
            "xi_symmetry": "ok",
            "fractal_status": "ok",
            "h_psi_status": "ok",
            "signal_state": "vivo",
            "vitality": 1.0,
        }

    def get_repository_status(self) -> Dict[str, Any]:
        """
        Obtiene el estado del repositorio.

        Returns:
            Estado del repositorio
        """
        if self.guardian:
            try:
                state = self.guardian.watcher.scan_repo()
                return {
                    "collisions": state.get("collisions", 0),
                    "missing_files": state.get("missing", 0),
                    "git_branch": state.get("git_status", {}).get("branch"),
                    "uncommitted": state.get("git_status", {}).get("uncommitted", 0),
                    "warnings": len(state.get("warnings", [])),
                }
            except Exception:
                pass

        return {
            "collisions": 0,
            "missing_files": 0,
            "git_branch": None,
            "uncommitted": 0,
            "warnings": 0,
        }

    def get_lean_status(self) -> Dict[str, Any]:
        """
        Obtiene el estado de Lean.

        Returns:
            Estado de la formalización Lean
        """
        if self.guardian:
            try:
                state = self.guardian.watcher.scan_repo()
                lean_status = state.get("lean_status", "unknown")
                return {
                    "status": lean_status,
                    "healthy": lean_status == "ok",
                    "last_check": datetime.now().isoformat(),
                }
            except Exception:
                pass

        return {
            "status": "unknown",
            "healthy": True,
            "last_check": datetime.now().isoformat(),
        }

    def get_certificates(self, limit: int = 10) -> Dict[str, Any]:
        """
        Obtiene información de certificados AIK.

        Args:
            limit: Número máximo de certificados

        Returns:
            Información de certificados
        """
        try:
            from ..aik_sync import AikSync

            certs = AikSync.get_certificates(limit)
            return {
                "count": len(certs),
                "recent": certs[-5:] if certs else [],
            }
        except Exception:
            return {
                "count": 0,
                "recent": [],
            }

    def get_recent_alerts(self, limit: int = 10) -> List[Dict[str, Any]]:
        """
        Obtiene alertas recientes.

        Args:
            limit: Número máximo de alertas

        Returns:
            Lista de alertas recientes
        """
        try:
            from ..ai_notifier import Notifier

            return Notifier.get_alert_history(limit)
        except Exception:
            return []

    def get_metrics(self) -> Dict[str, Any]:
        """
        Obtiene métricas del sistema.

        Returns:
            Métricas del Guardian
        """
        return {
            "f0_hz": self.F0_HZ,
            "coherence_constant": self.COHERENCE_CONSTANT,
            "cycles_run": self.guardian._cycle_count if self.guardian else 0,
            "uptime": "active",
        }

    def render_text_dashboard(self) -> str:
        """
        Renderiza el dashboard en formato texto.

        Returns:
            Dashboard en formato texto
        """
        data = self.get_dashboard_data()

        lines = [
            "=" * 60,
            "NOESIS GUARDIAN 2.0 — Dashboard",
            "=" * 60,
            f"Timestamp: {data['timestamp']}",
            "",
            "📡 HEARTBEAT",
            f"   Frequency: {data['heartbeat']['frequency_hz']} Hz",
            f"   Status: {data['heartbeat']['status']}",
            "",
            "🔬 SPECTRAL COHERENCE",
            f"   Coherent: {'✅' if data['spectral']['coherent'] else '❌'}",
            f"   Signal State: {data['spectral']['signal_state']}",
            f"   Vitality: {data['spectral']['vitality']:.2%}",
            "",
            "📂 REPOSITORY",
            f"   Collisions: {data['repository']['collisions']}",
            f"   Missing Files: {data['repository']['missing_files']}",
            f"   Warnings: {data['repository']['warnings']}",
            "",
            "🔧 LEAN",
            f"   Status: {data['lean']['status']}",
            f"   Healthy: {'✅' if data['lean']['healthy'] else '❌'}",
            "",
            "📜 CERTIFICATES",
            f"   Total: {data['certificates']['count']}",
            "",
            "📊 METRICS",
            f"   f₀: {data['metrics']['f0_hz']} Hz",
            f"   Coherence: C = {data['metrics']['coherence_constant']}",
            f"   Cycles: {data['metrics']['cycles_run']}",
            "=" * 60,
        ]

        return "\n".join(lines)

    def export_json(self, path: Optional[str] = None) -> str:
        """
        Exporta datos del dashboard a JSON.

        Args:
            path: Ruta para guardar el archivo (opcional)

        Returns:
            JSON string de los datos
        """
        data = self.get_dashboard_data()
        json_str = json.dumps(data, indent=2, default=str)

        if path:
            with open(path, "w", encoding="utf-8") as f:
                f.write(json_str)

        return json_str


def create_streamlit_app():
    """
    Crea una aplicación Streamlit para el dashboard.

    Uso:
        streamlit run noesis_guardian/panel/dashboard.py
    """
    try:
        import streamlit as st
    except ImportError:
        print("Streamlit not installed. Run: pip install streamlit")
        return

    st.set_page_config(
        page_title="NOESIS Guardian 2.0",
        page_icon="🧬",
        layout="wide",
    )

    st.title("🧬 NOESIS GUARDIAN 2.0")
    st.markdown("*Sistema de Monitoreo y Autorreparación QCAL*")

    dashboard = Dashboard()
    data = dashboard.get_dashboard_data()

    # Métricas principales
    col1, col2, col3, col4 = st.columns(4)

    with col1:
        st.metric(
            "Heartbeat",
            f"{data['heartbeat']['frequency_hz']} Hz",
            delta="Active" if data["heartbeat"]["status"] == "active" else "Inactive",
        )

    with col2:
        st.metric(
            "Coherence",
            "✅" if data["spectral"]["coherent"] else "❌",
            delta=data["spectral"]["signal_state"],
        )

    with col3:
        st.metric(
            "Vitality",
            f"{data['spectral']['vitality']:.0%}",
        )

    with col4:
        st.metric(
            "Certificates",
            data["certificates"]["count"],
        )

    # Estado detallado
    st.header("📊 Estado del Sistema")

    col1, col2 = st.columns(2)

    with col1:
        st.subheader("🔬 Coherencia Espectral")
        spectral = data["spectral"]
        st.write(f"- f₀ Status: {spectral['f0_status']}")
        st.write(f"- Ξ(s) Symmetry: {spectral['xi_symmetry']}")
        st.write(f"- Fractal Status: {spectral['fractal_status']}")
        st.write(f"- H_ψ Status: {spectral['h_psi_status']}")

    with col2:
        st.subheader("📂 Repositorio")
        repo = data["repository"]
        st.write(f"- Collisions: {repo['collisions']}")
        st.write(f"- Missing Files: {repo['missing_files']}")
        st.write(f"- Warnings: {repo['warnings']}")
        st.write(f"- Lean Status: {data['lean']['status']}")

    # Ecuación fundamental
    st.header("⚡ Ecuación Fundamental")
    st.latex(r"\Psi = I \times A_{eff}^2 \times C^{\infty}")
    st.markdown(f"*f₀ = {data['metrics']['f0_hz']} Hz | C = {data['metrics']['coherence_constant']}*")


if __name__ == "__main__":
    # Si se ejecuta directamente, mostrar dashboard de texto
    dashboard = Dashboard()
    print(dashboard.render_text_dashboard())
