"""
Streamlit dashboard for Noesis Guardian 3.0.

Provides a web interface for visualizing guardian logs.
"""

import json
from pathlib import Path

import streamlit as st


LOGFILE = Path("noesis_guardian/logs/guardian_log.json")


def load_entries():
    """Load all log entries from the guardian log file."""
    if not LOGFILE.exists():
        return []
    entries = []
    with LOGFILE.open() as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            try:
                entries.append(json.loads(line))
            except json.JSONDecodeError:
                continue
    return entries


def main():
    """Main Streamlit dashboard function."""
    st.title("Noesis Guardian 3.0 — Dashboard")

    entries = load_entries()
    st.write(f"Total de ciclos registrados: {len(entries)}")

    if not entries:
        st.info("Todavía no hay registros. Ejecuta guardian_core.py al menos una vez.")
        return

    last = entries[-1]
    st.subheader("Último ciclo")
    st.json(last)

    # Pequeño resumen
    missing_counts = [len(e["repo"]["missing"]) for e in entries if "repo" in e]
    coherent_flags = [e["spectral"]["coherent"] for e in entries if "spectral" in e]

    st.subheader("Historial simple")
    st.line_chart(missing_counts, height=200)
    st.write("Coherencia espectral (True/False):", coherent_flags)


if __name__ == "__main__":
    main()
