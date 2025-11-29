"""Plotly Dash dashboard for QCAL-CLOUD live monitoring."""

from __future__ import annotations

import asyncio
import json
from datetime import datetime
from pathlib import Path
from typing import Any, Dict, List

import dash
import plotly.express as px
import plotly.graph_objects as go
import requests
from dash import Dash, dcc, html

API_BASE = "http://localhost:8000"


def fetch_status() -> Dict[str, Any]:
    response = requests.get(f"{API_BASE}/api/status", timeout=10)
    response.raise_for_status()
    return response.json()


def layout(app: Dash) -> html.Div:
    data = fetch_status()
    latest = data.get("latest", [])
    metrics = data.get("metrics", {})

    times = [datetime.fromtimestamp(row["timestamp"]) for row in latest]
    errors = [row.get("relative_error", None) for row in latest]
    nodes = [row.get("node_id", "unknown") for row in latest]

    error_fig = go.Figure()
    if errors:
        error_fig.add_trace(
            go.Scatter(x=times, y=errors, mode="lines+markers", text=nodes, name="Relative error"),
        )
        error_fig.update_layout(yaxis_title="Relative Error", xaxis_title="Timestamp")

    node_counts = {node: nodes.count(node) for node in set(nodes)}
    map_fig = px.bar(x=list(node_counts.keys()), y=list(node_counts.values()), labels={"x": "Node", "y": "Validations"})

    evac_series = []
    dataset_path = Path(__file__).resolve().parents[1] / "QCAL-CLOUD" / "datasets" / "evac_rpsi_samples.csv"
    if dataset_path.exists():
        for line in dataset_path.read_text().splitlines()[1:]:
            freq, value = line.split(",")
            evac_series.append({"frequency": float(freq), "evac": float(value)})
    evac_fig = px.line(evac_series, x="frequency", y="evac", title="Evac(RΨ) vs Frequency")

    coherence = metrics.get("coherence_error")
    coherence_text = f"Global coherence error: {coherence:.2e}" if coherence else "Global coherence error: n/a"

    return html.Div(
        [
            html.H1("QCAL-CLOUD Live Validation"),
            html.P(coherence_text),
            dcc.Graph(figure=error_fig),
            dcc.Graph(figure=map_fig),
            dcc.Graph(figure=evac_fig),
        ]
    )


app = dash.Dash(__name__)
app.layout = lambda: layout(app)


if __name__ == "__main__":
    app.run_server(debug=True)
