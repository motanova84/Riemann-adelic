"""Interactive visualisation utilities for RH & D≡Ξ validation."""
from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Dict

import plotly.graph_objects as go
from plotly.subplots import make_subplots

try:  # pragma: no cover - optional dependency in headless environments
    import ipywidgets as widgets
    from IPython.display import HTML, display
except Exception:  # pragma: no cover
    widgets = None
    HTML = display = None


class ValidationDashboard:
    """Render interactive dashboards for stored validation results."""

    def __init__(self) -> None:
        self.results_data: Dict[str, Any] = {}

    def load_validation_data(self, results_file: str) -> None:
        path = Path(results_file)
        if not path.exists():
            raise FileNotFoundError(results_file)
        self.results_data = json.loads(path.read_text(encoding="utf8"))

    # ------------------------------------------------------------------
    # Plot construction helpers
    # ------------------------------------------------------------------
    def create_validation_summary(self) -> go.Figure:
        if not self.results_data:
            raise RuntimeError("Validation data not loaded")

        fig = make_subplots(
            rows=2,
            cols=2,
            subplot_titles=(
                "Overall Validation Status",
                "Zero Distribution",
                "D vs Ξ Relative Error",
                "Non-vanishing Region Minimums",
            ),
            specs=[[{"type": "indicator"}, {"type": "scatter"}], [{"type": "bar"}, {"type": "bar"}]],
        )

        status = self.results_data.get("overall_status", "UNKNOWN")
        fig.add_trace(
            go.Indicator(
                mode="gauge+number",
                value=1.0 if status == "PASSED" else 0.0,
                title={"text": "Validation"},
                gauge={"axis": {"range": [0, 1]}, "bar": {"color": "green" if status == "PASSED" else "red"}},
            ),
            row=1,
            col=1,
        )

        critical = self.results_data.get("components", {}).get("critical_line", {})
        zeros = critical.get("metrics", {}).get("spacing", {})
        if critical:
            imag_values = self.results_data.get("critical_line_samples", [])
            fig.add_trace(
                go.Scatter(x=[0.5] * len(imag_values), y=imag_values, mode="markers", marker=dict(size=4)),
                row=1,
                col=2,
            )

        ds_equiv = self.results_data.get("components", {}).get("ds_equivalence", {})
        if ds_equiv:
            errors = ds_equiv.get("metrics", {}).get("relative_errors", [])
            fig.add_trace(
                go.Bar(x=list(range(len(errors))), y=errors, name="Relative Error"),
                row=2,
                col=1,
            )

        non_vanishing = self.results_data.get("components", {}).get("non_vanishing", {})
        if non_vanishing:
            region_reports = non_vanishing.get("metrics", {}).get("region_reports", [])
            minima = [r.get("min_abs_value", 0.0) for r in region_reports]
            fig.add_trace(
                go.Bar(x=list(range(len(minima))), y=minima, name="Min |D_ratio|")
            , row=2, col=2)

        fig.update_layout(height=600, showlegend=False, title="RH & D≡Ξ Validation Overview")
        return fig

    def create_live_validation_widget(self):  # pragma: no cover - UI helper
        if widgets is None or display is None:
            raise RuntimeError("ipywidgets is required for the interactive widget")

        precision_slider = widgets.IntSlider(value=30, min=15, max=100, step=5, description="Precision")
        max_zeros_slider = widgets.IntSlider(value=100, min=10, max=1000, step=10, description="Zeros")
        run_button = widgets.Button(description="Run validation", button_style="success")
        output = widgets.Output()

        def _on_click(_):
            with output:
                output.clear_output()
                print("Connect this callback to run_complete_validation.py to perform live runs.")

        run_button.on_click(_on_click)
        controls = widgets.VBox([precision_slider, max_zeros_slider, run_button])
        layout = widgets.HBox([controls, output])
        display(layout)


__all__ = ["ValidationDashboard"]
