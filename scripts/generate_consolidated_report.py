"""Generate a consolidated HTML report from stored validation results."""
from __future__ import annotations

import json
from datetime import datetime
from pathlib import Path
from typing import Dict, List

RESULTS_DIR = Path("data/validation/results")
REPORT_DIR = Path("reports/rh_ds_validation")
REPORT_FILE = REPORT_DIR / "index.html"


def load_results() -> List[Dict]:
    results: List[Dict] = []
    if not RESULTS_DIR.exists():
        return results
    for path in sorted(RESULTS_DIR.glob("*.json")):
        try:
            results.append(json.loads(path.read_text(encoding="utf8")))
        except json.JSONDecodeError:
            continue
    return results


def render_report(results: List[Dict]) -> str:
    rows = []
    for entry in results:
        timestamp = entry.get("timestamp", "-")
        overall = entry.get("overall_status", "UNKNOWN")
        precision = entry.get("precision", "-")
        zeros = entry.get("components", {}).get("critical_line", {}).get("metrics", {}).get("zeros_tested", "-")
        rows.append(f"<tr><td>{timestamp}</td><td>{overall}</td><td>{precision}</td><td>{zeros}</td></tr>")

    table_rows = "\n".join(rows) if rows else "<tr><td colspan='4'>No results available</td></tr>"

    return f"""
<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="utf-8" />
  <title>RH &amp; D≡Ξ Validation Report</title>
  <style>
    body {{ font-family: Arial, sans-serif; margin: 2rem; }}
    table {{ border-collapse: collapse; width: 100%; }}
    th, td {{ border: 1px solid #ccc; padding: 0.5rem; text-align: left; }}
    th {{ background-color: #f0f0f0; }}
  </style>
</head>
<body>
  <h1>RH &amp; D≡Ξ Validation Report</h1>
  <p>Generated on {datetime.utcnow().isoformat()}Z</p>
  <table>
    <thead>
      <tr><th>Timestamp</th><th>Status</th><th>Precision</th><th>Zeros Tested</th></tr>
    </thead>
    <tbody>
      {table_rows}
    </tbody>
  </table>
</body>
</html>
"""


def main() -> None:
    results = load_results()
    REPORT_DIR.mkdir(parents=True, exist_ok=True)
    REPORT_FILE.write_text(render_report(results), encoding="utf8")
    print(f"📊 Report generated at {REPORT_FILE}")


if __name__ == "__main__":
    main()
