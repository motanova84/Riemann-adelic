#!/usr/bin/env python3
"""
Aggregate validation results from multiple runs.

This script collects validation results from various validation scripts
and creates a consolidated report for production monitoring and analysis.

Usage:
    python scripts/aggregate_results.py [--output-dir DIR] [--format json|html]
"""

import argparse
import json
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, List, Any


def load_validation_results(data_dir: Path) -> List[Dict[str, Any]]:
    """
    Load validation results from the data directory.

    Args:
        data_dir: Path to directory containing validation results

    Returns:
        List of validation result dictionaries
    """
    results = []

    # Check for validation results in various locations
    result_paths = [
        data_dir / "validation" / "results",
        data_dir / "results",
        Path("logs") / "validation",
    ]

    for result_dir in result_paths:
        if not result_dir.exists():
            continue

        # Load JSON result files
        for json_file in sorted(result_dir.glob("*.json")):
            try:
                with open(json_file, "r", encoding="utf-8") as f:
                    result = json.load(f)
                    result["source_file"] = str(json_file)
                    results.append(result)
            except (json.JSONDecodeError, IOError) as e:
                print(f"⚠️  Warning: Could not load {json_file}: {e}", file=sys.stderr)

    return results


def aggregate_statistics(results: List[Dict[str, Any]]) -> Dict[str, Any]:
    """
    Aggregate statistics from multiple validation results.

    Args:
        results: List of validation result dictionaries

    Returns:
        Dictionary with aggregated statistics
    """
    if not results:
        return {
            "total_runs": 0,
            "successful_runs": 0,
            "failed_runs": 0,
            "success_rate": 0.0,
            "avg_precision": 0,
            "latest_run": None,
        }

    total = len(results)
    successful = sum(
        1
        for r in results
        if r.get("overall_status") == "PASS" or r.get("status") == "success"
    )
    failed = total - successful

    # Calculate average precision
    precisions = [r.get("precision", 0) for r in results if "precision" in r]
    avg_precision = sum(precisions) / len(precisions) if precisions else 0

    # Get latest run
    sorted_results = sorted(results, key=lambda r: r.get("timestamp", ""), reverse=True)
    latest = sorted_results[0] if sorted_results else None

    return {
        "total_runs": total,
        "successful_runs": successful,
        "failed_runs": failed,
        "success_rate": (successful / total * 100) if total > 0 else 0.0,
        "avg_precision": avg_precision,
        "latest_run": latest,
        "aggregation_timestamp": datetime.now(timezone.utc).isoformat(),
    }


def generate_json_report(stats: Dict[str, Any], output_file: Path) -> None:
    """
    Generate JSON format report.

    Args:
        stats: Aggregated statistics dictionary
        output_file: Path to output JSON file
    """
    output_file.parent.mkdir(parents=True, exist_ok=True)
    with open(output_file, "w", encoding="utf-8") as f:
        json.dump(stats, f, indent=2, ensure_ascii=False)
    print(f"📊 JSON report generated: {output_file}")


def generate_html_report(stats: Dict[str, Any], output_file: Path) -> None:
    """
    Generate HTML format report.

    Args:
        stats: Aggregated statistics dictionary
        output_file: Path to output HTML file
    """
    latest = stats.get("latest_run", {}) or {}

    html_content = f"""<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>QCAL Production Validation Report</title>
    <style>
        body {{
            font-family: 'Segoe UI', Tahoma, Geneva, Verdana, sans-serif;
            margin: 0;
            padding: 20px;
            background: #f5f5f5;
        }}
        .container {{
            max-width: 1200px;
            margin: 0 auto;
            background: white;
            padding: 30px;
            border-radius: 8px;
            box-shadow: 0 2px 4px rgba(0,0,0,0.1);
        }}
        h1 {{
            color: #2c3e50;
            border-bottom: 3px solid #3498db;
            padding-bottom: 10px;
        }}
        .stats-grid {{
            display: grid;
            grid-template-columns: repeat(auto-fit, minmax(200px, 1fr));
            gap: 20px;
            margin: 30px 0;
        }}
        .stat-card {{
            background: #ecf0f1;
            padding: 20px;
            border-radius: 5px;
            text-align: center;
        }}
        .stat-value {{
            font-size: 2em;
            font-weight: bold;
            color: #2c3e50;
        }}
        .stat-label {{
            color: #7f8c8d;
            margin-top: 5px;
        }}
        .success {{ color: #27ae60; }}
        .failed {{ color: #e74c3c; }}
        .timestamp {{
            color: #95a5a6;
            font-size: 0.9em;
            margin-top: 20px;
        }}
        .latest-run {{
            background: #e8f4f8;
            padding: 15px;
            border-left: 4px solid #3498db;
            margin-top: 30px;
        }}
    </style>
</head>
<body>
    <div class="container">
        <h1>🔬 QCAL Production Validation Report</h1>

        <div class="stats-grid">
            <div class="stat-card">
                <div class="stat-value">{stats['total_runs']}</div>
                <div class="stat-label">Total Runs</div>
            </div>
            <div class="stat-card">
                <div class="stat-value success">{stats['successful_runs']}</div>
                <div class="stat-label">Successful</div>
            </div>
            <div class="stat-card">
                <div class="stat-value failed">{stats['failed_runs']}</div>
                <div class="stat-label">Failed</div>
            </div>
            <div class="stat-card">
                <div class="stat-value">{stats['success_rate']:.1f}%</div>
                <div class="stat-label">Success Rate</div>
            </div>
            <div class="stat-card">
                <div class="stat-value">{stats['avg_precision']:.0f}</div>
                <div class="stat-label">Avg Precision (DPS)</div>
            </div>
        </div>

        <div class="latest-run">
            <h3>Latest Run</h3>
            <p><strong>Status:</strong> {latest.get('overall_status', latest.get('status', 'N/A'))}</p>
            <p><strong>Timestamp:</strong> {latest.get('timestamp', 'N/A')}</p>
            <p><strong>Precision:</strong> {latest.get('precision', 'N/A')} decimal places</p>
        </div>

        <p class="timestamp">Report generated: {stats.get('aggregation_timestamp', 'N/A')}</p>
    </div>
</body>
</html>
"""

    output_file.parent.mkdir(parents=True, exist_ok=True)
    with open(output_file, "w", encoding="utf-8") as f:
        f.write(html_content)
    print(f"📊 HTML report generated: {output_file}")


def main():
    """Main entry point for the aggregation script."""
    parser = argparse.ArgumentParser(
        description="Aggregate validation results from multiple runs"
    )
    parser.add_argument(
        "--data-dir",
        type=Path,
        default=Path("data"),
        help="Directory containing validation results (default: data)",
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path("results"),
        help="Directory for aggregated reports (default: results)",
    )
    parser.add_argument(
        "--format",
        choices=["json", "html", "both"],
        default="both",
        help="Output format (default: both)",
    )

    args = parser.parse_args()

    print("🔍 Loading validation results...")
    results = load_validation_results(args.data_dir)
    print(f"   Found {len(results)} validation result(s)")

    print("📊 Aggregating statistics...")
    stats = aggregate_statistics(results)

    print("💾 Generating reports...")
    if args.format in ["json", "both"]:
        generate_json_report(stats, args.output_dir / "aggregated_results.json")

    if args.format in ["html", "both"]:
        generate_html_report(stats, args.output_dir / "aggregated_results.html")

    print("\n✅ Aggregation complete!")
    print(f"   Success rate: {stats['success_rate']:.1f}%")
    print(f"   Total runs: {stats['total_runs']}")


if __name__ == "__main__":
    main()
