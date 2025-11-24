# QCAL-CLOUD Distributed Validation Network

QCAL-CLOUD provides the scaffolding for a distributed, volunteer-friendly network
that executes the **`validate_v5_coronacion.py`** and **`Evac_Rpsi`** validation
routines across heterogeneous nodes. The platform couples lightweight clients,
a FastAPI-based coordination service, and real-time dashboards so that
contributors can reproduce spectral certificates with transparent provenance.

## Directory Overview

```
QCAL-CLOUD/
├── node_client/          # Lightweight worker that runs local validations
├── coordinator/          # Central FastAPI service that aggregates uploads
├── datasets/             # Canonical CSV/JSON snapshots used for validations
└── README.md             # Project overview and onboarding instructions
```

### Node Client

* `qcal_worker.py` reads `config.json`, schedules validation runs, and pushes
  signed result bundles back to the coordinator via REST and WebSockets.
* `requirements.txt` enumerates the minimum dependencies for a standalone node
  installation that mirrors the GitHub Actions workflow.

### Coordinator

* `qcal_server.py` encapsulates the orchestration logic: queue management,
  sqlite-backed persistence, and broadcast of live metrics.
* `dashboard_api.py` exposes REST and WebSocket endpoints consumed by the
  dashboard in `dashboard/`.
* `data/validation_logs/` stores append-only JSONL certificates alongside a
  SQLite database for queryable summaries.

### Datasets

Curated, reproducible datasets are colocated here for convenience during local
experiments. When publishing to Zenodo or Hugging Face, reuse the same schema
and include the provided `dataset_card.md`.

## Running the Coordinator

```bash
uvicorn coordinator.dashboard_api:app --reload --host 0.0.0.0 --port 8000 --app-dir QCAL-CLOUD
```

This starts the API server with:

* `POST /api/upload` – receive validation bundles from nodes or CI runners.
* `GET /api/status` – aggregate metrics for monitoring.
* `GET /api/datasets` – list published dataset snapshots.
* `WebSocket /ws/live` – push incremental updates to dashboards.

## Running a Node

```bash
python QCAL-CLOUD/node_client/qcal_worker.py --config QCAL-CLOUD/node_client/config.json
```

The worker will:

1. Invoke the repository validation scripts with the requested precision.
2. Store artifacts in `node_client/output/`.
3. Upload the certificate to the coordinator.
4. Stream heartbeat messages through the WebSocket channel.

## Dashboard

The `dashboard/` directory contains a Plotly Dash skeleton that consumes the
`/api/status` and `/ws/live` endpoints to render:

* **Live Validation Feed** – relative errors, timestamps, and node identifiers.
* **Node Map** – symbolic placement of active nodes.
* **Global Coherence Metric** – rolling mean error threshold (< 1e-6).
* **Spectral Visualisations** – Evac(RΨ) distributions and zero density plots.

Deploy the dashboard on Streamlit Cloud, Vercel, or any ASGI-compatible host.

## Next Steps

* Publish the datasets under dual hosting (Zenodo + Hugging Face).
* Invite external validators via the provided GitHub Actions workflow.
* Extend GPU/TPU acceleration inside the validation scripts using JAX/CuPy.

The result is a transparent, falsifiable network where each certificate is
reproducible, automatically aggregated, and visualised in real time.
