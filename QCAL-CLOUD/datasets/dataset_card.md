# QCAL-CLOUD Dataset Card

## Citation and Provenance

* **Primary DOI (Zenodo)**: _pending_ – upload using the metadata below.
* **Hugging Face Dataset ID**: `qcal-cloud/riemann-spectral-validation`
* **Source Repository**: https://github.com/jmmotaburr/-jmmotaburr-riemann-adelic

## Contents

| File | Description | Format | Key Fields |
| ---- | ----------- | ------ | ---------- |
| `zeros_t1e3.csv` | Truncated Odlyzko zero sample (first 10 zeros) | CSV | `zero_index`, `gamma` |
| `evac_rpsi_samples.csv` | Simulated Evac(RΨ) measurements across driving frequencies | CSV | `frequency_hz`, `evac_rpsi` |
| `spectral_results.json` | Aggregated validation summaries per node | JSON | `node_id`, `timestamp`, `relative_error`, `precision`, `evac_frequency` |

## Reproducibility Notes

* All CSV files use UTF-8 encoding and include headers.
* Numerical values are recorded with at least six significant digits.
* The JSON document follows RFC 8259 and can be ingested via `json.load`.

## License

The datasets inherit the repository license (see `LICENSE`) unless overridden by
the hosting platform.

## Fetch Script

Use `utils/fetch_dataset.py` to download and cache the published artefacts:

```bash
python -m utils.fetch_dataset --target data/external --source huggingface
```

The script resolves URLs for both Zenodo and Hugging Face mirrors, verifies the
SHA256 checksum, and emits structured logs suitable for CI pipelines.
