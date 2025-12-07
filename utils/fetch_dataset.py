"""Utility to fetch QCAL-CLOUD datasets from Zenodo or Hugging Face."""
from __future__ import annotations

import argparse
import hashlib
import json
import logging
import os
from pathlib import Path
from typing import Dict, Iterable, Tuple

import requests

DATASETS = {
    "zeros_t1e3.csv": {
        "zenodo": "https://zenodo.org/record/000000/files/zeros_t1e3.csv?download=1",
        "huggingface": "https://huggingface.co/datasets/qcal-cloud/riemann-spectral-validation/resolve/main/zeros_t1e3.csv",
        "sha256": "8874683b52dc53da77e21a0a694cf0ea32b293d0f1d9349fadd074f2bcf511a6",
    },
    "evac_rpsi_samples.csv": {
        "zenodo": "https://zenodo.org/record/000000/files/evac_rpsi_samples.csv?download=1",
        "huggingface": "https://huggingface.co/datasets/qcal-cloud/riemann-spectral-validation/resolve/main/evac_rpsi_samples.csv",
        "sha256": "e80f7d5d8dfc0e3fa02d45f50fe2a9b4f27f38f18d79f41060b280f0a3386f14",
    },
    "spectral_results.json": {
        "zenodo": "https://zenodo.org/record/000000/files/spectral_results.json?download=1",
        "huggingface": "https://huggingface.co/datasets/qcal-cloud/riemann-spectral-validation/resolve/main/spectral_results.json",
        "sha256": "64b5f5c4701a6f725953c2f03612a02dd68fc0fef46c8e8a63a0140d41d79c66",
    },
}


LOGGER = logging.getLogger("fetch_dataset")


def download_file(url: str, destination: Path) -> None:
    LOGGER.info("Downloading %s", url)
    response = requests.get(url, timeout=60)
    response.raise_for_status()
    destination.write_bytes(response.content)


def verify_checksum(path: Path, expected: str) -> bool:
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    if digest != expected:
        LOGGER.error("Checksum mismatch for %s", path)
        return False
    LOGGER.info("Verified checksum for %s", path)
    return True


def fetch_all(target_dir: Path, source: str) -> Iterable[Tuple[str, bool]]:
    target_dir.mkdir(parents=True, exist_ok=True)
    results = []
    for filename, metadata in DATASETS.items():
        url = metadata.get(source)
        if not url:
            LOGGER.warning("Source %s unavailable for %s", source, filename)
            continue
        destination = target_dir / filename
        download_file(url, destination)
        ok = verify_checksum(destination, metadata["sha256"])
        results.append((filename, ok))
    return results


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Fetch QCAL datasets")
    parser.add_argument("--target", type=Path, default=Path("data/external"))
    parser.add_argument("--source", choices=["zenodo", "huggingface"], default="huggingface")
    parser.add_argument("--json", action="store_true", help="Emit JSON summary")
    return parser.parse_args()


def configure_logging() -> None:
    level = logging.INFO if os.environ.get("FETCH_DATASET_DEBUG") != "1" else logging.DEBUG
    logging.basicConfig(level=level, format="%(levelname)s: %(message)s")


def main() -> None:
    args = parse_args()
    configure_logging()

    LOGGER.info("Fetching datasets to %s from %s", args.target, args.source)
    results = fetch_all(args.target, args.source)

    if args.json:
        output = {filename: {"ok": ok} for filename, ok in results}
        print(json.dumps(output))


if __name__ == "__main__":
    main()
