"""Construct a lightweight RDF graph from QCAL JSON-LD descriptors."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Iterable, Iterator, List, MutableMapping, Sequence, Tuple

PREFIXES = {
    "@base": None,
    "dc": "http://purl.org/dc/elements/1.1/",
    "formal": "https://qcal.example/formal#",
    "sem": "https://qcal.example/semantic#",
    "hash": "https://qcal.example/hash#",
    "freq": "https://qcal.example/frequency#",
    "prov": "http://www.w3.org/ns/prov#",
    "qcal": "urn:qcal:",
    "rdfs": "http://www.w3.org/2000/01/rdf-schema#",
    "xsd": "http://www.w3.org/2001/XMLSchema#",
}

REQUIRED_FIELDS = [
    "@id",
    "dc:title",
    "formal:kernel",
    "formal:proof",
    "formal:axioms",
    "sem:dependsOn",
    "hash:sha256",
    "freq:Hz",
]


def load_entries(paths: Sequence[Path]) -> Iterator[Tuple[Path, MutableMapping[str, object]]]:
    for path in paths:
        data = json.loads(path.read_text(encoding="utf-8"))
        if isinstance(data, list):
            for entry in data:
                if isinstance(entry, MutableMapping):
                    yield path, entry
                else:
                    raise TypeError(f"Entries in {path} must be JSON objects.")
        elif isinstance(data, MutableMapping):
            yield path, data
        else:
            raise TypeError(f"File {path} must contain a JSON object or array of objects.")


def ensure_fields(entry: MutableMapping[str, object], path: Path) -> None:
    missing = [field for field in REQUIRED_FIELDS if field not in entry]
    if missing:
        raise KeyError(f"File {path} is missing fields: {', '.join(missing)}")


def literal(value: object) -> str:
    if isinstance(value, (int, float)):
        return f"\"{value}\"^^xsd:double"
    value_str = str(value).replace("\"", '\\"')
    return f'"{value_str}"'


def write_turtle(paths: Sequence[Path], output: Path) -> None:
    lines: List[str] = []
    for prefix, iri in PREFIXES.items():
        if prefix == "@base":
            continue
        lines.append(f"@prefix {prefix}: <{iri}> .")
    lines.append("")

    for path, entry in load_entries(paths):
        ensure_fields(entry, path)
        subject = entry["@id"]
        lines.append(f"<{subject}> a formal:MathematicalStatement ;")
        axioms = entry.get("formal:axioms", [])
        if isinstance(axioms, list):
            axioms_literal = ", ".join(str(item) for item in axioms)
        else:
            axioms_literal = str(axioms)

        triples = [
            ("dc:title", entry["dc:title"]),
            ("formal:kernel", entry["formal:kernel"]),
            ("formal:proof", entry.get("formal:proof")),
            ("formal:axioms", axioms_literal),
            ("hash:sha256", entry.get("hash:sha256")),
            ("freq:Hz", entry.get("freq:Hz")),
        ]
        for predicate, value in triples:
            if value is None:
                continue
            lines.append(f"    {predicate} {literal(value)} ;")

        dependencies = entry.get("sem:dependsOn", [])
        if isinstance(dependencies, Iterable) and not isinstance(dependencies, (str, bytes)):
            for dep in dependencies:
                lines.append(f"    prov:wasDerivedFrom <{dep}> ;")

        lines[-1] = lines[-1].rstrip(" ;") + " ."
        lines.append("")

    output.write_text("\n".join(lines).rstrip() + "\n", encoding="utf-8")


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Build a Turtle graph from JSON-LD theorem descriptors.")
    parser.add_argument("paths", nargs="+", type=Path, help="Input JSON-LD files.")
    parser.add_argument("--output", type=Path, default=Path("graph.ttl"), help="Output Turtle file path.")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    write_turtle(args.paths, args.output)
    print(f"Graph written to {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
