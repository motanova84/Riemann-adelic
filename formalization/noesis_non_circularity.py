"""NOĒSIS non-circularity guard.

The spectral construction must not import the zeros of zeta as input.
This guard is intentionally lexical and conservative: it reports forbidden
identifiers in files designated as construction files. It is a CI guard, not
a mathematical proof of independence.
"""
from __future__ import annotations

from pathlib import Path
import re
import sys

FORBIDDEN = (
    r"\bzeta[_ ]?zeros?\b",
    r"\bzero[_ ]?set\b",
    r"\bcritical[_ ]?zeros?\b",
    r"\brho[_ ]?n\b",
    r"\bt[_ ]?n\b",
    r"\bzeros?\(.*zeta",
)

DEFAULT_ROOTS = (
    Path("formalization/lean/RiemannAdelic/Noesis"),
)


def scan(paths: tuple[Path, ...]) -> list[str]:
    failures: list[str] = []
    patterns = [re.compile(p, re.IGNORECASE) for p in FORBIDDEN]
    for root in paths:
        if not root.exists():
            continue
        for path in root.rglob("*.lean"):
            text = path.read_text(encoding="utf-8")
            for lineno, line in enumerate(text.splitlines(), 1):
                if any(pattern.search(line) for pattern in patterns):
                    failures.append(f"{path}:{lineno}: forbidden zero dependency")
    return failures


if __name__ == "__main__":
    failures = scan(DEFAULT_ROOTS)
    if failures:
        print("NOĒSIS NON-CIRCULARITY: FAIL")
        print("\n".join(failures))
        sys.exit(1)
    print("NOĒSIS NON-CIRCULARITY: PASS")
    print("No forbidden zero-dependency identifiers found in construction files.")
