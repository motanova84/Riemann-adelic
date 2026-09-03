from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
LEAN_DIR = REPO_ROOT / "formalization" / "lean" / "RiemannAdelic"

MODULES = [
    LEAN_DIR / "Unbounded_Hpsi.lean",
    LEAN_DIR / "Trace_Fredholm.lean",
    LEAN_DIR / "Guinand_Weil_Identity.lean",
    LEAN_DIR / "Spectral_Uniqueness.lean",
]


def test_unconditional_modules_exist():
    for path in MODULES:
        assert path.exists(), f"Missing module: {path}"


def test_unconditional_modules_have_no_sorry():
    for path in MODULES:
        text = path.read_text(encoding="utf-8")
        assert "sorry" not in text, f"`sorry` found in {path.name}"

