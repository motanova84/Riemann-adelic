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


def test_unbounded_hpsi_removes_first_axiom_bridge():
    path = LEAN_DIR / "Unbounded_Hpsi.lean"
    text = path.read_text(encoding="utf-8")
    assert "axiom essentiallySelfAdjoint_of_deficiency_zero" not in text
    assert "theorem essentiallySelfAdjoint_of_deficiency_zero_proof" in text


def test_remaining_axiom_names_removed_from_module_chain():
    checks = {
        LEAN_DIR / "Trace_Fredholm.lean": [
            "axiom fredholm_determinant_is_entire",
        ],
        LEAN_DIR / "Spectral_Uniqueness.lean": [
            "axiom resolvent_compact_axiom",
            "axiom purely_discrete_of_compact_resolvent",
        ],
    }
    for path, forbidden in checks.items():
        text = path.read_text(encoding="utf-8")
        for token in forbidden:
            assert token not in text, f"Forbidden axiom bridge still present: {token}"
