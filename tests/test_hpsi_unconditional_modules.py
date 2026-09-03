from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
LEAN_DIR = REPO_ROOT / "formalization" / "lean" / "RiemannAdelic"

MODULES = [
    LEAN_DIR / "Unbounded_Hpsi.lean",
    LEAN_DIR / "Trace_Fredholm.lean",
    LEAN_DIR / "Guinand_Weil_Identity.lean",
    LEAN_DIR / "Poisson_Mellin.lean",
    LEAN_DIR / "Spectral_Mechanics.lean",
    LEAN_DIR / "Hadamard_Uniqueness.lean",
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
    assert "theorem essentiallySelfAdjoint_from_kernel_triviality" in text
    assert "LocalL2DivergenceOnIoc" in text
    assert "LocalModeNotIntegrable" in text
    assert "def LocalL2DivergenceOnIoc (σ : Bool) (C : ℂ) : Prop :=\n  True" not in text
    assert "def LocalModeNotIntegrable (σ : Bool) (C : ℂ) : Prop :=\n  True" not in text


def test_unbounded_hpsi_norm_density_closed_without_sorry():
    path = LEAN_DIR / "Unbounded_Hpsi.lean"
    text = path.read_text(encoding="utf-8")
    assert "theorem localDeficiencyIntegrand_eq" in text
    assert "lemma norm_cpow_of_pos_real" in text
    assert "lemma norm_cpow_I_mul_real" in text
    lemma_start = text.find("theorem localDeficiencyIntegrand_eq")
    assert lemma_start != -1
    lemma_block = text[lemma_start:lemma_start + 1500]
    assert "sorry" not in lemma_block


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


def test_spectral_uniqueness_no_true_placeholders():
    path = LEAN_DIR / "Spectral_Uniqueness.lean"
    text = path.read_text(encoding="utf-8")
    assert "def ResolventIsCompact : Prop := ∀ z : ℂ, True" not in text
    assert "def PurelyDiscreteSpectrum : Prop := True" not in text
    assert "IsCompact (Set.range (R.resolvent z))" in text


def test_trace_fredholm_schatten_contract_present():
    path = LEAN_DIR / "Trace_Fredholm.lean"
    text = path.read_text(encoding="utf-8")
    assert "def IsHilbertSchmidtResolvent" in text
    assert "def ResolventInSchattenTwo" in text
    assert "resolvent_schatten_two" in text


def test_poisson_mellin_tripartite_contract_present():
    path = LEAN_DIR / "Poisson_Mellin.lean"
    text = path.read_text(encoding="utf-8")
    assert "structure PoissonMellinData" in text
    assert "theorem trace_formula_poisson_mellin_identity" in text
    assert "theorem fredholm_det_identically_equals_xi" in text


def test_spectral_mechanics_core_theorems_present():
    path = LEAN_DIR / "Spectral_Mechanics.lean"
    text = path.read_text(encoding="utf-8")
    assert "theorem log_deriv_fredholm_eq_resolvent_trace" in text
    assert "theorem adelic_semigroup_trace_expansion" in text
    assert "theorem mellin_prime_deltas_eq_zeta_log_deriv" in text
    assert "theorem trace_match_derived" in text


def test_hadamard_uniqueness_bridge_present():
    path = LEAN_DIR / "Hadamard_Uniqueness.lean"
    text = path.read_text(encoding="utf-8")
    assert "theorem entire_eq_of_log_deriv_eq_and_eq_at_point" in text
    assert "theorem spectral_determinant_identically_equals_xi" in text
