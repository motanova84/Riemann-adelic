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
    LEAN_DIR / "Canonical_Instances.lean",
    LEAN_DIR / "Coronacion_Final.lean",
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


def test_unbounded_hpsi_dyadic_local_closure_present():
    path = LEAN_DIR / "Unbounded_Hpsi.lean"
    text = path.read_text(encoding="utf-8")
    assert "lemma pairwise_disjoint_Ioc_diadic" in text
    assert "lemma volume_Ioc_diadic" in text
    assert "lemma lintegral_Ioc_diadic_ge" in text
    assert "theorem lintegral_x_pow_neg_two_Ioc_eq_top" in text


def test_unbounded_hpsi_causal_kernel_bridge_present():
    path = LEAN_DIR / "Unbounded_Hpsi.lean"
    text = path.read_text(encoding="utf-8")
    assert "def integratingExponent" in text
    assert "def integratingFactor" in text
    assert "def SatisfiesAdjointODE" in text
    assert "structure DeficiencyODEUniquenessWitness" in text
    assert "structure LocalDivergenceWitness" in text
    assert "theorem deficiency_mode_unique" in text
    assert "theorem local_mode_not_integrable_of_ne_zero" in text
    assert "theorem adjoint_solution_is_zero_of_L2" in text
    assert "theorem kernel_adjoint_trivial_unconditional" in text
    assert "theorem deficiency_indices_zero_unconditional" in text
    assert "toFun : H → (ℝ → ℂ)" in text
    assert "adjoint_solution_zero_of_L2" in text
    assert "deficiencyCoeff" in text
    assert "kernel_coeff_nonzero_implies_not_integrable" in text
    assert "kernel_coeff_integrable" in text
    assert "structure ArchimedeanDifferentialModel" in text
    assert "def makeFirstFrontHypotheses" in text


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
    assert "def xiShifted" in text
    assert "lemma wronskian_zero_of_log_deriv_eq" in text
    assert "lemma deriv_div_eq_zero_of_log_deriv_eq" in text
    assert "def zeroSet" in text
    assert "def regularDomain" in text
    assert "lemma preconnected_compl_countable_zeros" in text
    assert "lemma quotient_constant_on_connected_domain" in text
    assert "lemma eq_on_univ_of_eq_on_dense" in text
    assert "structure HolomorphicQuotientRigidityWitness" not in text
    assert "theorem entire_rigidity_unconditional" in text
    assert "theorem spectral_rigidity_quotient" in text
    assert "theorem entire_rigidity_of_log_deriv_match" in text
    assert "structure UnconditionalSpectralIdentificationData" in text
    assert "theorem unconditional_spectral_identification" in text


def test_trace_fredholm_schatten_contract_present():
    path = LEAN_DIR / "Trace_Fredholm.lean"
    text = path.read_text(encoding="utf-8")
    assert "def IsHilbertSchmidtResolvent" in text
    assert "def InSchattenTwoClass" in text
    assert "lemma integrable_dilation_power" in text
    assert "lemma norm_sq_resolvent_kernel" in text
    assert "def resolventKernelLocal" in text
    assert "structure KernelSchattenWitness" in text
    assert "def ResolventInSchattenTwo" in text
    assert "resolvent_schatten_two" in text
    assert "structure ResolventData" in text
    assert "zeros_eq_spectrum :" in text


def test_poisson_mellin_tripartite_contract_present():
    path = LEAN_DIR / "Poisson_Mellin.lean"
    text = path.read_text(encoding="utf-8")
    assert "structure PoissonMellinData" in text
    assert "theorem trace_formula_poisson_mellin_identity" in text
    assert "theorem fredholm_det_identically_equals_xi" in text


def test_spectral_mechanics_core_theorems_present():
    path = LEAN_DIR / "Spectral_Mechanics.lean"
    text = path.read_text(encoding="utf-8")
    assert "structure PoissonGlobalDecompositionData" in text
    assert "theorem log_deriv_fredholm_eq_resolvent_trace" in text
    assert "theorem adelic_semigroup_trace_expansion" in text
    assert "theorem mellin_prime_deltas_eq_zeta_log_deriv" in text
    assert "theorem trace_match_derived" in text
    assert "theorem poisson_global_log_deriv_match" in text


def test_guinand_weil_global_log_deriv_bridge_present():
    path = LEAN_DIR / "Guinand_Weil_Identity.lean"
    text = path.read_text(encoding="utf-8")
    assert "poissonGlobal" in text
    assert "theorem fredholm_log_derivative_eq_xi_log_derivative" in text
    assert "noncomputable def concreteXi" in text
    assert "noncomputable def archimedeanTraceTerm" in text
    assert "noncomputable def primeTraceSum" in text
    assert "noncomputable def totalGeometricTrace" in text
    assert "structure TraceIdentityBridge" in text
    assert "def GeometricXiLogDerivClosure" in text
    assert "lemma log_deriv_mul" in text
    assert "lemma hasDerivAt_crit_line" in text
    assert "lemma deriv_factor_w" in text
    assert "lemma deriv_factor_w_sub_one" in text
    assert "lemma hasDerivAt_crit_line_half" in text
    assert "lemma deriv_crit_line_half" in text
    assert "lemma deriv_factor_archimedean_pow" in text
    assert "lemma log_deriv_archimedean_factor" in text
    assert "lemma deriv_factor_gamma" in text
    assert "lemma log_deriv_gamma_factor" in text
    assert "lemma deriv_factor_zeta" in text
    assert "lemma log_deriv_zeta_factor" in text
    assert "theorem concreteXi_log_derivative_expansion" in text
    assert "theorem concreteXi_log_derivative_expansion_exact" in text
    assert "theorem geometric_xi_log_deriv_closure_proof" in text
    assert "theorem geometric_xi_log_deriv_closure_unconditional" in text
    assert "geometric_eq_xi_log_deriv" not in text
    assert "theorem log_derivative_eq_xi_log_derivative" in text


def test_hadamard_uniqueness_bridge_present():
    path = LEAN_DIR / "Hadamard_Uniqueness.lean"
    text = path.read_text(encoding="utf-8")
    assert "theorem entire_eq_of_log_deriv_eq_and_eq_at_point" in text
    assert "theorem spectral_determinant_identically_equals_xi" in text


def test_canonical_instances_constructors_present():
    path = LEAN_DIR / "Canonical_Instances.lean"
    text = path.read_text(encoding="utf-8")
    assert "structure CanonicalArchimedeanData" in text
    assert "def canonicalArchimedeanModel" in text
    assert "structure CanonicalTraceBridgeData" in text
    assert "def canonicalTraceBridge" in text
    assert "def canonicalGeometricXiClosure" in text


def test_coronacion_final_closure_present():
    path = LEAN_DIR / "Coronacion_Final.lean"
    text = path.read_text(encoding="utf-8")
    assert "structure EssentialSpectrumRealityWitness" not in text
    assert "h_spec_real : EssSelfAdjoint M" in text
    assert "(h_rigidity :" not in text
    assert "R.isSpectralPoint s → s.im = 0" in text
    assert "entire_rigidity_unconditional" in text
    assert "theorem riemann_hypothesis_cosmic_closure" in text
    assert "theorem critical_line_localization_shifted" in text
