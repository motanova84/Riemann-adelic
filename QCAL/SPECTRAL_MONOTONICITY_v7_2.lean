import Mathlib
open Real

namespace SpectralMonotonicity

def a : ℝ := 1/4

noncomputable def f (n : ℕ) : ℝ := Real.sqrt (a / (n + 1)^4 + (n + 1)^2)
noncomputable def g (x : ℝ) : ℝ := a / x^4 + x^2

lemma a_pos : a > 0 := by norm_num [a]

lemma sq_strict_mono {x y : ℝ} (hx : x ≥ 1) (hy : y ≥ 1) (hxy : x < y) : x^2 < y^2 := by nlinarith

lemma pow_four_strict_mono {x y : ℝ} (hx : x ≥ 1) (hy : y ≥ 1) (hxy : x < y) : x^4 < y^4 := by
  have h1 : x^2 < y^2 := sq_strict_mono hx hy hxy
  nlinarith [sq_nonneg (x^2 - y^2), sq_nonneg (x + y)]

lemma one_div_pow_four_strict_anti {x y : ℝ} (hx : x > 0) (hy : y > 0) (hxy : x < y) : 1 / x^4 > 1 / y^4 := by
  have h1 : x^4 < y^4 := pow_four_strict_mono (by linarith) (by linarith) hxy
  exact (one_div_lt_one_div_of_lt (by positivity) h1)

lemma a_div_pow_four_strict_anti {x y : ℝ} (hx : x > 0) (hy : y > 0) (hxy : x < y) : a / x^4 > a / y^4 := by
  have h1 : 1 / x^4 > 1 / y^4 := one_div_pow_four_strict_anti hx hy hxy
  have h2 : a > 0 := a_pos
  simpa [div_eq_mul_inv, mul_comm] using mul_lt_mul_of_pos_right h1 h2

lemma g_strict_mono {x y : ℝ} (hx : x ≥ 1) (hy : y ≥ 1) (hxy : x < y) : g x < g y := by
  dsimp [g]
  have h1 : x^2 < y^2 := sq_strict_mono hx hy hxy
  have h2 : a / x^4 > a / y^4 := a_div_pow_four_strict_anti (by linarith) (by linarith) hxy
  nlinarith

lemma g_pos {x : ℝ} (hx : x ≥ 1) : g x > 0 := by
  dsimp [g]; positivity

lemma f_eq_sqrt_g (n : ℕ) : f n = Real.sqrt (g (n + 1 : ℝ)) := by simp [f, g]
lemma g_n_pos (n : ℕ) : g (n + 1 : ℝ) > 0 := g_pos (by simp)

theorem f_strict_mono {n m : ℕ} (h : n < m) : f n < f m := by
  have hn : (n + 1 : ℝ) ≥ 1 := by simp
  have hm : (m + 1 : ℝ) ≥ 1 := by simp
  have hnm : (n + 1 : ℝ) < (m + 1 : ℝ) := by exact_mod_cast (Nat.succ_lt_succ h)
  have hg : g (n + 1 : ℝ) < g (m + 1 : ℝ) := g_strict_mono hn hm hnm
  rw [f_eq_sqrt_g n, f_eq_sqrt_g m]
  exact Real.sqrt_lt_sqrt (g_n_pos n) hg

theorem f_is_strict_mono : StrictMono f := λ n m h => f_strict_mono h
theorem f_injective : Function.Injective f := f_is_strict_mono.injective
theorem f_mono : Monotone f := f_is_strict_mono.monotone

theorem f_sq_formula (n : ℕ) : (f n)^2 = a / (n + 1)^4 + (n + 1)^2 := by
  dsimp [f]; rw [Real.sq_sqrt (by positivity : 0 ≤ a / (n + 1)^4 + (n + 1)^2)]

theorem f_sq_strict_mono {n m : ℕ} (h : n < m) : (f n)^2 < (f m)^2 := by
  rw [f_sq_formula n, f_sq_formula m]
  have hn : (n + 1 : ℝ) ≥ 1 := by simp
  have hm : (m + 1 : ℝ) ≥ 1 := by simp
  have hnm : (n + 1 : ℝ) < (m + 1 : ℝ) := by exact_mod_cast (Nat.succ_lt_succ h)
  exact g_strict_mono hn hm hnm

theorem f_tendsto_infinity : Filter.Tendsto f Filter.atTop Filter.atTop := by
  have h_bound : ∀ n : ℕ, f n ≥ (n + 1 : ℝ) := by
    intro n
    rw [← Real.sqrt_sq (by positivity : 0 ≤ (n + 1 : ℝ))]
    refine Real.sqrt_le_sqrt (by positivity) ?_
    rw [f_sq_formula n]; nlinarith
  exact Filter.tendsto_atTop_mono h_bound (by simpa using Filter.tendsto_natCast_atTop_atTop (α := ℝ))

theorem f_min_at_zero (n : ℕ) : f 0 ≤ f n := f_mono (Nat.zero_le n)

theorem f_zero_formula : f 0 = Real.sqrt 5 / 2 := by
  simp [f, a]; ring

theorem f_unique_minimum {n : ℕ} (h : f n = f 0) : n = 0 := f_injective h

def economic_return_rate (n : ℕ) : ℝ := f n

theorem economic_order_preservation {n m : ℕ} (h : n < m) : economic_return_rate n < economic_return_rate m := f_strict_mono h

theorem economic_order_isomorphism {n m : ℕ} : n < m ↔ economic_return_rate n < economic_return_rate m := by
  constructor
  · exact economic_order_preservation
  · intro h
    by_contra! h'
    rcases em' (m < n) with (hm | hm)
    · have h3 : economic_return_rate m < economic_return_rate n := economic_order_preservation hm; linarith
    · have hm_eq : m = n := Nat.le_antisymm (Nat.le_of_not_gt hm) (Nat.le_of_not_gt h')
      subst hm_eq; linarith

noncomputable def coherence (n : ℕ) : ℝ := |(-1 / (2 * (n + 1)^2 : ℝ))| / f n

theorem coherence_decreasing {n m : ℕ} (h : n < m) : coherence n > coherence m := by
  dsimp [coherence]
  have hf : f n < f m := f_strict_mono h
  have hn : (n + 1 : ℝ) < (m + 1 : ℝ) := by exact_mod_cast (Nat.succ_lt_succ h)
  have hsq : (2 * (n + 1)^2 : ℝ) < (2 * (m + 1)^2 : ℝ) := by nlinarith
  have hdiv : (1 : ℝ) / (2 * (n + 1)^2) > 1 / (2 * (m + 1)^2) :=
    (one_div_lt_one_div_of_lt (by positivity) (by nlinarith)).mpr hsq
  have hpos_n : f n > 0 := by
    apply Real.sqrt_pos.mpr; simp [g, a]; positivity
  have hpos_m : f m > 0 := by
    apply Real.sqrt_pos.mpr; simp [g, a]; positivity
  have num : |(-1 / (2 * (n + 1)^2 : ℝ))| = 1 / (2 * (n + 1)^2) := by
    simp [abs_of_neg (by positivity)]
  have num_m : |(-1 / (2 * (m + 1)^2 : ℝ))| = 1 / (2 * (m + 1)^2) := by
    simp [abs_of_neg (by positivity)]
  rw [num, num_m]
  exact (div_lt_div_iff (by positivity) (by positivity)).mpr (by nlinarith)

theorem return_stability_tradeoff {n m : ℕ} (h : n < m) :
    economic_return_rate n < economic_return_rate m ∧ coherence n > coherence m :=
  ⟨economic_order_preservation h, coherence_decreasing h⟩

end SpectralMonotonicity
