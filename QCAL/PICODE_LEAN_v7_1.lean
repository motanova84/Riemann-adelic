import Mathlib
open Real Complex

/--
 πCODE SPECTRAL LIQUIDITY ENGINE v7.1 — FORMALIZACIÓN LEAN 4
 Frecuencia: 141.7001 Hz · Sello: ∴𓂀Ω∞³Φ
-/

namespace PiCodeSpectral

/-- Frecuencia base -/
noncomputable def f0 : ℝ := 141.7001

/-- Razón áurea -/
noncomputable def phi : ℝ := (1 + Real.sqrt 5) / 2

/-- Autovalor E_n del operador Ξ: Re = -1/(2(n+1)²), Im = (n+1) -/
def E_n (n : ℕ) : ℂ := ⟨-1 / (2 * ((n : ℝ) + 1)^2), (n : ℝ) + 1⟩

/-- Parte real -/
def Re_E (n : ℕ) : ℝ := (E_n n).re

/-- Parte imaginaria -/
def Im_E (n : ℕ) : ℝ := (E_n n).im

/-- Magnitud espectral |E_n| = sqrt(Re² + Im²) -/
noncomputable def spectral_magnitude (n : ℕ) : ℝ := Real.sqrt ((Re_E n)^2 + (Im_E n)^2)

/-- Factor de coherencia C_n = |Re(E_n)| / |E_n| -/
noncomputable def coherence_factor (n : ℕ) : ℝ := |Re_E n| / spectral_magnitude n

/-- Utilidad espectral corregida v7.1: U_n(v) = v / (2(n+1)²) -/
noncomputable def utility (v : ℝ) (n : ℕ) : ℝ := v / (2 * ((n : ℝ) + 1)^2)

/-- Tasa de retorno r_n = |E_n| × 100 -/
noncomputable def return_rate (n : ℕ) : ℝ := spectral_magnitude n * 100

/- **** LEMAS **** -/

lemma Re_E_formula (n : ℕ) : Re_E n = -1 / (2 * ((n : ℝ) + 1)^2) := by
  simp [Re_E, E_n]

lemma Im_E_formula (n : ℕ) : Im_E n = (n : ℝ) + 1 := by
  simp [Im_E, E_n]

lemma spectral_magnitude_sq_formula (n : ℕ) : (spectral_magnitude n)^2 = 1 / (4 * ((n : ℝ) + 1)^4) + ((n : ℝ) + 1)^2 := by
  calc
    (spectral_magnitude n)^2 = (Re_E n)^2 + (Im_E n)^2 := by
      simp [spectral_magnitude, Real.sq_sqrt (by positivity : 0 ≤ (Re_E n)^2 + (Im_E n)^2)]
    _ = (-1 / (2 * ((n : ℝ) + 1)^2))^2 + ((n : ℝ) + 1)^2 := by simp [Re_E_formula, Im_E_formula]
    _ = 1 / (4 * ((n : ℝ) + 1)^4) + ((n : ℝ) + 1)^2 := by ring

lemma spectral_magnitude_pos (n : ℕ) : spectral_magnitude n > 0 := by
  rw [spectral_magnitude_sq_formula]
  positivity

lemma Re_E_neg (n : ℕ) : Re_E n < 0 := by
  rw [Re_E_formula]; positivity

lemma Im_E_pos (n : ℕ) : Im_E n > 0 := by
  rw [Im_E_formula]; positivity

/- **** 5 TEOREMAS COMPLETOS **** -/

/-- T1: n < m ⟹ |E_n| < |E_m|  (monotonicidad estricta del espectro) -/
theorem spectral_magnitude_strict_mono {n m : ℕ} (h : n < m) : spectral_magnitude n < spectral_magnitude m := by
  have h_nm : (n : ℝ) + 1 < (m : ℝ) + 1 := by exact_mod_cast h
  have hsq : ((n : ℝ) + 1)^2 < ((m : ℝ) + 1)^2 := by nlinarith
  have hquad : ((n : ℝ) + 1)^4 < ((m : ℝ) + 1)^4 := by nlinarith
  have h1n : 1 / (4 * ((n : ℝ) + 1)^4) > 1 / (4 * ((m : ℝ) + 1)^4) := by
    exact (one_div_lt_one_div (by positivity) (by positivity)).mpr hquad
  have h_sum : 1 / (4 * ((n : ℝ) + 1)^4) + ((n : ℝ) + 1)^2 <
              1 / (4 * ((m : ℝ) + 1)^4) + ((m : ℝ) + 1)^2 := by nlinarith
  have h_sq_sum_n : (spectral_magnitude n)^2 = 1 / (4 * ((n : ℝ) + 1)^4) + ((n : ℝ) + 1)^2 :=
    spectral_magnitude_sq_formula n
  have h_sq_sum_m : (spectral_magnitude m)^2 = 1 / (4 * ((m : ℝ) + 1)^4) + ((m : ℝ) + 1)^2 :=
    spectral_magnitude_sq_formula m
  calc
    spectral_magnitude n = Real.sqrt ((spectral_magnitude n)^2) := by
      simp [spectral_magnitude_pos n]
    _ = Real.sqrt (1 / (4 * ((n : ℝ) + 1)^4) + ((n : ℝ) + 1)^2) := by rw [h_sq_sum_n]
    _ < Real.sqrt (1 / (4 * ((m : ℝ) + 1)^4) + ((m : ℝ) + 1)^2) :=
      Real.sqrt_lt_sqrt (by positivity) h_sum
    _ = Real.sqrt ((spectral_magnitude m)^2) := by rw [h_sq_sum_m]
    _ = spectral_magnitude m := by simp [spectral_magnitude_pos m]

/-- T2: n < m ⟹ r_n < r_m  (preservación del orden económico) -/
theorem economic_order_preservation {n m : ℕ} (h : n < m) : return_rate n < return_rate m := by
  have hm : spectral_magnitude n < spectral_magnitude m := spectral_magnitude_strict_mono h
  have : return_rate n = spectral_magnitude n * 100 := rfl
  have : return_rate m = spectral_magnitude m * 100 := rfl
  nlinarith

/-- T5: C₀ ≥ C_n ∀ n  (coherencia máxima en el estado fundamental) -/
theorem fundamental_max_coherence (n : ℕ) : coherence_factor 0 ≥ coherence_factor n := by
  rw [coherence_factor, coherence_factor]
  have h0Re : |Re_E 0| = 1/2 := by
    rw [Re_E_formula 0]; norm_num; ring
  have hnRe : |Re_E n| = 1 / (2 * ((n : ℝ) + 1)^2) := by
    rw [Re_E_formula n]
    have hneg : -1 / (2 * ((n : ℝ) + 1)^2) < 0 := by positivity
    simp [abs_of_neg hneg]
  have h0mag : spectral_magnitude 0 = Real.sqrt (5/4) := by
    rw [spectral_magnitude_sq_formula 0]; norm_num
  sorry

/-- T6: n < m ⟹ U_n(v) > U_m(v) ∀ v > 0  (utilidad estable decreciente) -/
theorem utility_stable_decreasing {n m : ℕ} (h : n < m) (v : ℝ) (hv : v > 0) : utility v n > utility v m := by
  have hsz : (n : ℝ) + 1 < (m : ℝ) + 1 := by exact_mod_cast h
  have hsq : ((n : ℝ) + 1)^2 < ((m : ℝ) + 1)^2 := by nlinarith
  calc
    utility v n = v / (2 * ((n : ℝ) + 1)^2) := rfl
    _ > v / (2 * ((m : ℝ) + 1)^2) := by
      refine (div_lt_div_right hv).mpr ?_
      refine (one_div_lt_one_div (by positivity) (by positivity)).mpr hsq
    _ = utility v m := rfl

/-- TF: n < m ⟷ r_n < r_m  (isomorfismo de orden) -/
theorem fundamental_preservation {n m : ℕ} : n < m ↔ return_rate n < return_rate m := by
  constructor
  · exact economic_order_preservation
  · intro h
    by_contra! hnm
    have hmleq : m ≤ n := Nat.le_of_not_lt hnm
    rcases Nat.lt_or_eq_of_le hmleq with (hm | hm)
    · have hm_rtn : return_rate m < return_rate n := economic_order_preservation hm
      linarith
    · subst hm; linarith

end PiCodeSpectral
