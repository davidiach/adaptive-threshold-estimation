import ThresholdHC.EntropyTailAssembly.MixedWork

/-! The terminal unresolved population has small mass. Its capped work is
summable even though no inverse moment of that component is assumed. -/

noncomputable section
open MeasureTheory Set Real
open scoped BigOperators

namespace ThresholdHC.EntropyTailAssembly
open ThresholdHC.Tier6

theorem quarter_geometric_sum (n : ℕ) : ∑ l ∈ Finset.range n, (1/4:ℝ)^l ≤ 4/3 := by
  have h := hasSum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/4) (by norm_num : (1/4:ℝ) < 1)
  have hb := sum_le_hasSum (Finset.range n) (fun _ _ => by positivity) h
  norm_num at hb ⊢
  exact hb

theorem quarter_linear_term (n : ℕ) : (n+1:ℝ)*(1/4:ℝ)^(n+1) ≤ 1/4 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ]
    push_cast
    nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/4) (n+1)]

theorem sqrt_accuracy_ratio {ρ : ℝ} (hρ : 0 ≤ ρ) {l J : ℕ} (hl : l ≤ J) :
    sqrt (levelAccuracy ρ J) = sqrt (levelAccuracy ρ l)*(1/4:ℝ)^(J-l) := by
  rw [sqrt_levelAccuracy hρ, sqrt_levelAccuracy hρ, mul_assoc, ← pow_add]
  congr 2
  omega

theorem terminal_sqrt_ratio {ρ z : ℝ} (hρ : 0 < ρ) (_hz : 0 ≤ z)
    {J l : ℕ} (hzJ : z ≤ levelAccuracy ρ J/8) (hl : l ≤ J) :
    sqrt z / sqrt (levelAccuracy ρ l) ≤ (3/8:ℝ)*(1/4:ℝ)^(J-l) := by
  have hδ := levelAccuracy_pos hρ J
  have hs : sqrt z ≤ (3/8:ℝ)*sqrt (levelAccuracy ρ J) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    nlinarith [sq_sqrt hδ.le]
  rw [sqrt_accuracy_ratio hρ.le hl] at hs
  apply (div_le_iff₀ (sqrt_pos_of_pos (levelAccuracy_pos hρ l))).mpr
  nlinarith only [hs]

theorem terminal_ratio_sum {ρ z : ℝ} (hρ : 0 < ρ) (hz : 0 ≤ z)
    (J : ℕ) (hzJ : z ≤ levelAccuracy ρ J/8) :
    (∑ l ∈ Finset.range (J+1), sqrt z / sqrt (levelAccuracy ρ l)) ≤ 1/2 := by
  have h := Finset.sum_le_sum (s := Finset.range (J+1))
    (fun l hl => terminal_sqrt_ratio hρ hz hzJ (show l ≤ J by simpa using hl))
  rw [← Finset.mul_sum] at h
  have he : (∑ l ∈ Finset.range (J+1), (1/4:ℝ)^(J-l)) =
      ∑ l ∈ Finset.range (J+1), (1/4:ℝ)^l := by
    simpa using Finset.sum_range_reflect (fun l => (1/4:ℝ)^l) (J+1)
  rw [he] at h
  linarith [quarter_geometric_sum (J+1)]

theorem terminal_selected_work {ρ z A : ℝ} (hρ : 0 < ρ) (_hz : 0 ≤ z) (hA : 0 ≤ A)
    (J : ℕ) (hzJ : z ≤ levelAccuracy ρ J/8) :
    16*(J+1)*sqrt (z*A) ≤ 2*sqrt (ρ*A) := by
  have hδ := levelAccuracy_pos hρ J
  have hs : sqrt (z*A) ≤ sqrt (levelAccuracy ρ J)*sqrt A/2 := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have hm := mul_le_mul_of_nonneg_right hzJ hA
    have he : (sqrt (levelAccuracy ρ J)*sqrt A/2)^2 = levelAccuracy ρ J*A/4 := by
      rw [div_pow, mul_pow, sq_sqrt hδ.le, sq_sqrt hA]
      norm_num
    rw [he]
    nlinarith [mul_nonneg hδ.le hA]
  have he : sqrt (levelAccuracy ρ J)*sqrt A = sqrt (ρ*A)*(1/4:ℝ)^(J+1) := by
    rw [sqrt_levelAccuracy hρ.le, sqrt_mul hρ.le]
    ring
  rw [he] at hs
  have h1 := mul_le_mul_of_nonneg_left hs (show (0:ℝ) ≤ 16*(J+1) by positivity)
  have h2 := mul_le_mul_of_nonneg_left (quarter_linear_term J) (show 0 ≤ 8*sqrt (ρ*A) by positivity)
  nlinarith only [h1, h2]

theorem unresolved_level_envelope (σ τ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ]
    (hσ : Integrable (fun d : Gap => (d:ℝ)⁻¹^2) σ)
    (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ) {ρ z : ℝ}
    (hρ : 0 < ρ) (hz : 0 ≤ z) (hm : ρ/128 < (σ+τ).real univ) (l : ℕ) :
    let k := errorCapExponent (σ+τ) (levelAccuracy ρ l) (levelAccuracy_pos hρ l)
    sqrt (z*levelAccuracy ρ l*4^k) ≤
      16*sqrt (z*(∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ)) +
      256*(∫ d : Gap, (d:ℝ)⁻¹ ∂τ)*(sqrt z/sqrt (levelAccuracy ρ l)) := by
  dsimp only
  let δ := levelAccuracy ρ l
  let k := errorCapExponent (σ+τ) δ (levelAccuracy_pos hρ l)
  let A := ∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ
  let H := ∫ d : Gap, (d:ℝ)⁻¹ ∂τ
  have hδ : 0 < δ := levelAccuracy_pos hρ l
  have hM : (0:ℝ) < 4^k := by positivity
  have hA : 0 ≤ A := integral_nonneg (fun _ => sq_nonneg _)
  have hH : 0 ≤ H := integral_nonneg (fun d => inv_nonneg.mpr d.property.1.le)
  have hmass : δ/8 < (σ+τ).real univ := by
    have h := levelAccuracy_le_first hρ.le l
    dsimp [δ]
    linarith
  have he := errorCapExponent_error_lower (σ+τ) hδ hmass
  change sqrt (z*δ*4^k) ≤ 16*sqrt (z*A)+256*H*(sqrt z/sqrt δ)
  rcases cap_dichotomy σ τ hσ hM he with ht | hs
  · have hi := eta_le_inverse τ hτ hM
    have hc : δ ≤ 256*H/sqrt ((4:ℝ)^k) := by
      exact ht.trans ((mul_le_mul_of_nonneg_left hi (by norm_num : (0:ℝ) ≤ 256)).trans_eq (by ring))
    have hmul := (le_div_iff₀ (sqrt_pos_of_pos hM)).mp hc
    have hc' : sqrt ((4:ℝ)^k) ≤ 256*H/δ := (le_div_iff₀ hδ).mpr (by nlinarith only [hmul])
    have hb := mul_le_mul_of_nonneg_left hc' (show 0 ≤ sqrt z*sqrt δ by positivity)
    have he1 : sqrt z*sqrt δ*sqrt ((4:ℝ)^k) = sqrt (z*δ*4^k) := by
      rw [sqrt_mul (mul_nonneg hz hδ.le), sqrt_mul hz]
    have he2 : sqrt z*sqrt δ*(256*H/δ) = 256*H*(sqrt z/sqrt δ) := by
      have hsδ := sq_sqrt hδ.le
      have hn := (sqrt_pos_of_pos hδ).ne'
      field_simp
      rw [hsδ]
      ring
    rw [he1, he2] at hb
    exact hb.trans (le_add_of_nonneg_left (by positivity))
  · have hb : sqrt (z*δ*4^k) ≤ 16*sqrt (z*A) := by
      apply sqrt_le_iff.mpr
      refine ⟨by positivity, ?_⟩
      have hh := mul_le_mul_of_nonneg_left hs hz
      nlinarith [sq_sqrt (mul_nonneg hz hA)]
    exact hb.trans (le_add_of_nonneg_right (by positivity))

theorem unresolved_work_sum (σ τ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ]
    (hσ : Integrable (fun d : Gap => (d:ℝ)⁻¹^2) σ)
    (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ) {ρ z : ℝ}
    (hρ : 0 < ρ) (hz : 0 ≤ z) (hm : ρ/128 < (σ+τ).real univ)
    (J : ℕ) (hzJ : z ≤ levelAccuracy ρ J/8) :
    (∑ l ∈ Finset.range (J+1), sqrt (z*levelAccuracy ρ l*
      4^(errorCapExponent (σ+τ) (levelAccuracy ρ l) (levelAccuracy_pos hρ l)))) ≤
      2*sqrt (ρ*(∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ))+128*(∫ d : Gap, (d:ℝ)⁻¹ ∂τ) := by
  have hA : 0 ≤ ∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ := integral_nonneg (fun _ => sq_nonneg _)
  have hH : 0 ≤ ∫ d : Gap, (d:ℝ)⁻¹ ∂τ := integral_nonneg (fun d => inv_nonneg.mpr d.property.1.le)
  have h := Finset.sum_le_sum (s := Finset.range (J+1))
    (fun l _ => unresolved_level_envelope σ τ hσ hτ hρ hz hm l)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum] at h
  have h1 := terminal_selected_work hρ hz hA J hzJ
  have h2 := mul_le_mul_of_nonneg_left (terminal_ratio_sum hρ hz J hzJ)
    (show 0 ≤ 256*(∫ d : Gap, (d:ℝ)⁻¹ ∂τ) by positivity)
  push_cast at h
  nlinarith only [h, h1, h2]

end ThresholdHC.EntropyTailAssembly
