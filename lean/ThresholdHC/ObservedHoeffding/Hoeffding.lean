import ThresholdHC.ObservedState.Targets
import Mathlib.Probability.Moments.SubGaussian

/-! Weighted Hoeffding for the sign target `target w` under the product sign prior
`signLaw q`, and the replication tail of the proof of `prop:outer`
(`paper/v6/core.tex`). -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace ThresholdHC.ObservedHoeffding
open ThresholdHC.ObservedState

/-- A sub-Gaussian parameter can be raised. -/
theorem subgaussian_mono {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}
    {c c' : ℝ≥0} (h : HasSubgaussianMGF X c μ) (hc : c ≤ c') : HasSubgaussianMGF X c' μ where
  integrable_exp_mul := h.integrable_exp_mul
  mgf_le t := by
    refine (h.mgf_le t).trans (Real.exp_le_exp.mpr ?_)
    have hc' : (c : ℝ) ≤ c' := hc
    gcongr

/-- The centered contribution of one cell to the sign target. -/
def centeredCell {I : Type} (q : I → unitInterval) (w : I → ℝ) (i : I) (s : I → Bool) : ℝ :=
  w i * (if s i then (1 : ℝ) else 0) - w i * (q i : ℝ)

/-- One cell of nonnegative length `w i` has sub-Gaussian parameter `(w i / 2)²`. -/
theorem coordinate_subgaussian {I : Type} [Fintype I] (q : I → unitInterval) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (i : I) :
    HasSubgaussianMGF (centeredCell q w i) ((‖w i - 0‖₊ / 2) ^ 2) (signLaw q) := by
  have hb := hasSubgaussianMGF_of_mem_Icc (μ := bernoulliMeasure true false (q i))
    (X := fun b : Bool => w i * (if b then (1 : ℝ) else 0)) (a := 0) (b := w i)
    (measurable_of_countable _).aemeasurable
    (ae_of_all _ (fun b => by cases b <;> simp [hw i]))
  rw [integral_bernoulliMeasure] at hb
  have hmap : (signLaw q).map (fun s : I → Bool => s i) = bernoulliMeasure true false (q i) :=
    (measurePreserving_eval (fun i => bernoulliMeasure true false (q i)) i).map_eq
  rw [← hmap] at hb
  have h := HasSubgaussianMGF.of_map (μ := signLaw q) (Y := fun s : I → Bool => s i)
    (measurable_pi_apply i).aemeasurable hb
  refine h.congr (ae_of_all _ (fun s => ?_))
  simp [centeredCell, Function.comp, mul_comm]

/-- The centered cells are independent under the product sign prior. -/
theorem centeredCell_indep {I : Type} [Fintype I] (q : I → unitInterval) (w : I → ℝ) :
    iIndepFun (fun i => centeredCell q w i) (signLaw q) := by
  unfold signLaw
  exact iIndepFun_pi (X := fun i (b : Bool) => w i * (if b then (1 : ℝ) else 0) - w i * (q i : ℝ))
    (fun i => (measurable_of_countable _).aemeasurable)

theorem centeredCell_sum {I : Type} [Fintype I] (q : I → unitInterval) (w : I → ℝ)
    (s : I → Bool) :
    (∑ i, centeredCell q w i s) = target w s - ∑ i, w i * (q i : ℝ) := by
  simp only [centeredCell, Finset.sum_sub_distrib, target]

/-- The centered sign target is sub-Gaussian with any parameter `c ≥ ∑ w² / 4`. -/
theorem target_subgaussian {I : Type} [Fintype I] (q : I → unitInterval) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (c : ℝ≥0) (hs : (∑ i, (w i) ^ 2) / 4 ≤ c) :
    HasSubgaussianMGF (fun s => target w s - ∑ i, w i * (q i : ℝ)) c (signLaw q) := by
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun (centeredCell_indep q w)
    (s := Finset.univ) (fun i _ => coordinate_subgaussian q w hw i)
  have hle : (∑ i ∈ Finset.univ, (‖w i - 0‖₊ / 2) ^ 2) ≤ c := by
    rw [← NNReal.coe_le_coe]
    push_cast
    calc
      _ = (∑ i, (w i) ^ 2) / 4 := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        rw [sub_zero, Real.norm_of_nonneg (hw i)]
        ring
      _ ≤ c := hs
  refine (subgaussian_mono hsum hle).congr (ae_of_all _ (fun s => ?_))
  exact centeredCell_sum q w s

/-- Weighted Hoeffding for the sign target, two-sided with the strict event:
`∑ w² ≤ v` gives the tail `2 exp(-2r²/v)` at radius `r`. -/
theorem weighted_hoeffding {I : Type} [Fintype I] (q : I → unitInterval) (w : I → ℝ)
    {v r : ℝ} (hw : ∀ i, 0 ≤ w i) (hv : 0 < v) (hs : (∑ i, (w i) ^ 2) ≤ v) (hr : 0 ≤ r) :
    signLaw q {s | r < |target w s - ∑ i, w i * (q i : ℝ)|} ≤
      ENNReal.ofReal (2 * Real.exp (-2 * r ^ 2 / v)) := by
  have hc : ((Real.toNNReal (v / 4) : ℝ≥0) : ℝ) = v / 4 := Real.coe_toNNReal _ (by positivity)
  have hX := target_subgaussian q w hw (Real.toNNReal (v / 4)) (by rw [hc]; linarith)
  have hu := hX.measure_ge_le hr
  have hl := hX.neg.measure_ge_le hr
  have hexp : -r ^ 2 / (2 * ((Real.toNNReal (v / 4) : ℝ≥0) : ℝ)) = -2 * r ^ 2 / v := by
    rw [hc]
    field_simp
    ring
  rw [hexp] at hu hl
  have hsub : {s | r < |target w s - ∑ i, w i * (q i : ℝ)|} ⊆
      {s | r ≤ target w s - ∑ i, w i * (q i : ℝ)} ∪
        {s | r ≤ (-(fun s => target w s - ∑ i, w i * (q i : ℝ))) s} := by
    intro s hs
    have hs' : r < |target w s - ∑ i, w i * (q i : ℝ)| := hs
    rcases lt_abs.mp hs' with h | h
    · exact Or.inl h.le
    · exact Or.inr h.le
  have hreal : (signLaw q).real {s | r < |target w s - ∑ i, w i * (q i : ℝ)|} ≤
      2 * Real.exp (-2 * r ^ 2 / v) := by
    calc
      _ ≤ _ := measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ _ := measureReal_union_le _ _
      _ ≤ _ := by linarith
  exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)).mpr hreal

/-- The count `M ≥ 32 Δ⁻² log(2/δ)` makes the replication tail at most `δ`. -/
theorem replication_exp_le {M Δ δ : ℝ} (hΔ : 0 < Δ) (hδ : 0 < δ)
    (hcount : 32 * Real.log (2 / δ) / Δ ^ 2 ≤ M) :
    2 * Real.exp (-M * Δ ^ 2 / 32) ≤ δ := by
  have hlog : Real.log (2 / δ) ≤ M * Δ ^ 2 / 32 := by
    have h := (div_le_iff₀ (by positivity : (0 : ℝ) < Δ ^ 2)).mp hcount
    linarith
  have hexp : Real.exp (-M * Δ ^ 2 / 32) ≤ Real.exp (-Real.log (2 / δ)) :=
    Real.exp_le_exp.mpr (by linarith)
  rw [Real.exp_neg, Real.exp_log (by positivity), inv_div] at hexp
  linarith

/-- The display in the proof of `prop:outer`. -/
theorem replication_tail {I : Type} [Fintype I] (q : I → unitInterval) (w : I → ℝ) (M : ℕ)
    {Δ δ : ℝ} (hw : ∀ i, 0 ≤ w i) (hM : 0 < M) (hs : (∑ i, (w i) ^ 2) ≤ 1 / (M : ℝ))
    (hΔ : 0 < Δ) (hδ : 0 < δ) (hcount : 32 * Real.log (2 / δ) / Δ ^ 2 ≤ (M : ℝ)) :
    signLaw q {s | Δ / 8 < |target w s - ∑ i, w i * (q i : ℝ)|} ≤
        ENNReal.ofReal (2 * Real.exp (-(M : ℝ) * Δ ^ 2 / 32)) ∧
      2 * Real.exp (-(M : ℝ) * Δ ^ 2 / 32) ≤ δ := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  refine ⟨?_, replication_exp_le hΔ hδ hcount⟩
  have h := weighted_hoeffding q w hw (by positivity : (0 : ℝ) < 1 / (M : ℝ)) hs
    (by positivity : 0 ≤ Δ / 8)
  have he : -2 * (Δ / 8) ^ 2 / (1 / (M : ℝ)) = -(M : ℝ) * Δ ^ 2 / 32 := by
    field_simp
    ring
  rwa [he] at h

end ThresholdHC.ObservedHoeffding
