import ThresholdHC.StoppingProgram.FlowBounds

/-! Closure and normalization of the actual flow cone. These algebraic
facts support conic duality without assuming it. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap SignLaw)

theorem perspectiveCone_add {a b t u z w : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 ≤ t) (hu : 0 ≤ u)
    (hz : z^2 ≤ a*t) (hw : w^2 ≤ b*u) : (z+w)^2 ≤ (a+b)*(t+u) := by
  by_cases ha0 : a = 0
  · have hz0 : z = 0 := by rw [ha0,zero_mul] at hz; nlinarith [sq_nonneg z]
    rw [ha0,hz0,zero_add,zero_add]
    nlinarith [mul_nonneg hb ht]
  have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  by_cases hb0 : b = 0
  · have hw0 : w = 0 := by rw [hb0,zero_mul] at hw; nlinarith [sq_nonneg w]
    rw [hb0,hw0,add_zero,add_zero]
    nlinarith [mul_nonneg ha hu]
  have hb' : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have hzt : z^2/a ≤ t := (div_le_iff₀ ha').mpr (by simpa only [mul_comm] using hz)
  have hwu : w^2/b ≤ u := (div_le_iff₀ hb').mpr (by simpa only [mul_comm] using hw)
  have hsum := (quadratic_div_add_le (x := z) (z := w) ha' hb').trans (add_le_add hzt hwu)
  simpa only [mul_comm] using (div_le_iff₀ (add_pos ha' hb')).mp hsum

def addFlow {N : ℕ} (f g : Flow N) : Flow N :=
  ⟨fun s => f.stopWeight s+g.stopWeight s,fun s => f.continueWeight s+g.continueWeight s,
    fun s => f.outputWeight s+g.outputWeight s,fun s => f.momentWeight s+g.momentWeight s⟩

def scaleFlow {N : ℕ} (r : ℝ) (f : Flow N) : Flow N :=
  ⟨fun s => r*f.stopWeight s,fun s => r*f.continueWeight s,
    fun s => r*f.outputWeight s,fun s => r*f.momentWeight s⟩

theorem arrayAt_add_flow {N : ℕ} (u v : CountState N → ℝ) (n k : ℕ) :
    arrayAt (fun s => u s+v s) n k = arrayAt u n k+arrayAt v n k := by
  unfold arrayAt
  split_ifs <;> simp

theorem arrayAt_scale_flow {N : ℕ} (u : CountState N → ℝ) (r : ℝ) (n k : ℕ) :
    arrayAt (fun s => r*u s) n k = r*arrayAt u n k := by
  unfold arrayAt
  split_ifs <;> simp

theorem FlowCone.add {N : ℕ} {f g : Flow N} (hf : FlowCone f) (hg : FlowCone g) :
    FlowCone (addFlow f g) := by
  constructor
  · exact fun s => add_nonneg (hf.stop_nonneg s) (hg.stop_nonneg s)
  · exact fun s => add_nonneg (hf.continue_nonneg s) (hg.continue_nonneg s)
  · exact fun s => add_nonneg (hf.moment_nonneg s) (hg.moment_nonneg s)
  · simp only [addFlow,hf.root_stop,hg.root_stop,add_zero]
  · simp only [addFlow,hf.root_output,hg.root_output,add_zero]
  · simp only [addFlow,hf.root_moment,hg.root_moment,add_zero]
  · intro s hs
    simp only [addFlow,hf.terminal s hs,hg.terminal s hs,add_zero]
  · intro s hs
    have h1 := hf.recursion s hs
    have h2 := hg.recursion s hs
    simp only [addFlow,arrayAt_add_flow]
    linarith
  · intro s
    exact perspectiveCone_add (hf.stop_nonneg s) (hg.stop_nonneg s)
      (hf.moment_nonneg s) (hg.moment_nonneg s) (hf.perspective s) (hg.perspective s)

theorem FlowCone.scale {N : ℕ} {f : Flow N} (hf : FlowCone f) {r : ℝ} (hr : 0 ≤ r) :
    FlowCone (scaleFlow r f) := by
  constructor
  · exact fun s => mul_nonneg hr (hf.stop_nonneg s)
  · exact fun s => mul_nonneg hr (hf.continue_nonneg s)
  · exact fun s => mul_nonneg hr (hf.moment_nonneg s)
  · simp only [scaleFlow,hf.root_stop,mul_zero]
  · simp only [scaleFlow,hf.root_output,mul_zero]
  · simp only [scaleFlow,hf.root_moment,mul_zero]
  · intro s hs
    simp only [scaleFlow,hf.terminal s hs,mul_zero]
  · intro s hs
    simp only [scaleFlow,arrayAt_scale_flow]
    rw [← mul_add,hf.recursion s hs]
    ring
  · intro s
    have hh := mul_le_mul_of_nonneg_left (hf.perspective s) (sq_nonneg r)
    dsimp only [scaleFlow]
    nlinarith [hh]

theorem intensity_scale {N : ℕ} (r : ℝ) (f : Flow N) : intensity (scaleFlow r f) = r*intensity f := rfl

theorem countMean_scale {N : ℕ} (μ : Measure Gap) (q : SignLaw) (r : ℝ) (u : CountState N → ℝ) :
    countMean μ q (fun s => r*u s) = r*countMean μ q u := by
  simp only [countMean,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem flowInformation_scale {N : ℕ} (μ : Measure Gap) (Q : FourPriors)
    (f : Flow N) {r : ℝ} (hr : 0 ≤ r) :
    flowInformation μ Q (scaleFlow r f) = ENNReal.ofReal r*flowInformation μ Q f := by
  simp only [flowInformation,scaleFlow,ENNReal.ofReal_mul hr,Finset.mul_sum,mul_assoc]

theorem normalized_flow {N : ℕ} (f : Flow N) (hf : FlowCone f) (hi : 0 < intensity f) :
    FlowCone (scaleFlow (intensity f)⁻¹ f) ∧ intensity (scaleFlow (intensity f)⁻¹ f) = 1 := by
  exact ⟨hf.scale (inv_nonneg.mpr hi.le),by rw [intensity_scale,inv_mul_cancel₀ hi.ne']⟩

end ThresholdHC.StoppingProgram
