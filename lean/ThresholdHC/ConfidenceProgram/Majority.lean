import ThresholdHC.Confidence.Amplification
import Mathlib.Probability.Independence.Integration

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ThresholdHC.ConfidenceProgram
open ThresholdHC.Confidence

/-- The exponential-moment majority bound for independent coordinates with
failure probability at most one quarter. The output distributions may differ. -/
theorem quarter_majority {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : ℕ) (f : MedianIndex m → Ω → ℝ) (hm : ∀ i, Measurable (f i)) (hi : iIndepFun f P) (θ r : ℝ)
    (hf : ∀ i, P {u | r < |f i u-θ|} ≤ 1/4) :
    P {u | r < |median m (fun i => f i u)-θ|} ≤ ENNReal.ofReal ((3/4:ℝ)^m/2) := by
  classical
  let bad : Set ℝ := {y | r < |y-θ|}
  have hb : MeasurableSet bad := measurableSet_lt measurable_const ((measurable_id.sub_const θ).abs)
  let g (y : ℝ) : ℝ≥0∞ := 1+bad.indicator (fun _ => 2) y
  have hg : Measurable g := (measurable_const (a := (1:ℝ≥0∞))).add ((measurable_const (a := (2:ℝ≥0∞))).indicator hb)
  let X (i : MedianIndex m) (u : Ω) := g (f i u)
  have hX (i) : Measurable (X i) := hg.comp (hm i)
  have hind : iIndepFun X P := hi.comp (fun _ => g) (fun _ => hg)
  have hex (i) : (∫⁻ u, X i u ∂P) ≤ ENNReal.ofReal (3/2:ℝ) := by
    have he : X i = fun u => 1+(f i ⁻¹' bad).indicator (fun _ => (2:ℝ≥0∞)) u := by
      funext u; by_cases h : f i u ∈ bad <;> simp [X,g,h]
    rw [he,lintegral_add_left measurable_const,lintegral_const,measure_univ,mul_one,
      lintegral_indicator (hm i hb),lintegral_const,Measure.restrict_apply_univ]
    have h : (1:ℝ≥0∞)+2*P (f i ⁻¹' bad) ≤ 1+2*(1/4) :=
      add_le_add le_rfl (mul_le_mul_right (hf i) (2:ℝ≥0∞))
    refine h.trans_eq ?_
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_add (by finiteness) (by finiteness),ENNReal.toReal_mul]
    norm_num
  let F (u : Ω) := ∏ i, X i u
  have hF : Measurable F := Finset.measurable_prod _ (fun i _ => hX i)
  have hE : ∫⁻ u, F u ∂P ≤ ENNReal.ofReal ((3/2:ℝ)^(2*m+1)) := by
    rw [show (∫⁻ u, F u ∂P) = ∏ i, (∫⁻ u, X i u ∂P) from
      lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ X hind hX]
    refine (Finset.prod_le_prod (fun i _ => hex i)).trans_eq ?_
    simp [ENNReal.ofReal_pow (by norm_num : 0 ≤ (3/2:ℝ)),MedianIndex]
  let y : ℝ≥0∞ := 3^(m+1)
  have hsub : {u | r < |median m (fun i => f i u)-θ|} ⊆ {u | y ≤ F u} := by
    intro u hu
    obtain ⟨s,hs⟩ := median_bad_subset m (fun i => f i u) θ r hu
    have he (i) (h : i ∈ s.val) : X i u = 3 := by
      have h' : f i u ∈ bad := hs i h
      simp [X,g,h']
      norm_num
    have hge (i) : 1 ≤ X i u := le_self_add
    calc y = ∏ i ∈ s.val, X i u := by simp only [Finset.prod_congr rfl he,Finset.prod_const,s.property,y]
         _ ≤ _ := Finset.prod_le_prod_of_subset_of_one_le (Finset.subset_univ _) (fun i _ _ => hge i)
  have hmkv := meas_ge_le_lintegral_div (μ := P) hF.aemeasurable (by dsimp [y]; positivity : y ≠ 0) (by dsimp [y]; finiteness : y ≠ ⊤)
  refine (measure_mono hsub).trans (hmkv.trans ((ENNReal.div_le_div_right hE y).trans_eq ?_))
  change ENNReal.ofReal ((3/2:ℝ)^(2*m+1))/(3:ℝ≥0∞)^(m+1) = _
  rw [← show ENNReal.ofReal ((3:ℝ)^(m+1)) = (3:ℝ≥0∞)^(m+1) by rw [ENNReal.ofReal_pow (by norm_num : 0 ≤ (3:ℝ))]; norm_num,
    ← ENNReal.ofReal_div_of_pos (by positivity)]
  congr 1
  rw [pow_succ,pow_succ,pow_mul]
  have he : ((3/2:ℝ)^2)^m = (3/4:ℝ)^m*3^m := by rw [← mul_pow]; norm_num
  rw [he]
  field_simp

end ThresholdHC.ConfidenceProgram
