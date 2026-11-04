import ThresholdHC.Genie.ReferenceRegularization
import ThresholdHC.Genie.RevealReward
import ThresholdHC.Genie.FlowDepth
import ThresholdHC.StoppingProgram.FlowCostMoment

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace ThresholdHC.GenieRate
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram ThresholdHC.Genie
open ThresholdHC.CapIdentification

private theorem midpoint_perspective (a b v e : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (he : 0 < e) (hv : e*((a+b)/2) ≤ v) :
    perspective (b-a) v ≤ ENNReal.ofReal ((4/e)*((a+b)/2)) := by
  have hp : 0 ≤ (a+b)/2 := by positivity
  rw [perspective_le_finite_iff _ _ ((mul_nonneg he.le hp).trans hv) _ ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (mul_nonneg (by positivity) hp)]
  have hsq : (b-a)^2 ≤ (a+b)^2 := by nlinarith [mul_nonneg ha hb]
  calc (b-a)^2 ≤ (a+b)^2 := hsq
       _ = ((4/e)*((a+b)/2))*(e*((a+b)/2)) := by field_simp; ring
       _ ≤ _ := mul_le_mul_of_nonneg_left hv (mul_nonneg (by positivity) hp)

/-- Conditional terminal information is bounded by the midpoint probability
of that very word. The estimate includes zero reference masses. -/
theorem regularized_reveal_word (μ : Measure Gap) [IsProbabilityMeasure μ] (Q : FourPriors)
    (e : ℝ) (he : 0 ≤ e ∧ e ≤ 1) (hpos : 0 < e) (n k : ℕ) :
    revealReward μ (regularizedPriors Q e he) n k ≤
      ENNReal.ofReal (4/e)*ENNReal.ofReal (prefixCoefficient μ (midpointPrior Q.low Q.high) n k) := by
  let m := midpointPrior Q.low Q.high
  let v := (regularizedPriors Q e he).variance
  have heq (d : Gap) : m.val d = (Q.low.val d+Q.high.val d)/2 := by dsimp [m,midpointPrior,mixPrior]; ring
  have hv (d : Gap) : v.val d = e*m.val d+(1-e)*Q.variance.val d := rfl
  have hs (d : Gap) := midpoint_perspective (Q.low.val d) (Q.high.val d) (v.val d) e
    (Q.low.property.2 d).1 (Q.high.property.2 d).1 hpos (by rw [← heq,hv]; nlinarith [mul_nonneg (sub_nonneg.mpr he.2) (Q.variance.property.2 d).1])
  have ht (d : Gap) := midpoint_perspective (1-Q.high.val d) (1-Q.low.val d) (1-v.val d) e
    (sub_nonneg.mpr (Q.high.property.2 d).2) (sub_nonneg.mpr (Q.low.property.2 d).2) hpos (by
      rw [hv,heq]; nlinarith [mul_nonneg (sub_nonneg.mpr he.2) (sub_nonneg.mpr (Q.variance.property.2 d).2)])
  have hn : 0 ≤ 4/e := by positivity
  have hC : ENNReal.ofReal (prefixCoefficient μ m n k) =
      ∫⁻ d, ENNReal.ofReal (prefixDensity m n k d) ∂μ :=
    ofReal_integral_eq_lintegral_ofReal (prefixDensity_integrable μ m n k) (ae_of_all _ (prefixDensity_nonneg m n k))
  rw [← show m = midpointPrior Q.low Q.high from rfl,hC,← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro d
  have h₁ : perspective (Q.high.val d-Q.low.val d) (v.val d) ≤ ENNReal.ofReal ((4/e)*m.val d) := by
    simpa only [heq] using hs d
  have h₀ : perspective (Q.high.val d-Q.low.val d) (1-v.val d) ≤ ENNReal.ofReal ((4/e)*(1-m.val d)) := by
    rw [heq]
    convert ht d using 2 <;> ring
  refine (add_le_add (mul_le_mul_right h₁ _) (mul_le_mul_right h₀ _)).trans_eq ?_
  change _ = ENNReal.ofReal (4/e)*ENNReal.ofReal (prefixDensity m n k d)
  rw [← ENNReal.ofReal_mul (prefixLikelihood_nonneg true n k d),
    ← ENNReal.ofReal_mul (prefixLikelihood_nonneg false n k d),
    ← ENNReal.ofReal_add (mul_nonneg (prefixLikelihood_nonneg _ _ _ _) (mul_nonneg hn (m.property.2 d).1))
      (mul_nonneg (prefixLikelihood_nonneg _ _ _ _) (mul_nonneg hn (sub_nonneg.mpr (m.property.2 d).2))),
    ← ENNReal.ofReal_mul hn]
  congr 1
  unfold prefixDensity
  ring

/-- Probability of a depth-N stop costs N observations under the same prior. -/
theorem terminal_mass_work {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (f : Flow N) (hf : FlowCone f) :
    (N:ℝ)*rawLayer f.stopWeight (prefixCoefficient μ q) N ≤ countMean μ q f.continueWeight := by
  rw [← stopping_depth_countMean μ q f hf,← rawLayer_mul_depth]
  apply Finset.single_le_sum _ (Finset.mem_range.mpr (Nat.lt_succ_self N))
  intro n _
  exact Finset.sum_nonneg fun k _ => mul_nonneg (Genie.rawArray_nonneg _ hf.stop_nonneg _ _)
    (mul_nonneg (Nat.cast_nonneg _) (prefixCoefficient_nonneg μ q _ _))

end ThresholdHC.GenieRate
