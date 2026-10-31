import ThresholdHC.StoppingProgram.PriceMultipliers
import ThresholdHC.StoppingProgram.OutputChoices

/-! Exact output elimination forces a finite information/work ratio under
every positive feasible conic price, including null-reference states. -/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators

namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap)

theorem conePrice_null_contrast {N : ℕ} (μ : Measure Gap) (Q : FourPriors) {α η : ℝ}
    (hα : 0 < α) (hprice : ∀ f : Flow N, FlowCone f → 0 ≤ conePrice μ Q α η f)
    (f : Flow N) (hf : FlowCone f) (s : CountState N) (ha : 0 < f.stopWeight s)
    (hv : countCoefficient μ Q.variance s = 0) :
    countCoefficient μ Q.high s-countCoefficient μ Q.low s = 0 := by
  by_contra hd
  let d := countCoefficient μ Q.high s-countCoefficient μ Q.low s
  let W := countMean μ Q.work f.continueWeight
  let z := (η*W+1)/(α*d)
  have hc := hprice (singleOutput f s z) (singleOutput_cone f hf s ha z)
  change 0 ≤ countMean μ Q.variance (Pi.single s (z^2/f.stopWeight s))-
    α*(countMean μ Q.high (Pi.single s z)-countMean μ Q.low (Pi.single s z))+η*W at hc
  rw [countMean_single,countMean_single,countMean_single,hv,zero_mul,← sub_mul] at hc
  change 0 ≤ 0-α*(d*z)+η*W at hc
  have he : α*(d*z) = η*W+1 := by
    dsimp [z]
    have had : α*d ≠ 0 := mul_ne_zero hα.ne' hd
    calc
      α*(d*((η*W+1)/(α*d))) = ((η*W+1)/(α*d))*(α*d) := by ring
      _ = η*W+1 := div_mul_cancel₀ _ had
  rw [he] at hc
  linarith

theorem conePrice_information_finite {N : ℕ} (μ : Measure Gap) (Q : FourPriors) {α η : ℝ}
    (hα : 0 < α) (hprice : ∀ f : Flow N, FlowCone f → 0 ≤ conePrice μ Q α η f)
    (f : Flow N) (hf : FlowCone f) : flowInformation μ Q f ≠ ⊤ := by
  apply ENNReal.sum_ne_top.mpr
  intro s hs
  by_cases ha : f.stopWeight s = 0
  · simp [ha]
  have ha' : 0 < f.stopWeight s := lt_of_le_of_ne (hf.stop_nonneg s) (Ne.symm ha)
  apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
  apply ne_of_lt
  apply (perspective_finite_iff (countCoefficient_nonneg μ Q.variance s)).mpr
  by_cases hv : countCoefficient μ Q.variance s = 0
  · exact Or.inr (conePrice_null_contrast μ Q hα hprice f hf s ha' hv)
  · exact Or.inl (lt_of_le_of_ne (countCoefficient_nonneg μ Q.variance s) (Ne.symm hv))

theorem conePrice_information_bound {N : ℕ} (μ : Measure Gap) (Q : FourPriors) {α η : ℝ}
    (hα : 0 < α) (hprice : ∀ f : Flow N, FlowCone f → 0 ≤ conePrice μ Q α η f)
    (f : Flow N) (hf : FlowCone f) :
    α^2*(flowInformation μ Q f).toReal ≤ 4*η*countMean μ Q.work f.continueWeight := by
  have hI := conePrice_information_finite μ Q hα hprice f hf
  have hh := hprice (optimizedOutput μ Q α f) (optimizedOutput_cone μ Q α f hf)
  unfold conePrice at hh
  rw [optimizedOutput_lagrange μ Q α f hf hI] at hh
  change 0 ≤ -(α^2/4)*(flowInformation μ Q f).toReal+η*countMean μ Q.work f.continueWeight at hh
  nlinarith

theorem conePrice_ratio_bound {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (Q : FourPriors) {α η : ℝ} (hα : 0 < α) (hη : 0 ≤ η)
    (hprice : ∀ f : Flow N, FlowCone f → 0 ≤ conePrice μ Q α η f) :
    informationRatio μ N Q ≤ ENNReal.ofReal (4*η/α^2) := by
  apply iSup_le
  intro f
  apply iSup_le
  intro hf
  apply iSup_le
  intro hi
  have hw : 0 < countMean μ Q.work f.continueWeight := by
    have hh := flow_work_ge_intensity μ Q.work f hf
    rw [hi] at hh
    linarith
  have hI := conePrice_information_finite μ Q hα hprice f hf
  apply (ENNReal.div_le_iff (ENNReal.ofReal_ne_zero_iff.mpr hw) ENNReal.ofReal_ne_top).mpr
  rw [← ENNReal.ofReal_toReal hI,← ENNReal.ofReal_mul (by positivity : 0 ≤ 4*η/α^2)]
  apply ENNReal.ofReal_le_ofReal
  calc
    (flowInformation μ Q f).toReal ≤ (4*η*countMean μ Q.work f.continueWeight)/α^2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hα)).mpr
      nlinarith [conePrice_information_bound μ Q hα hprice f hf]
    _ = (4*η/α^2)*countMean μ Q.work f.continueWeight := by ring

theorem conePrice_ratio_finite {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (Q : FourPriors) {α η : ℝ} (hα : 0 < α) (hη : 0 ≤ η)
    (hprice : ∀ f : Flow N, FlowCone f → 0 ≤ conePrice μ Q α η f) :
    informationRatio μ N Q ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (conePrice_ratio_bound μ Q hα hη hprice)

theorem conePrice_ratio_real_bound {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (Q : FourPriors) {α η : ℝ} (hα : 0 < α) (hη : 0 ≤ η)
    (hprice : ∀ f : Flow N, FlowCone f → 0 ≤ conePrice μ Q α η f) :
    α^2*(informationRatio μ N Q).toReal ≤ 4*η := by
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (conePrice_ratio_bound μ Q hα hη hprice)
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ 4*η/α^2)] at hh
  have ht := (le_div_iff₀ (sq_pos_of_pos hα)).mp hh
  nlinarith

end ThresholdHC.StoppingProgram
