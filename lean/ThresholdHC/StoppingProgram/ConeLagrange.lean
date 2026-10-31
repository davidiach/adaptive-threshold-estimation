import ThresholdHC.StoppingProgram.InformationBound

/-! The flow-cone Lagrangian inequality, with zero stopping weights and
null variance references handled explicitly before taking real parts. -/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators

namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap)

theorem perspective_cone_lower_toReal {a t z v d α : ℝ}
    (ha : 0 ≤ a) (ht : 0 ≤ t) (hv : 0 ≤ v) (hcone : z^2 ≤ a*t)
    (hfinite : ENNReal.ofReal a*perspective d v ≠ ⊤) :
    -(α^2/4)*(ENNReal.ofReal a*perspective d v).toReal ≤ v*t-α*d*z := by
  by_cases ha0 : a = 0
  · have hz : z = 0 := by rw [ha0,zero_mul] at hcone; nlinarith [sq_nonneg z]
    simp only [ha0,hz,ENNReal.ofReal_zero,zero_mul,ENNReal.toReal_zero,mul_zero,sub_zero]
    exact mul_nonneg hv ht
  have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  by_cases hv0 : v = 0
  · have hd : d = 0 := by
      by_contra hd
      have he : ENNReal.ofReal a*perspective d v = ⊤ := by
        rw [hv0,perspective_nonzero_zero hd,
          ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr ha')]
      exact hfinite he
    simp only [hv0,hd,perspective_zero_zero,mul_zero,ENNReal.toReal_zero,zero_mul,sub_zero,le_refl]
  have hv' : 0 < v := lt_of_le_of_ne hv (Ne.symm hv0)
  rw [perspective_pos hv',ENNReal.toReal_mul,ENNReal.toReal_ofReal ha,
    ENNReal.toReal_ofReal (div_nonneg (sq_nonneg d) hv)]
  have he : -(α^2/4)*(a*(d^2/v)) = -(α^2*a*d^2/(4*v)) := by
    field_simp
  rw [he]
  exact perspective_cone_lower ha ht hv' hcone

theorem flow_cone_lagrange {N : ℕ} (μ : Measure Gap) (Q : FourPriors)
    (f : Flow N) (hf : FlowCone f) (hI : flowInformation μ Q f ≠ ⊤) (α : ℝ) :
    -(α^2/4)*(flowInformation μ Q f).toReal ≤
      countMean μ Q.variance f.momentWeight-
        α*(countMean μ Q.high f.outputWeight-countMean μ Q.low f.outputWeight) := by
  let T : CountState N → ℝ≥0∞ := fun s => ENNReal.ofReal (f.stopWeight s)*perspective
    (countCoefficient μ Q.high s-countCoefficient μ Q.low s) (countCoefficient μ Q.variance s)
  have hT (s : CountState N) : T s ≠ ⊤ := ne_top_of_le_ne_top hI
    (Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ s))
  have hi : (flowInformation μ Q f).toReal = ∑ s, (T s).toReal := ENNReal.toReal_sum (fun s _ => hT s)
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun s _ =>
    perspective_cone_lower_toReal (α := α) (d := countCoefficient μ Q.high s-countCoefficient μ Q.low s)
      (hf.stop_nonneg s) (hf.moment_nonneg s) (countCoefficient_nonneg μ Q.variance s)
      (hf.perspective s) (hT s))
  change (∑ s, -(α^2/4)*(T s).toReal) ≤ _ at hh
  rw [← Finset.mul_sum,← hi] at hh
  convert hh using 1
  simp only [countMean,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _
  ring

end ThresholdHC.StoppingProgram
