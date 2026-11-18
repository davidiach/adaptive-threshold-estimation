import ThresholdHC.LargeBudgetRMS.LargeBudgetBinomial
import ThresholdHC.LargeBudgetRMS.LargeBudgetTable

/-! A 25-flip witness in the ordinary population model. -/
noncomputable section
namespace ThresholdHC.SharpRMS.LargeBudget
open MeasureTheory Tier3 Tier5 Tier6
open scoped ENNReal

def fifthGap : Gap := ⟨1/5,by norm_num⟩
private def output25 (w : Prefix 25) : ℝ := estimate25 (headsNat w)

def twentyFiveFlips : AdaptiveEstimator Unit where
  randomLaw := Measure.dirac ()
  probability := inferInstance
  policy := fun _ => freshPolicy 24
  policy_measurable := fun _ _ => measurableSet_eq_fun measurable_const measurable_const
  output := fun z => output25 (processPrefix 25 z.2)
  output_measurable := (measurable_of_countable output25).comp
    (Measurable.of_eval fun i => (measurable_pi_apply i.val).comp measurable_snd)

theorem twenty_five_budget (μ : Measure Gap) [IsProbabilityMeasure μ] : UniformBudget μ twentyFiveFlips 25 := by
  intro q
  apply HardBudget.pathwise_expected μ twentyFiveFlips q (by norm_num)
  rw [show ⌊(25:ℝ)⌋₊ = 25 by norm_num]
  exact HardBudget.stopAt_pathwise_cap twentyFiveFlips 25 (fun _ xs => xs.length) (fun _ => rfl)

theorem twenty_five_squared_risk (q : SignLaw) :
    squaredRisk (experimentLaw (Measure.dirac fifthGap) twentyFiveFlips q)
      (populationOutput twentyFiveFlips) (signMean (Measure.dirac fifthGap) q.val) ≤
        ENNReal.ofReal (radius^2) := by
  classical
  let p := q.val fifthGap
  let f := fun w : Prefix 25 => (output25 w - p)^2
  let P := experimentLaw (Measure.dirac fifthGap) twentyFiveFlips q
  have hm : Measurable (fun z : PopulationSeed Unit × ProcessTape => f (processPrefix 25 z.2)) :=
    (measurable_of_countable f).comp
      (Measurable.of_eval fun i => (measurable_pi_apply i.val).comp measurable_snd)
  obtain ⟨C,hC⟩ := (Set.finite_range fun w => |f w|).bddAbove
  have hbound (w) : |f w| ≤ C := hC ⟨w,rfl⟩
  have hi : Integrable (fun z : PopulationSeed Unit × ProcessTape => f (processPrefix 25 z.2)) P :=
    (integrable_const C).mono' hm.aestronglyMeasurable (ae_of_all _ fun z => hbound _)
  have hr := (population_realization Unit (Measure.dirac fifthGap) twentyFiveFlips q).2
    25 (fun _ => f) (fun _ => measurable_const) ⟨C, fun _ w => hbound w⟩
  have hseed : populationSeedLaw (Measure.dirac fifthGap) twentyFiveFlips =
      Measure.dirac ((), fun _ => fifthGap) := by
    simp [populationSeedLaw, twentyFiveFlips, Measure.infinitePi_dirac, Measure.dirac_prod_dirac]
  rw [hseed, integral_dirac] at hr
  change (∫ z, f (processPrefix 25 z.2) ∂P) =
      ∑ w, creationLaw (freshPolicy 24) (fun _ => 1/5) (fun _ => p) w * f w at hr
  let loss := fun k => (estimate25 k-p)^2
  have av := fresh_average 24 25 (by decide) (1/5) p (by norm_num [Set.mem_Icc]) (q.property.2 fifthGap) loss 0
  simp only [zero_add] at av
  change (∑ w : Prefix 25, creationLaw (freshPolicy 24) (fun _ => 1/5) (fun _ => p) w*f w) =
    binomialAverage _ loss 25 0 at av
  rw [av,binomial_sum] at hr
  simp only [zero_add] at hr
  rw [show signMean (Measure.dirac fifthGap) q.val = p by simp [signMean,p]]
  change (∫⁻ z, ENNReal.ofReal (f (processPrefix 25 z.2)) ∂P) ≤ _
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => sq_nonneg _), hr]
  exact ENNReal.ofReal_le_ofReal (table_risk p (q.property.2 fifthGap))


theorem upper_25 :
    minimaxRisk (Measure.dirac fifthGap) 25 ≤ ENNReal.ofReal radius := by
  unfold minimaxRisk
  refine le_trans (sInf_le (a := maximalRMSRisk (Measure.dirac fifthGap) twentyFiveFlips) ?_) ?_
  · exact ⟨Unit, inferInstance, twentyFiveFlips, twenty_five_budget _, rfl⟩
  apply iSup_le
  intro q
  apply HardBudget.rms_from_square _ _ _ _ (by norm_num)
  exact twenty_five_squared_risk q


/-- Any uniform coefficient at budgets B≥25 must cover the law concentrated at 1/5. -/
theorem coefficient_upper (c : ℝ) (h : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 25≤B →
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)*c) ≤ minimaxRisk μ B) :
    c ≤ radius := by
  have at25 := h (Measure.dirac fifthGap) 25 (by norm_num)
  have m : modulus (Measure.dirac fifthGap) (1/Real.sqrt 25)=1 := by
    norm_num [modulus,clippedGap,fifthGap,Real.sqrt_eq_iff_mul_self_eq]
  rw [m,one_mul] at at25
  exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp (at25.trans upper_25)

end ThresholdHC.SharpRMS.LargeBudget
