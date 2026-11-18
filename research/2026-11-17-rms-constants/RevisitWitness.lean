import RevisitRisk
import LargeBudgetWitness

/-! A hard cap of 25 flips and a uniform risk certificate for the adaptive revisit rule. -/
noncomputable section
namespace ThresholdHC.SharpRMS.Revisit
open MeasureTheory Tier3 Tier5 Tier6 Proofs LargeBudget
open scoped ENNReal

private def output25 (w : Prefix 25) : ℝ :=
  estimate (((fullHist w).take 20).count true) (((fullHist w).drop 20).count true)

def revisitEstimator : AdaptiveEstimator Unit where
  randomLaw := Measure.dirac ()
  probability := inferInstance
  policy := fun _ => policy
  policy_measurable := fun _ _ => measurableSet_eq_fun measurable_const measurable_const
  output := fun z => output25 (processPrefix 25 z.2)
  output_measurable := (measurable_of_countable output25).comp
    (Measurable.of_eval fun i => (measurable_pi_apply i.val).comp measurable_snd)

theorem revisit_cap : HardBudget.PathwiseCap revisitEstimator 25 :=
  HardBudget.stopAt_pathwise_cap revisitEstimator 25 (fun _ => label) (fun _ => rfl)

theorem revisit_budget (μ : Measure Gap) [IsProbabilityMeasure μ] : UniformBudget μ revisitEstimator 25 := by
  intro q
  apply HardBudget.pathwise_expected μ revisitEstimator q (by norm_num)
  rw [show ⌊(25:ℝ)⌋₊ = 25 by norm_num]
  exact revisit_cap

theorem revisit_squared_risk (q : SignLaw) :
    squaredRisk (experimentLaw (Measure.dirac fifthGap) revisitEstimator q)
      (populationOutput revisitEstimator) (signMean (Measure.dirac fifthGap) q.val) ≤
        ENNReal.ofReal (bound^2) := by
  classical
  let p := q.val fifthGap
  let f := fun w : Prefix 25 => (output25 w - p)^2
  let P := experimentLaw (Measure.dirac fifthGap) revisitEstimator q
  have hm : Measurable (fun z : PopulationSeed Unit × ProcessTape => f (processPrefix 25 z.2)) :=
    (measurable_of_countable f).comp
      (Measurable.of_eval fun i => (measurable_pi_apply i.val).comp measurable_snd)
  obtain ⟨C,hC⟩ := (Set.finite_range fun w => |f w|).bddAbove
  have hbound (w) : |f w| ≤ C := hC ⟨w,rfl⟩
  have hi : Integrable (fun z : PopulationSeed Unit × ProcessTape => f (processPrefix 25 z.2)) P :=
    (integrable_const C).mono' hm.aestronglyMeasurable (ae_of_all _ fun z => hbound _)
  have hr := (population_realization Unit (Measure.dirac fifthGap) revisitEstimator q).2
    25 (fun _ => f) (fun _ => measurable_const) ⟨C, fun _ w => hbound w⟩
  have hseed : populationSeedLaw (Measure.dirac fifthGap) revisitEstimator =
      Measure.dirac ((), fun _ => fifthGap) := by
    simp [populationSeedLaw, revisitEstimator, Measure.infinitePi_dirac, Measure.dirac_prod_dirac]
  rw [hseed, integral_dirac] at hr
  have av := expect_counts (fun j k => (estimate j k-p)^2) p (q.property.2 fifthGap)
  change (∑ w : Prefix 25, law policy p w*f w) = _ at av
  change (∫ z, f (processPrefix 25 z.2) ∂P) = ∑ w : Prefix 25, law policy p w*f w at hr
  rw [av] at hr
  rw [show signMean (Measure.dirac fifthGap) q.val = p by simp [signMean,p]]
  change (∫⁻ z, ENNReal.ofReal (f (processPrefix 25 z.2)) ∂P) ≤ _
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => sq_nonneg _), hr]
  exact ENNReal.ofReal_le_ofReal (adaptive_binomial_risk p (q.property.2 fifthGap))

theorem revisit_upper_25 :
    minimaxRisk (Measure.dirac fifthGap) 25 ≤ ENNReal.ofReal bound := by
  unfold minimaxRisk
  refine le_trans (sInf_le (a := maximalRMSRisk (Measure.dirac fifthGap) revisitEstimator) ?_) ?_
  · exact ⟨Unit, inferInstance, revisitEstimator, revisit_budget _, rfl⟩
  apply iSup_le
  intro q
  apply HardBudget.rms_from_square _ _ _ _ (by norm_num)
  exact revisit_squared_risk q

/-- Any uniform coefficient at budgets B≥25 must cover the law concentrated at 1/5. -/
theorem revisit_coefficient_upper (c : ℝ) (h : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 25≤B →
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)*c) ≤ minimaxRisk μ B) :
    c ≤ bound := by
  have at25 := h (Measure.dirac fifthGap) 25 (by norm_num)
  have m : modulus (Measure.dirac fifthGap) (1/Real.sqrt 25)=1 := by
    norm_num [modulus,clippedGap,fifthGap,Real.sqrt_eq_iff_mul_self_eq]
  rw [m,one_mul] at at25
  exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp (at25.trans revisit_upper_25)

end ThresholdHC.SharpRMS.Revisit
