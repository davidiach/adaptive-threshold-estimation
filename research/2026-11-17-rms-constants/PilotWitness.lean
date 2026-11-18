import PilotCertificate
import LargeBudgetWitness

/-! A hard cap of 25 flips and a uniform risk certificate for the pilot decision tree. -/
noncomputable section
namespace ThresholdHC.SharpRMS.Pilot
open MeasureTheory Tier3 Tier5 Tier6 Proofs LargeBudget
open scoped ENNReal

private def output25 (w : Prefix 25) : ℝ :=
  (entry (((fullHist w).take 18).count true) (index ((fullHist w).drop 18)) : ℝ)/100000

def pilotEstimator : AdaptiveEstimator Unit where
  randomLaw := Measure.dirac ()
  probability := inferInstance
  policy := fun _ => policy protocolChoices
  policy_measurable := fun _ _ => measurableSet_eq_fun measurable_const measurable_const
  output := fun z => output25 (processPrefix 25 z.2)
  output_measurable := (measurable_of_countable output25).comp
    (Measurable.of_eval fun i => (measurable_pi_apply i.val).comp measurable_snd)

theorem pilot_cap : HardBudget.PathwiseCap pilotEstimator 25 :=
  HardBudget.stopAt_pathwise_cap pilotEstimator 25 (fun _ => label protocolChoices) (fun _ => rfl)

theorem pilot_budget (μ : Measure Gap) [IsProbabilityMeasure μ] : UniformBudget μ pilotEstimator 25 := by
  intro q
  apply HardBudget.pathwise_expected μ pilotEstimator q (by norm_num)
  rw [show ⌊(25:ℝ)⌋₊ = 25 by norm_num]
  exact pilot_cap

theorem pilot_risk_formula (q : SignLaw) :
    squaredRisk (experimentLaw (Measure.dirac fifthGap) pilotEstimator q)
      (populationOutput pilotEstimator) (signMean (Measure.dirac fifthGap) q.val) =
        ENNReal.ofReal (Revisit.IntPoly.value (riskPoly protocolChoices entry) (q.val fifthGap) / 10^35) := by
  classical
  let p := q.val fifthGap
  let f := fun w : Prefix 25 => (output25 w - p)^2
  let P := experimentLaw (Measure.dirac fifthGap) pilotEstimator q
  have hm : Measurable (fun z : PopulationSeed Unit × ProcessTape => f (processPrefix 25 z.2)) :=
    (measurable_of_countable f).comp
      (Measurable.of_eval fun i => (measurable_pi_apply i.val).comp measurable_snd)
  obtain ⟨C,hC⟩ := (Set.finite_range fun w => |f w|).bddAbove
  have hbound (w) : |f w| ≤ C := hC ⟨w,rfl⟩
  have hi : Integrable (fun z : PopulationSeed Unit × ProcessTape => f (processPrefix 25 z.2)) P :=
    (integrable_const C).mono' hm.aestronglyMeasurable (ae_of_all _ fun z => hbound _)
  have hr := (population_realization Unit (Measure.dirac fifthGap) pilotEstimator q).2
    25 (fun _ => f) (fun _ => measurable_const) ⟨C, fun _ w => hbound w⟩
  have hseed : populationSeedLaw (Measure.dirac fifthGap) pilotEstimator =
      Measure.dirac ((), fun _ => fifthGap) := by
    simp [populationSeedLaw, pilotEstimator, Measure.infinitePi_dirac, Measure.dirac_prod_dirac]
  rw [hseed, integral_dirac] at hr
  have av := expect_counts protocolChoices (loss entry p) p (q.property.2 fifthGap)
  change (∑ w : Prefix 25, Revisit.law (policy protocolChoices) p w*f w) = _ at av
  change (∫ z, f (processPrefix 25 z.2) ∂P) = ∑ w : Prefix 25, Revisit.law (policy protocolChoices) p w*f w at hr
  rw [av] at hr
  rw [show signMean (Measure.dirac fifthGap) q.val = p by simp [signMean,p]]
  change (∫⁻ z, ENNReal.ofReal (f (processPrefix 25 z.2)) ∂P) = _
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => sq_nonneg _), hr]
  rw [risk_value _ _ _ (q.property.2 fifthGap)]
  have cancel (x : ℝ) : x=(10:ℝ)^35*x/10^35 := by ring
  exact congrArg ENNReal.ofReal (cancel _)

/-- The worst squared risk for this particular decision tree is attained at p=0.
The same value occurs at p=1 by endpoint_one. -/
theorem pilot_worst_squared :
    (⨆ q : SignLaw, squaredRisk (experimentLaw (Measure.dirac fifthGap) pilotEstimator q)
      (populationOutput pilotEstimator) (signMean (Measure.dirac fifthGap) q.val)) =
      ENNReal.ofReal ((endpoint:ℝ) / 10^35) := by
  apply le_antisymm
  · apply iSup_le
    intro q
    rw [pilot_risk_formula]
    exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (certificate _ (q.property.2 fifthGap)) (by norm_num))
  · let zero : SignLaw := ⟨fun _ => 0, measurable_const, fun _ => by constructor <;> norm_num⟩
    apply le_trans _ (le_iSup (fun q : SignLaw => squaredRisk (experimentLaw (Measure.dirac fifthGap) pilotEstimator q)
      (populationOutput pilotEstimator) (signMean (Measure.dirac fifthGap) q.val)) zero)
    rw [pilot_risk_formula]
    change _ ≤ ENNReal.ofReal (Revisit.IntPoly.value (riskPoly protocolChoices entry) 0 / 10^35)
    rw [endpoint_value]

theorem pilot_squared_risk (q : SignLaw) :
    squaredRisk (experimentLaw (Measure.dirac fifthGap) pilotEstimator q)
      (populationOutput pilotEstimator) (signMean (Measure.dirac fifthGap) q.val) ≤
        ENNReal.ofReal (bound^2) := by
  have h := le_iSup (fun s : SignLaw => squaredRisk (experimentLaw (Measure.dirac fifthGap) pilotEstimator s)
    (populationOutput pilotEstimator) (signMean (Measure.dirac fifthGap) s.val)) q
  rw [pilot_worst_squared] at h
  exact h.trans (ENNReal.ofReal_le_ofReal (by norm_num [endpoint,bound]))

theorem pilot_upper_25 :
    minimaxRisk (Measure.dirac fifthGap) 25 ≤ ENNReal.ofReal bound := by
  unfold minimaxRisk
  refine le_trans (sInf_le (a := maximalRMSRisk (Measure.dirac fifthGap) pilotEstimator) ?_) ?_
  · exact ⟨Unit, inferInstance, pilotEstimator, pilot_budget _, rfl⟩
  apply iSup_le
  intro q
  apply HardBudget.rms_from_square _ _ _ _ (by norm_num)
  exact pilot_squared_risk q

/-- Any uniform coefficient at budgets B≥25 must cover the law concentrated at 1/5. -/
theorem pilot_coefficient_upper (c : ℝ) (h : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 25≤B →
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)*c) ≤ minimaxRisk μ B) :
    c ≤ bound := by
  have at25 := h (Measure.dirac fifthGap) 25 (by norm_num)
  have m : modulus (Measure.dirac fifthGap) (1/Real.sqrt 25)=1 := by
    norm_num [modulus,clippedGap,fifthGap,Real.sqrt_eq_iff_mul_self_eq]
  rw [m,one_mul] at at25
  exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp (at25.trans pilot_upper_25)

end ThresholdHC.SharpRMS.Pilot
