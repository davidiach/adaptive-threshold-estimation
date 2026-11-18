import ThresholdHC.SharpRMS.SingleTape
import ThresholdHC.SharpRMS.PopulationTransfer
import ThresholdHC.Tier6.RiskReduction

/-! Exact work and risk identities for the original experiment under causal simulation. -/
noncomputable section
namespace ThresholdHC.SharpRMS
open MeasureTheory Tier3 Tier5 Tier6 CriticalEntropy ContinuousObserved ObservableSimulation
open scoped ENNReal

theorem simulation_expected_work {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (g : Gap) (A : AdaptiveEstimator R) (q : SignLaw) :
    expectedWork (Measure.dirac g) (sourceEstimator μ g A) q = expectedWork μ A (sourceTarget g q) := by
  let F := fun z : R × ProcessTape => totalProcessWork z.2
  have m : Measurable F := measurable_totalProcessWork Prod.snd
    (fun n b => measurableSet_eq_fun ((measurable_pi_apply n).comp measurable_snd) measurable_const)
  simpa only [expectedWork,F,targetObservation,decodeTape_work] using
    transferred_observation μ g A q (sourceTarget g q) (single_tape_law μ g q) F m

theorem simulation_rms {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (g : Gap) (A : AdaptiveEstimator R) (q : SignLaw) :
    ENNReal.ofReal (modulus μ g.val) * rootMeanRisk (experimentLaw (Measure.dirac g) (sourceEstimator μ g A) q)
      (populationOutput (sourceEstimator μ g A)) (signMean (Measure.dirac g) q.val) =
    rootMeanRisk (experimentLaw μ A (sourceTarget g q)) (populationOutput A) (signMean μ (sourceTarget g q).val) := by
  let ω := modulus μ g.val
  have hp : 0 < ω := modulus_pos μ g.property.1
  let S := sourceEstimator μ g A
  let m := signMean μ (sourceTarget g q).val
  let loss := fun z : R × ProcessTape => ENNReal.ofReal ((A.output z-m)^2)
  have ml : Measurable loss := ENNReal.measurable_ofReal.comp ((A.output_measurable.sub measurable_const).pow_const 2)
  have eq := transferred_observation μ g A q (sourceTarget g q) (single_tape_law μ g q) loss ml
  have mean : signMean (Measure.dirac g) q.val=q.val g := by simp [signMean]
  have aff (x : ℝ) : ω*((x-(1-ω)/2)/ω-q.val g) = x-m := by
    dsimp only [m]
    rw [source_target_mean]
    change ω*((x-(1-ω)/2)/ω-q.val g) = x-(1+(2*q.val g-1)*ω)/2
    field_simp [hp.ne']
    ring
  have sq : ENNReal.ofReal (ω^2)*squaredRisk (experimentLaw (Measure.dirac g) S q) (populationOutput S)
      (signMean (Measure.dirac g) q.val) = squaredRisk (experimentLaw μ A (sourceTarget g q)) (populationOutput A) m := by
    unfold squaredRisk
    rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply Eq.trans _ eq
    apply lintegral_congr
    intro z
    rw [←ENNReal.ofReal_mul (sq_nonneg _),←mul_pow,mean]
    change ENNReal.ofReal ((ω*((A.output (targetObservation A g (z.1.1,z.2))-(1-ω)/2)/ω-q.val g))^2) = _
    rw [aff]
  have result := congrArg (fun x : ℝ≥0∞ => x^(1/2:ℝ)) sq
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),ofReal_square_rpow_half ω hp.le] at result
  exact result

/-- Every uniformly budgeted estimator for the target population induces one
for the critical point mass with the same expected work and rescaled error. -/
theorem critical_gap_reduction (μ : Measure Gap) [IsProbabilityMeasure μ] (g : Gap) (B : ℝ) :
    ENNReal.ofReal (modulus μ g.val)*minimaxRisk (Measure.dirac g) B ≤ minimaxRisk μ B := by
  apply le_sInf
  rintro x ⟨R,mR,A,hb,rfl⟩
  let S := sourceEstimator μ g A
  have budget : UniformBudget (Measure.dirac g) S B := fun q =>
    (simulation_expected_work μ g A q).le.trans (hb (sourceTarget g q))
  have low : minimaxRisk (Measure.dirac g) B ≤ maximalRMSRisk (Measure.dirac g) S :=
    sInf_le ⟨SourceSeed R,inferInstance,S,budget,rfl⟩
  apply (mul_le_mul_right low _).trans
  unfold maximalRMSRisk
  rw [ENNReal.mul_iSup]
  apply iSup_le
  intro q
  rw [simulation_rms μ g A q]
  exact le_iSup (fun p : SignLaw => rootMeanRisk (experimentLaw μ A p) (populationOutput A) (signMean μ p.val)) (sourceTarget g q)

end ThresholdHC.SharpRMS
