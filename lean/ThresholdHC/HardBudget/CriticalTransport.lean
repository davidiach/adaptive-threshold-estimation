import ThresholdHC.HardBudget.Application
import ThresholdHC.ConfidenceTransfer.CriticalModel
import ThresholdHC.CriticalUpper.Full

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.HardBudget
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.ObservableSimulation ThresholdHC.RareAboveTwo
open ThresholdHC.CriticalEntropy ThresholdHC.CriticalUpper ThresholdHC.ConfidenceTransfer

private theorem extend_critical_sign (u : SignLaw) :
    ∃ (q : ℝ → unitInterval) (hq : Measurable q), criticalSign q hq = u := by
  let f : Gap → ℝ := Subtype.val
  have hf : MeasurableEmbedding f := MeasurableEmbedding.subtype_coe
    (measurableSet_Ioc : MeasurableSet (Ioc (0:ℝ) (1/2)))
  let q := Function.extend f (signUnit u) (fun _ => 0)
  have hm : Measurable q := hf.measurable_extend (measurable_signUnit u) measurable_const
  refine ⟨q,hm,Subtype.ext (funext (fun d => ?_))⟩
  exact congrArg Subtype.val (hf.injective.extend_apply (signUnit u) (fun _ => 0) d)

theorem critical_observable_transport {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    (q : ℝ → unitInterval) (hq : Measurable q) (F : R × ProcessTape → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, F (z.1.1,z.2) ∂experimentLaw criticalPositiveLaw A (criticalSign q hq)) =
      ∫⁻ z, F (z.1.1,z.2) ∂criticalExperimentLaw A q hq := by
  rw [original_observable_lintegral _ _ _ _ hF,critical_observable_lintegral _ _ _ _ hF]
  have he : originalPopulationTapeLaw criticalPositiveLaw (criticalSign q hq) = criticalTapeLaw q :=
    congrArg parameterTapeLaw (critical_parameter_law q hq)
  simp only [originalSimulationLaw,criticalSimulationLaw,he]

private theorem transport_work {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    (q : ℝ → unitInterval) (hq : Measurable q) :
    expectedWork criticalPositiveLaw A (criticalSign q hq) = criticalExpectedWork A q hq := by
  apply critical_observable_transport A q hq (fun z => totalProcessWork z.2)
  exact measurable_totalProcessWork Prod.snd (fun n b =>
    measurableSet_eq_fun ((measurable_pi_apply n).comp measurable_snd) measurable_const)

private theorem transport_rms {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    (q : ℝ → unitInterval) (hq : Measurable q) :
    rootMeanRisk (experimentLaw criticalPositiveLaw A (criticalSign q hq)) (populationOutput A)
      (signMean criticalPositiveLaw (criticalSign q hq).val) =
    rootMeanRisk (criticalExperimentLaw A q hq) (fun z => A.output (z.1.1,z.2))
      (∫ d, (q d : ℝ) ∂criticalGapLaw) := by
  rw [critical_sign_mean]
  apply congrArg (fun t : ℝ≥0∞ => t^(1/2:ℝ))
  exact critical_observable_transport A q hq (fun z => loss _ (A.output z)) ((measurable_loss _).comp A.output_measurable)

theorem critical_budget_equivalence {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (ρ B : ℝ) :
    CriticalUniformBudget A ρ B ↔ RareBudget criticalPositiveLaw A ρ B := by
  constructor
  · intro h u hu
    obtain ⟨q,hq,rfl⟩ := extend_critical_sign u
    rw [transport_work]
    exact h q hq ((critical_sign_mean q hq).ge.trans hu)
  · intro h q hq hm
    rw [← transport_work]
    exact h _ ((critical_sign_mean q hq).le.trans hm)

theorem critical_risk_equivalence {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (ρ : ℝ) :
    criticalMaximalRMSRisk A ρ = rareRisk criticalPositiveLaw A ρ := by
  apply le_antisymm
  · apply iSup_le; intro q; apply iSup_le; intro hq; apply iSup_le; intro hm
    rw [← transport_rms]
    exact le_iSup_of_le (criticalSign q hq) (le_iSup_of_le
      (show RarePrior criticalPositiveLaw ρ (criticalSign q hq) from (critical_sign_mean q hq).le.trans hm) le_rfl)
  · apply iSup_le; intro u; apply iSup_le; intro hu
    obtain ⟨q,hq,rfl⟩ := extend_critical_sign u
    rw [transport_rms]
    exact le_iSup_of_le q (le_iSup_of_le hq (le_iSup_of_le ((critical_sign_mean q hq).ge.trans hu) le_rfl))

end ThresholdHC.HardBudget
