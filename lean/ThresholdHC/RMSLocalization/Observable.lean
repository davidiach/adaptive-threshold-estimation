import ThresholdHC.RMSLocalization.Creation

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.RMSLocalization
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.CriticalEntropy
open ThresholdHC.ObservableSimulation ThresholdHC.ConfidenceTransfer ThresholdHC.RareAboveTwo

theorem signUnit_midpoint (q r : SignLaw) :
    signUnit (ThresholdHC.StoppingProgram.midpointPrior q r) =
      midpointPrior (signUnit q) (signUnit r) := by
  funext d
  apply Subtype.ext
  change (1/2)*q.val d+(1-1/2)*r.val d = (q.val d+r.val d)/2
  ring

theorem observable_null_hellinger {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q r : SignLaw)
    (hqhalf : ∀ d, q.val d ≤ 1/2) (hrhalf : ∀ d, r.val d ≤ 1/2)
    (n : ℕ) (κ : ℝ) (hκ : 0 ≤ κ)
    (hloc : LocalNullWorkBound μ (gapParameter false) (gapParameter true) (signUnit q) (signUnit r) κ) :
    1-(hellingerAffinity (observablePrefixLaw μ A q n) (observablePrefixLaw μ A r n)).toReal ≤
      2*κ*∫ z, ThresholdHC.workOf (processPrefix n z.2)
        ∂experimentLaw μ A (ThresholdHC.StoppingProgram.midpointPrior q r) := by
  let s := ThresholdHC.StoppingProgram.midpointPrior q r
  have hpoint (u : R) :
      1-realFiniteAffinity (creationPopulationWeight (n := n) μ (A.policy u) (fun d : Gap => (d : ℝ)) q.val)
        (creationPopulationWeight μ (A.policy u) (fun d : Gap => (d : ℝ)) r.val) ≤
        2*κ*∑ w : Prefix n, creationPopulationWeight μ (A.policy u) (fun d : Gap => (d : ℝ)) s.val w*ThresholdHC.workOf w := by
    have h := creation_null_hellinger μ (gapParameter false) (gapParameter true) (signUnit q) (signUnit r)
      (measurable_gapParameter false) (measurable_gapParameter true) (measurable_signUnit q) (measurable_signUnit r)
      hqhalf hrhalf (fun d : Gap => (d : ℝ)) measurable_subtype_coe (fun d => ⟨d.property.1.le,d.property.2⟩)
      (ae_of_all _ (fun d => by simp [gapParameter,sub_eq_add_neg]))
      (ae_of_all _ (fun d => by simp [gapParameter])) (A.policy u) n κ hκ hloc
    dsimp only at h
    rw [← signUnit_midpoint q r] at h
    exact h
  have h := observable_population_hellinger_bound A.randomLaw μ
    (experimentLaw μ A q) (experimentLaw μ A r) (experimentLaw μ A s)
    Prod.fst Prod.snd A.policy (fun d : Gap => (d : ℝ)) q.val r.val s.val
    measurable_fst observable_tape_measurable A.policy_measurable measurable_subtype_coe
    q.property.1 r.property.1 s.property.1 (fun d => ⟨d.property.1.le,d.property.2⟩)
    q.property.2 r.property.2 s.property.2
    (population_realization R μ A q).2 (population_realization R μ A r).2 (population_realization R μ A s).2
    n 1 (2*κ) (fun u => by simpa only [mul_one] using hpoint u)
  simpa only [mul_one,observablePrefixLaw,s] using h

end ThresholdHC.RMSLocalization
