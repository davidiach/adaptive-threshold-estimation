import ThresholdHC.StoppingProgram.CreationInformation
import ThresholdHC.CriticalEntropy.SeededPopulationTransfer
import ThresholdHC.RareAboveTwo.TerminalInformation

/-! The actual seed-and-prefix experiment obeys the midpoint information/work
bound for arbitrary measurable seed spaces and adaptive population policies. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.StoppingProgram
open ThresholdHC.CriticalEntropy ThresholdHC.ObservableSimulation
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.RareAboveTwo

theorem observable_prefix_information {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    (q r : SignLaw) (N : ℕ) :
    1-(hellingerAffinity (observablePrefixLaw μ A q N)
      (observablePrefixLaw μ A r N)).toReal ≤
      (informationRatio μ N (midpointFourPriors q r)).toReal/4 *
        ∫ z, ThresholdHC.workOf (processPrefix N z.2) ∂experimentLaw μ A (midpointPrior q r) := by
  have h := observable_population_hellinger_bound A.randomLaw μ
    (experimentLaw μ A q) (experimentLaw μ A r) (experimentLaw μ A (midpointPrior q r))
    Prod.fst Prod.snd A.policy (fun d : Gap => (d : ℝ)) q.val r.val (midpointPrior q r).val
    measurable_fst observable_tape_measurable A.policy_measurable measurable_subtype_coe
    q.property.1 r.property.1 (midpointPrior q r).property.1
    (fun d => ⟨d.property.1.le,d.property.2⟩) q.property.2 r.property.2 (midpointPrior q r).property.2
    (population_realization R μ A q).2 (population_realization R μ A r).2
    (population_realization R μ A (midpointPrior q r)).2 N 1
    ((informationRatio μ N (midpointFourPriors q r)).toReal/4)
    (fun u => by simpa only [mul_one] using creation_population_information μ q r (A.policy u) N)
  simpa only [mul_one,observablePrefixLaw] using h

theorem observable_prefix_information_budget {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    (q r : SignLaw) (N : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hw : expectedWork μ A (midpointPrior q r) ≤ ENNReal.ofReal B) :
    1-(hellingerAffinity (observablePrefixLaw μ A q N)
      (observablePrefixLaw μ A r N)).toReal ≤
      (informationRatio μ N (midpointFourPriors q r)).toReal/4*B := by
  have hfin : expectedWork μ A (midpointPrior q r) < ⊤ := hw.trans_lt (by simp)
  have hpre := prefix_work_le_total (experimentLaw μ A (midpointPrior q r))
    Prod.snd observable_tape_measurable hfin N
  have hwork : (expectedWork μ A (midpointPrior q r)).toReal ≤ B := by
    have h := ENNReal.toReal_mono (by simp : ENNReal.ofReal B ≠ ⊤) hw
    simpa only [ENNReal.toReal_ofReal hB] using h
  exact (observable_prefix_information μ A q r N).trans
    (mul_le_mul_of_nonneg_left (hpre.trans hwork) (by positivity))

end ThresholdHC.StoppingProgram
