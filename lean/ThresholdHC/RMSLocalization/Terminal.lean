import ThresholdHC.RMSLocalization.Observable

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.RMSLocalization
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.CriticalEntropy ThresholdHC.RareAboveTwo
open ThresholdHC.ObservableSimulation ThresholdHC.ConfidenceTransfer

/-- Uniform prefix bounds extend to the actual stopped finite decision.
Each endpoint supplies its own finite-work reconstruction. -/
theorem terminal_null_hellinger {R I : Type} [MeasurableSpace R]
    [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q r : SignLaw)
    (hqhalf : ∀ d, q.val d ≤ 1/2) (hrhalf : ∀ d, r.val d ≤ 1/2)
    (κ B : ℝ) (hκ : 0 ≤ κ) (hB : 0 ≤ B)
    (hloc : LocalNullWorkBound μ (gapParameter false) (gapParameter true) (signUnit q) (signUnit r) κ)
    (hwq : expectedWork μ A q < ∞) (hwr : expectedWork μ A r < ∞)
    (hwm : expectedWork μ A (ThresholdHC.StoppingProgram.midpointPrior q r) ≤ ENNReal.ofReal B)
    (f : R × ProcessTape → I) (hf : Measurable f) :
    1-(hellingerAffinity (observableDecisionLaw μ A q f) (observableDecisionLaw μ A r f)).toReal ≤ 2*κ*B := by
  let s := ThresholdHC.StoppingProgram.midpointPrior q r
  have hmfin := hwm.trans_lt ENNReal.ofReal_lt_top
  have hwork : (expectedWork μ A s).toReal ≤ B := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hwm
    rwa [ENNReal.toReal_ofReal hB] at h
  have hprefix (n : ℕ) :
      (1-(hellingerAffinity (observablePrefixLaw μ A q n) (observablePrefixLaw μ A r n)).toReal)*1 ≤ 2*κ*B := by
    rw [mul_one]
    apply (observable_null_hellinger μ A q r hqhalf hrhalf n κ hκ hloc).trans
    exact mul_le_mul_of_nonneg_left
      ((prefix_work_le_total (experimentLaw μ A s) Prod.snd observable_tape_measurable hmfin n).trans hwork)
      (by positivity)
  have h := observable_terminal_affinity_bound μ A q r hwq hwr f hf 1 (2*κ*B) (by norm_num) hprefix
  simpa only [mul_one] using h

end ThresholdHC.RMSLocalization
