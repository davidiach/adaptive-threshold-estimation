import ThresholdHC.CriticalEntropy.CriticalTerminalAffinity

noncomputable section

namespace ThresholdHC.CriticalEntropy
open MeasureTheory Set ThresholdHC.Tier3
open scoped ENNReal
set_option maxHeartbeats 2000000

/-- The full rare class permits every measurable prior valued in [0,1].
The half-capped class is used only to construct a lower-bound pair. -/
def CriticalRarePrior (ρ : ℝ) (q : ℝ → unitInterval) : Prop :=
  Measurable q ∧ (∫ d, (q d : ℝ) ∂criticalGapLaw) ≤ ρ

def CriticalUniformBudget {R : Type} [MeasurableSpace R]
    (A : Tier6.AdaptiveEstimator R) (ρ B : ℝ) : Prop :=
  ∀ (q : ℝ → unitInterval) (hq : Measurable q),
    (∫ d, (q d : ℝ) ∂criticalGapLaw) ≤ ρ → criticalExpectedWork A q hq ≤ ENNReal.ofReal B

def criticalMaximalRMSRisk {R : Type} [MeasurableSpace R]
    (A : Tier6.AdaptiveEstimator R) (ρ : ℝ) : ℝ≥0∞ :=
  ⨆ (q : ℝ → unitInterval) (hq : Measurable q)
    (_ : (∫ d, (q d : ℝ) ∂criticalGapLaw) ≤ ρ),
    Tier6.rootMeanRisk (criticalExperimentLaw A q hq)
      (fun z => A.output (z.1.1,z.2)) (∫ d, (q d : ℝ) ∂criticalGapLaw)

def criticalMinimaxRisk (ρ B : ℝ) : ℝ≥0∞ :=
  sInf {r | ∃ (R : Type) (_ : MeasurableSpace R) (A : Tier6.AdaptiveEstimator R),
    CriticalUniformBudget A ρ B ∧ r = criticalMaximalRMSRisk A ρ}

/-- One pair controls every finite observable decision of every admissible
infinite-experiment algorithm. Endpoint stopping follows from the full budget
class, and the information bound charges work under its admissible midpoint. -/
theorem critical_common_terminal_pair : ∃ C : ℝ, 0 < C ∧
    ∀ (ρ : unitInterval), 0 < (ρ : ℝ) → (ρ : ℝ) ≤ 1/4 →
    ∀ δ : ℝ, 0 ≤ δ → δ ≤ (ρ : ℝ)/96 →
    ∃ (q r : ℝ → unitInterval) (hq : CappedPrior criticalGapLaw (ρ : ℝ) q)
      (hr : CappedPrior criticalGapLaw (ρ : ℝ) r),
      δ ≤ (∫ d, (r d : ℝ) ∂criticalGapLaw)-(∫ d, (q d : ℝ) ∂criticalGapLaw) ∧
      ∀ (R I : Type) [MeasurableSpace R] [Fintype I] [MeasurableSpace I]
        [MeasurableSingletonClass I] (A : Tier6.AdaptiveEstimator R)
        (B : ℝ), 0 ≤ B → CriticalUniformBudget A (ρ : ℝ) B →
        ∀ (f : R × ProcessTape → I), Measurable f →
        (1-(hellingerAffinity (criticalObservationLaw A q hq.1 f)
          (criticalObservationLaw A r hr.1 f)).toReal)*(ρ : ℝ)*criticalLogFactor (ρ : ℝ) ≤
          C*δ^2*B := by
  obtain ⟨C,hC,hcommon⟩ := critical_common_experiment_prefix_pair
  refine ⟨C,hC,?_⟩
  intro ρ hρ hρ' δ hδ hδρ
  obtain ⟨q,r,hq,hr,hsep,hpair⟩ := hcommon ρ hρ hρ' δ hδ hδρ
  refine ⟨q,r,hq,hr,hsep,?_⟩
  intro R I _ _ _ _ A B hB hbudget f hf
  have hqwork := hbudget q hq.1 hq.2.2
  have hrwork := hbudget r hr.1 hr.2.2
  have hqfin := hqwork.trans_lt ENNReal.ofReal_lt_top
  have hrfin := hrwork.trans_lt ENNReal.ofReal_lt_top
  have hs := cappedPrior_midpoint criticalGapLaw (ρ : ℝ) q r hq hr
  have hswork := hbudget (midpointPrior q r) hs.1 hs.2.2
  have hsfin := hswork.trans_lt ENNReal.ofReal_lt_top
  have hsreal : (criticalExpectedWork A (midpointPrior q r) hs.1).toReal ≤ B :=
    ENNReal.toReal_le_of_le_ofReal hB hswork
  have hterminal := critical_terminal_affinity_bound A q r hq.1 hr.1 hqfin hrfin f hf
    ((ρ : ℝ)*criticalLogFactor (ρ : ℝ)) (C*δ^2*B)
    (mul_nonneg hρ.le (criticalLogFactor_pos (ρ : ℝ) hρ ρ.property.2).le) (fun n => by
      have hw := (critical_prefix_work_le_total A (midpointPrior q r) hs.1 hsfin n).trans hsreal
      have hb := (hpair R A n).trans (mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ C*δ^2))
      simpa only [mul_assoc] using hb)
  simpa only [mul_assoc] using hterminal

end ThresholdHC.CriticalEntropy
