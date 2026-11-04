import ThresholdHC.HardBudget.Ordinary
import ThresholdHC.HardBudget.Rare
import ThresholdHC.HardBudget.Critical
noncomputable section
open ThresholdHC.HardBudget ThresholdHC.Tier6 ThresholdHC.ObservableSimulation
open scoped ENNReal
example {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (r : R) (n : ℕ) (M : ℝ) (s : Table) :
    stageOutput A M r (readBlock n (fun h => (A.policy r h).getD 0) s).1 = stageResult A n M r s :=
  stageOutput_correct A M n r s
example {R : ℕ → Type} [∀ j, MeasurableSpace (R j)] (A : ∀ j, AdaptiveEstimator (R j))
    (r : ∀ j, R j) (s : Table) (k j : ℕ) :
    (readBlock (paid k) (planReader A r k) s).2 (Nat.pair k j) = s (Nat.pair k j) :=
  next_stage_fresh A r k s j
example {R : ℕ → Type} [∀ j, MeasurableSpace (R j)] (A : ∀ j, AdaptiveEstimator (R j))
    (M : ℝ) (r : ∀ j, R j) (s : Table) (k : ℕ) :
    planOutput A M r k (readBlock (paid k) (planReader A r k) s).1 = idealFallback A M r s k :=
  planOutput_readBlock A M r s k
example {R : ℕ → Type} [∀ j, MeasurableSpace (R j)] (A : ∀ j, AdaptiveEstimator (R j))
    (M : ℝ) (k : ℕ) : PathwiseCap (estimator A M k) (paid k) := estimator_cap A M k
example {R : ℕ → Type} [∀ j, MeasurableSpace (R j)] (A : ∀ j, AdaptiveEstimator (R j))
    (M : ℝ) (k : ℕ) (μ : MeasureTheory.Measure Gap) [MeasureTheory.IsProbabilityMeasure μ] (q : SignLaw) :
    MeasureTheory.MeasurePreserving stageInputs (originalSimulationLaw μ (estimator A M k) q)
      (MeasureTheory.Measure.infinitePi (fun i => originalSimulationLaw μ (A i) q)) :=
  stageInputs_preserving A M k μ q
example : ObservableFallbackStatement := observable_fallback
example (μ : MeasureTheory.Measure Gap) [MeasureTheory.IsProbabilityMeasure μ] {B : ℝ} (hB : 1 ≤ B) :
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)/64) ≤ hardMinimaxRisk μ B ∧
      hardMinimaxRisk μ B ≤ ENNReal.ofReal (3000*modulus μ (1/Real.sqrt B)) := ordinary_hard_minimax μ hB
example : ∃ rule : ℝ → AdaptiveEstimator (ℕ → ThresholdHC.BlindUpper.BatchSeed),
    (∀ B : ℝ, 0 ≤ B → PathwiseCap (rule B) ⌊B⌋₊) ∧
    ∀ (B : ℝ), 0 < B → ∀ (μ : MeasureTheory.Measure Gap) [MeasureTheory.IsProbabilityMeasure μ],
      maximalRMSRisk μ (rule B) ≤ ENNReal.ofReal (3000*modulus μ (1/Real.sqrt B)) := ordinary_hard_family
example (μ : MeasureTheory.Measure Gap) [MeasureTheory.IsProbabilityMeasure μ] {ρ B : ℝ}
    (hr : 0 < ρ) (hu : ρ ≤ 1/4) (hb : 0 < B) :
    ENNReal.ofReal ((10:ℝ)⁻¹^17)*ThresholdHC.EntropyTail.selection μ ρ B ≤ hardRareMinimaxRisk μ ρ B ∧
      hardRareMinimaxRisk μ ρ B ≤ 160000*ThresholdHC.EntropyTail.selection μ ρ B := rare_hard_minimax μ hr hu hb
open ThresholdHC.ConfidenceTransfer ThresholdHC.CriticalEntropy
example : ∃ c : ℝ, 0 < c ∧ ∀ {ρ B : ℝ}, 0 < ρ → ρ ≤ 1/4 → 0 < B →
    ENNReal.ofReal (c*min ρ (Real.sqrt (ρ*criticalLogFactor ρ/B))) ≤ hardRareMinimaxRisk criticalPositiveLaw ρ B ∧
    hardRareMinimaxRisk criticalPositiveLaw ρ B ≤ ENNReal.ofReal (570000*min ρ (Real.sqrt (ρ*criticalLogFactor ρ/B))) :=
  critical_hard_minimax
#print axioms ThresholdHC.HardBudget.block_path
#print axioms ThresholdHC.HardBudget.clip_loss_le
#print axioms ThresholdHC.HardBudget.count_at_checkpoint
#print axioms ThresholdHC.HardBudget.count_zero_of_small
#print axioms ThresholdHC.HardBudget.critical_budget_equivalence
#print axioms ThresholdHC.HardBudget.critical_hard_family
#print axioms ThresholdHC.HardBudget.critical_hard_minimax
#print axioms ThresholdHC.HardBudget.critical_observable_transport
#print axioms ThresholdHC.HardBudget.critical_rate_scale
#print axioms ThresholdHC.HardBudget.critical_rate_small
#print axioms ThresholdHC.HardBudget.critical_risk_equivalence
#print axioms ThresholdHC.HardBudget.decode_correct
#print axioms ThresholdHC.HardBudget.estimator
#print axioms ThresholdHC.HardBudget.estimator_cap
#print axioms ThresholdHC.HardBudget.estimator_output
#print axioms ThresholdHC.HardBudget.estimator_squared_loss
#print axioms ThresholdHC.HardBudget.expected_loss_step
#print axioms ThresholdHC.HardBudget.fallback_rate
#print axioms ThresholdHC.HardBudget.next_stage_fresh
#print axioms ThresholdHC.HardBudget.observable_fallback
#print axioms ThresholdHC.HardBudget.ordinary_budget_scale
#print axioms ThresholdHC.HardBudget.ordinary_hard_family
#print axioms ThresholdHC.HardBudget.ordinary_hard_minimax
#print axioms ThresholdHC.HardBudget.paid_fits
#print axioms ThresholdHC.HardBudget.pathwise_expected
#print axioms ThresholdHC.HardBudget.planOutput_readBlock
#print axioms ThresholdHC.HardBudget.rare_hard_family
#print axioms ThresholdHC.HardBudget.rare_hard_minimax
#print axioms ThresholdHC.HardBudget.readBlock_append
#print axioms ThresholdHC.HardBudget.readBlock_length
#print axioms ThresholdHC.HardBudget.readBlock_relabel
#print axioms ThresholdHC.HardBudget.readBlock_untouched
#print axioms ThresholdHC.HardBudget.rms_family
#print axioms ThresholdHC.HardBudget.selection_budget_scale
#print axioms ThresholdHC.HardBudget.selection_saturates
#print axioms ThresholdHC.HardBudget.stageInputs_preserving
#print axioms ThresholdHC.HardBudget.stageOutput_correct
#print axioms ThresholdHC.HardBudget.stage_loss_le
#print axioms ThresholdHC.HardBudget.timeout_quarter
