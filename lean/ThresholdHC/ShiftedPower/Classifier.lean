import ThresholdHC.EntropyTailExecution.AllocatedEstimator
import ThresholdHC.BlindUpper.CutoffBiasWork
import ThresholdHC.ShiftedPower.WorkKernel

noncomputable section
open MeasureTheory Real Set
open scoped ENNReal
namespace ThresholdHC.ShiftedPower
open ThresholdHC.Tier6 ThresholdHC.Tier2 ThresholdHC.BlindUpper ThresholdHC.EntropyTailExecution
open ThresholdHC.ObservableSimulation ThresholdHC.RareAboveTwo ThresholdHC.CriticalUpper

def classifierCall (k : ℕ) : FiniteCall where
  cost := classifierStop k
  value := classifierValue k
  measurable_cost := measurable_classifierStop k
  measurable_value := measurable_classifierValue k
  positive := classifierStop_pos k
  prefix_ext := fun _ _ h => classifier_prefix_ext k _ _ h

theorem classifierCall_binary (k : ℕ) (ω : ℕ → Bool) :
    (classifierCall k).value ω = 0 ∨ (classifierCall k).value ω = 1 :=
  Tier2.Model.decision_zero_or_one (fun j => ThresholdHC.Uniform713.dyadicMean observations j ω) k

theorem classifierCall_cap (k : ℕ) (ω : ℕ → Bool) : ((classifierCall k).cost ω:ℝ) ≤ (2:ℝ)^k := by
  exact_mod_cast classifierStop_le k ω

private theorem gapParameter_coin (d : Gap) (S : Bool) :
    gapParameter S d = coinParameter d S d.property.1 d.property.2 := by
  apply Subtype.ext
  cases S <;> rfl

def errorKernel (k : ℕ) (d : Gap) : ℝ := min 1 ((((2:ℝ)^k*(d:ℝ)^2)⁻¹)^2)

theorem classifierCall_error (k : ℕ) (d : Gap) (S : Bool) :
    (tapeMeasure (gapParameter S d)).real {ω | (classifierCall k).value ω ≠ bit S} ≤ errorKernel k d := by
  rw [gapParameter_coin]
  have h := ThresholdHC.Proofs.lemma6_error k d S d.property.1 d.property.2
  rw [errProbK_eq_measure] at h
  exact h

theorem classifierCall_bias (k : ℕ) (d : Gap) (S : Bool) :
    |(∫ ω, (classifierCall k).value ω ∂tapeMeasure (gapParameter S d))-bit S| ≤ errorKernel k d :=
  (binary_mean_error _ _ (measurable_classifierValue k) (classifierCall_binary k) S).trans (classifierCall_error k d S)

theorem classifierCall_work (k : ℕ) (d : Gap) (S : Bool) :
    (∫ ω, ((classifierCall k).cost ω:ℝ) ∂tapeMeasure (gapParameter S d)) ≤
      17*ThresholdHC.Uniform713.workEnvelope k d := by
  rw [gapParameter_coin]
  have h := ThresholdHC.Proofs.lemma6_work k d S d.property.1 d.property.2
  rw [workK_eq_integral] at h
  simpa only [classifierCall,classifierStop,Tier2.Model.work,mN,ThresholdHC.Uniform713.workEnvelope,
    ThresholdHC.Uniform713.cap,Nat.cast_pow,Nat.cast_ofNat] using h

theorem classifierCall_difference (k l : ℕ) (d : Gap) (S : Bool) :
    (∫ ω, ((classifierCall k).value ω-(classifierCall l).value ω)^2 ∂tapeMeasure (gapParameter S d)) ≤
      errorKernel k d+errorKernel l d := by
  have h := Tier2.Model.squared_decision_difference_le_errors (μ := tapeMeasure (gapParameter S d))
    (m := fun j ω => ThresholdHC.Uniform713.dyadicMean observations j ω)
    (fun j => ThresholdHC.Uniform713.measurable_prefixMean Tier2.measurable_observations (2^j)) k l (bit S)
  exact h.trans (add_le_add (classifierCall_error k d S) (classifierCall_error l d S))

end ThresholdHC.ShiftedPower
