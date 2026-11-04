import ThresholdHC.ConfidenceProgram.Lower
noncomputable section
open MeasureTheory InformationTheory ThresholdHC.Tier6 ThresholdHC.RareAboveTwo
open ThresholdHC.ObservableSimulation ThresholdHC.ConfidenceTransfer
open scoped ENNReal
example {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (q r : SignLaw) {κ B : ℝ} (hκ : 0 ≤ κ) (hB : 0 ≤ B)
    (h : LocalReferenceWorkBound μ (gapParameter false) (gapParameter true) (signUnit q) (signUnit r) κ)
    (hw : expectedWork μ A (smoothedSign q r) ≤ ENNReal.ofReal B)
    (hw' : expectedWork μ A (smoothedSign r q) < ∞) :
    klDiv (observableDecisionLaw μ A (smoothedSign q r) id) (observableDecisionLaw μ A (smoothedSign r q) id) ≤
      ENNReal.ofReal ((8/3)*κ*B) := stopped_reference_work_kl μ A q r κ B hκ hB h hw hw'
open ThresholdHC.ConfidenceProgram ThresholdHC.Genie
example (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B δ : ℝ}
    (hr : 0 < ρ) (hu : ρ ≤ 1/2) (hb : 0 < B) (hd : 0 < δ) (hd' : δ ≤ 1/4) :
    infiniteProgramValue μ ρ (B/Real.log (1/δ))/30 ≤ rareConfidenceRadius μ ρ B δ :=
  stopping_confidence_lower μ hr hu hb hd hd'
example (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B δ : ℝ}
    (hr : 0 < ρ) (hu : ρ ≤ 1/4) (hb : 0 < B) (hd : 0 < δ) (hd' : δ ≤ 1/4) :
    (ENNReal.ofReal ((10:ℝ)⁻¹^17)*ThresholdHC.EntropyTail.selection μ ρ (B/Real.log (1/δ)))/30 ≤
      rareConfidenceRadius μ ρ B δ := entropy_tail_confidence_lower μ hr hu hb hd hd'
#print axioms ThresholdHC.ConfidenceProgram.entropy_tail_confidence_lower
#print axioms ThresholdHC.ConfidenceProgram.midpoint_reference_bound
#print axioms ThresholdHC.ConfidenceProgram.quartet_confidence
#print axioms ThresholdHC.ConfidenceProgram.stopping_confidence_lower
#print axioms ThresholdHC.ConfidenceTransfer.creation_null_work_kl
#print axioms ThresholdHC.ConfidenceTransfer.creation_reference_work_kl
#print axioms ThresholdHC.ConfidenceTransfer.finite_null_work_kl
#print axioms ThresholdHC.ConfidenceTransfer.finite_reference_work_kl
#print axioms ThresholdHC.ConfidenceTransfer.local_reference_of_null
#print axioms ThresholdHC.ConfidenceTransfer.observable_null_work_kl
#print axioms ThresholdHC.ConfidenceTransfer.observable_reference_work_kl
#print axioms ThresholdHC.ConfidenceTransfer.pair_confidence_work
#print axioms ThresholdHC.ConfidenceTransfer.pair_reference_confidence_work
#print axioms ThresholdHC.ConfidenceTransfer.stopped_null_work_kl
#print axioms ThresholdHC.ConfidenceTransfer.stopped_reference_work_kl
