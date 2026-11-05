import ThresholdHC.ConfidenceLocalization.CommonPair
import ThresholdHC.ConfidenceTransfer.CommonPairRate

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.ConfidenceLocalization
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.CriticalEntropy
open ThresholdHC.ObservableSimulation ThresholdHC.ConfidenceTransfer

/-- The common-pair premise follows from the actual variance/null-work
obstruction, uniformly over all capped local policies and auxiliary seeds. -/
theorem common_pair_bound {μ : Measure Gap} [IsProbabilityMeasure μ]
    {ρ b J : ℝ} (hρ : 0 < ρ) (hρ' : ρ ≤ 1/4) (hJ : 0 < J)
    (hobs : NullVarianceObstruction μ (gapParameter false) (gapParameter true) ρ b J) :
    CommonPairBound μ ρ b J := by
  intro δ hδ hδb
  let c : unitInterval := ⟨ρ,hρ.le,by linarith⟩
  obtain ⟨u,v,hu,hv,hsep,hlocal⟩ := common_pair_of_obstruction μ
    (gapParameter false) (gapParameter true) (measurable_gapParameter false) (measurable_gapParameter true)
    c hρ hρ' hJ hδ hδb hobs
  let q : SignLaw := ⟨fun d => (u d : ℝ),measurable_subtype_coe.comp hu.1,fun d => (u d).property⟩
  let r : SignLaw := ⟨fun d => (v d : ℝ),measurable_subtype_coe.comp hv.1,fun d => (v d).property⟩
  refine ⟨q,r,hu.2.2,hv.2.2,hu.2.1,hv.2.1,hsep,?_⟩
  have heq : signUnit q = u := by funext d; apply Subtype.ext; rfl
  have her : signUnit r = v := by funext d; apply Subtype.ext; rfl
  intro R E _ _ ν _ A n hn
  rw [heq,her]
  exact hlocal ν A n hn

/-- The 1/128 confidence lower bound now uses the variance/null-work
obstruction directly, with the policy-uniform pair constructed internally. -/
theorem confidence_rate_of_obstruction {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    {ρ b J B ε δ : ℝ} (hρ : 0 < ρ) (hρ' : ρ ≤ 1/4)
    (hb : 0 < b) (hJ : 0 < J) (hB : 0 < B) (hδ : 0 < δ) (hδ' : δ ≤ 1/4)
    (hobs : NullVarianceObstruction μ (gapParameter false) (gapParameter true) ρ b J)
    (hw : RareBudget μ A ρ B)
    (hconf : ∀ q : SignLaw, RarePrior μ ρ q →
      ThresholdHC.Confidence.failureProbability μ A q ε ≤ ENNReal.ofReal δ) :
    min b (Real.sqrt (J*Real.log (1/δ)/B))/128 ≤ ε :=
  confidence_rate_of_common_pair μ A hb hJ hB hδ hδ' (common_pair_bound hρ hρ' hJ hobs) hw hconf

theorem minimax_confidence_of_obstruction (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ b J B δ : ℝ} (hρ : 0 < ρ) (hρ' : ρ ≤ 1/4)
    (hb : 0 < b) (hJ : 0 < J) (hB : 0 < B) (hδ : 0 < δ) (hδ' : δ ≤ 1/4)
    (hobs : NullVarianceObstruction μ (gapParameter false) (gapParameter true) ρ b J) :
    ENNReal.ofReal (min b (Real.sqrt (J*Real.log (1/δ)/B))/128) ≤
      rareConfidenceRadius μ ρ B δ :=
  minimax_confidence_rate_of_common_pair μ hb hJ hB hδ hδ' (common_pair_bound hρ hρ' hJ hobs)

end ThresholdHC.ConfidenceLocalization
