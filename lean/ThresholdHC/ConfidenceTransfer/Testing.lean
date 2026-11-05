import ThresholdHC.ConfidenceTransfer.Terminal
import ThresholdHC.Confidence.Lower

noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal
namespace ThresholdHC.ConfidenceTransfer
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.ObservableSimulation

/-- Uniform confidence at a radius below a quarter of the original pair's
separation requires logarithmic information, even with unbounded stopping. -/
theorem pair_reference_confidence_work {R : Type} [MeasurableSpace R] (μ : Measure Gap)
    [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q r : SignLaw)
    {ρ B κ ε δ : ℝ} (hB : 0 ≤ B) (hκ : 0 ≤ κ) (hδ : 0 < δ) (hδ' : δ ≤ 1/4)
    (hq : RarePrior μ ρ q) (hr : RarePrior μ ρ r)
    (hloc : LocalReferenceWorkBound μ (gapParameter false) (gapParameter true) (signUnit q) (signUnit r) κ)
    (hw : RareBudget μ A ρ B)
    (hconf : ∀ s : SignLaw, RarePrior μ ρ s →
      ThresholdHC.Confidence.failureProbability μ A s ε ≤ ENNReal.ofReal δ)
    (hsep : 4*ε < signMean μ q.val - signMean μ r.val) :
    Real.log (1/δ)/4 ≤ (8/3)*κ*B := by
  let s := smoothedSign q r
  let t := smoothedSign r q
  have hs := smoothedSign_rare μ q r hq hr
  have ht := smoothedSign_rare μ r q hr hq
  have hobs : Measurable (fun z : PopulationSeed R × ThresholdHC.Tier3.ProcessTape => (z.1.1,z.2)) :=
    measurable_fst.fst.prodMk measurable_snd
  let (b : SignLaw) : IsProbabilityMeasure (observableDecisionLaw μ A b id) :=
    (Measure.isProbabilityMeasure_map_iff hobs.aemeasurable).2 inferInstance
  have hf (b : SignLaw) (hb : RarePrior μ ρ b) :
      (observableDecisionLaw μ A b id) {z | ε < |A.output z - signMean μ b.val|} ≤ ENNReal.ofReal δ := by
    change ((experimentLaw μ A b).map (fun z => (z.1.1,z.2))) {z | ε < |A.output z - signMean μ b.val|} ≤ _
    rw [Measure.map_apply hobs (measurableSet_lt measurable_const
      ((A.output_measurable.sub_const _).abs))]
    exact hconf b hb
  have hsep' : 2*ε < signMean μ s.val-signMean μ t.val := by
    rw [smoothedSign_separation μ r q]
    linarith
  have htest := ThresholdHC.Confidence.confidence_testing_bound (observableDecisionLaw μ A s id)
    (observableDecisionLaw μ A t id) A.output A.output_measurable _ _ ε δ hδ hδ' hsep'
    (hf s hs) (hf t ht)
  have hu := stopped_reference_work_kl μ A q r κ B hκ hB hloc (hw s hs)
    ((hw t ht).trans_lt ENNReal.ofReal_lt_top)
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (mul_nonneg (by norm_num) hκ) hB)).mp (htest.trans hu)

theorem pair_confidence_work {R : Type} [MeasurableSpace R] (μ : Measure Gap)
    [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q r : SignLaw)
    {ρ B κ ε δ : ℝ} (hB : 0 ≤ B) (hκ : 0 ≤ κ) (hδ : 0 < δ) (hδ' : δ ≤ 1/4)
    (hq : RarePrior μ ρ q) (hr : RarePrior μ ρ r)
    (hqhalf : ∀ d, q.val d ≤ 1/2) (hrhalf : ∀ d, r.val d ≤ 1/2)
    (hloc : LocalNullWorkBound μ (gapParameter false) (gapParameter true) (signUnit q) (signUnit r) κ)
    (hw : RareBudget μ A ρ B)
    (hconf : ∀ s : SignLaw, RarePrior μ ρ s →
      ThresholdHC.Confidence.failureProbability μ A s ε ≤ ENNReal.ofReal δ)
    (hsep : 4*ε < signMean μ q.val - signMean μ r.val) :
    Real.log (1/δ)/4 ≤ (16/3)*κ*B := by
  have h := pair_reference_confidence_work μ A q r hB (by positivity : 0 ≤ 2*κ) hδ hδ' hq hr
    (local_reference_of_null μ _ _ _ _ (measurable_gapParameter false) (measurable_gapParameter true)
      (measurable_signUnit q) (measurable_signUnit r) hqhalf hrhalf hκ hloc) hw hconf hsep
  nlinarith only [h]

end ThresholdHC.ConfidenceTransfer
