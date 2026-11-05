import ThresholdHC.RMSLocalization.Terminal
import ThresholdHC.RMSLocalization.Testing

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.RMSLocalization
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.CriticalEntropy ThresholdHC.RareAboveTwo
open ThresholdHC.ObservableSimulation ThresholdHC.ConfidenceTransfer

theorem pair_rms_risk {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q r : SignLaw)
    {ρ B κ δ : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B) (hκ : 0 ≤ κ)
    (hq : RarePrior μ ρ q) (hr : RarePrior μ ρ r)
    (hqhalf : ∀ d, q.val d ≤ 1/2) (hrhalf : ∀ d, r.val d ≤ 1/2)
    (hloc : LocalNullWorkBound μ (gapParameter false) (gapParameter true) (signUnit q) (signUnit r) κ)
    (hw : RareBudget μ A ρ B) (hinfo : 2*κ*B ≤ 1/10)
    (hsep : δ ≤ signMean μ r.val-signMean μ q.val) :
    ENNReal.ofReal (δ/4) ≤ rareRisk μ A ρ := by
  let a := signMean μ q.val
  let b := signMean μ r.val
  let d := thresholdDecision A.output ((a+b)/2)
  have hd : Measurable d := measurable_thresholdDecision A.output A.output_measurable _
  have hm : RarePrior μ ρ (ThresholdHC.StoppingProgram.midpointPrior q r) :=
    ThresholdHC.StoppingProgram.mixPrior_rare μ q r hq hr (1/2) (by norm_num)
  have h := (terminal_null_hellinger μ A q r hqhalf hrhalf κ B hκ hB hloc
    ((hw q hq).trans_lt ENNReal.ofReal_lt_top) ((hw r hr).trans_lt ENNReal.ofReal_lt_top)
    (hw _ hm) d hd).trans hinfo
  have haff : (9/10 : ℝ) ≤ (hellingerAffinity
      ((experimentLaw μ A q).map (thresholdDecision (populationOutput A) ((a+b)/2)))
      ((experimentLaw μ A r).map (thresholdDecision (populationOutput A) ((a+b)/2)))).toReal := by
    change (9/10 : ℝ) ≤ (hellingerAffinity (observableDecisionLaw μ A q d)
      (observableDecisionLaw μ A r d)).toReal
    linarith
  have hf : Measurable (populationOutput A) :=
    A.output_measurable.comp (measurable_fst.fst.prodMk measurable_snd)
  have hab : a < b := by change δ ≤ b-a at hsep; linarith
  have hs := squared_risk_lower_of_affinity (experimentLaw μ A q) (experimentLaw μ A r)
    (populationOutput A) a b hf hab haff
  have hR := rms_pair_lower (experimentLaw μ A q) (experimentLaw μ A r)
    (populationOutput A) a b δ hδ.le hsep hs
  exact hR.trans (max_le (le_iSup_of_le q (le_iSup_of_le hq le_rfl))
    (le_iSup_of_le r (le_iSup_of_le hr le_rfl)))

end ThresholdHC.RMSLocalization
