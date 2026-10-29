import ThresholdHC.RareAboveTwo.PrefixInformation
import ThresholdHC.CriticalEntropy.CriticalAlgorithmLower

noncomputable section
namespace ThresholdHC.RareAboveTwo
open MeasureTheory ProbabilityTheory Set Filter ThresholdHC.Tier3 ThresholdHC.Tier4
open ThresholdHC.Tier6 ThresholdHC.CriticalEntropy
open scoped ENNReal Topology

theorem rare_lower_at_separation {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    (a ρ B δ : ℝ) (ha : a ≤ 1/2) (hsupp : ∀ᵐ d : Gap ∂μ, (d : ℝ) ≤ a)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4) (hB : 0 ≤ B) (hδ : 0 < δ) (hδρ : δ ≤ ρ/2)
    (hinfo : 64*δ^2*a^2*B ≤ ρ/8) (hbudget : RareBudget μ A ρ B) :
    ENNReal.ofReal (δ/8) ≤ rareRisk μ A ρ := by
  have hu : 0 ≤ ρ/2 ∧ ρ/2 ≤ 1 := by constructor <;> linarith
  have hv : 0 ≤ ρ/2+δ ∧ ρ/2+δ ≤ 1 := by constructor <;> linarith
  let q := flatSign (ρ/2) hu
  let r := flatSign (ρ/2+δ) hv
  have hq : RarePrior μ ρ q := by change signMean μ (flatSign _ _).val ≤ ρ; rw [flatSign_mean]; linarith
  have hr : RarePrior μ ρ r := by change signMean μ (flatSign _ _).val ≤ ρ; rw [flatSign_mean]; linarith
  have hqfin : expectedWork μ A q < ∞ := (hbudget q hq).trans_lt (by simp)
  have hrfin : expectedWork μ A r < ∞ := (hbudget r hr).trans_lt (by simp)
  let f := thresholdDecision A.output ((ρ/2+(ρ/2+δ))/2)
  have hf : Measurable f := measurable_thresholdDecision A.output A.output_measurable _
  have hpre (n : ℕ) :
      (1-(hellingerAffinity (observablePrefixLaw μ A q n) (observablePrefixLaw μ A r n)).toReal)*(ρ/2) ≤
        ρ/8 := by
    have h := rare_prefix_information μ A a ρ B (ρ/2) (ρ/2+δ) ha hsupp hρ1 hB
      (by linarith) (by linarith) (by linarith) hu hv hbudget n
    have he : ρ/2+δ-ρ/2=δ := by ring
    rw [he] at h
    exact h.trans hinfo
  have hi := observable_terminal_affinity_bound μ A q r hqfin hrfin f hf (ρ/2) (ρ/8)
    (by positivity) hpre
  have haff : (3/4 : ℝ) ≤ (hellingerAffinity (observableDecisionLaw μ A q f)
      (observableDecisionLaw μ A r f)).toReal := by nlinarith
  have hsq := two_point_risk_lower_of_decision_affinity
    (experimentLaw μ A q) (experimentLaw μ A r) (populationOutput A)
    (ρ/2) (ρ/2+δ) (measurable_populationOutput A) (by linarith) haff
  have hb := critical_rms_pair_lower (experimentLaw μ A q) (experimentLaw μ A r)
    (populationOutput A) (ρ/2) (ρ/2+δ) δ hδ.le (by linarith) hsq
  apply hb.trans
  apply max_le
  · have h : rootMeanRisk (experimentLaw μ A q) (populationOutput A) (signMean μ q.val) ≤ rareRisk μ A ρ :=
      le_iSup_of_le q (le_iSup_of_le hq le_rfl)
    simpa only [q,flatSign_mean] using h
  · have h : rootMeanRisk (experimentLaw μ A r) (populationOutput A) (signMean μ r.val) ≤ rareRisk μ A ρ :=
      le_iSup_of_le r (le_iSup_of_le hr le_rfl)
    simpa only [r,flatSign_mean] using h

end ThresholdHC.RareAboveTwo
