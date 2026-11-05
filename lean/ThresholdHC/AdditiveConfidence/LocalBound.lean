import ThresholdHC.AdditiveConfidence.StatisticMass
import ThresholdHC.AdditiveConfidence.WorkMixture
import ThresholdHC.AdditiveConfidence.FiniteMixture

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace ThresholdHC.AdditiveConfidence
open ThresholdHC.Tier6 ThresholdHC.CriticalEntropy ThresholdHC.ObservableSimulation
open ThresholdHC.ConfidenceLocalization ThresholdHC.ConfidenceTransfer

theorem GapMixture.local_bound {I : Type} [Fintype I] {μ : Measure Gap} [IsProbabilityMeasure μ]
    (M : GapMixture I μ) (p₀ p₁ : Gap → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (q r : I → SignLaw) (hq : ∀ i d, (q i).val d ≤ 1/2) (hr : ∀ i d, (r i).val d ≤ 1/2)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hloc : ∀ i, LocalNullWorkBound (M.law i) p₀ p₁ (signUnit (q i)) (signUnit (r i)) κ) :
    LocalNullWorkBound μ p₀ p₁ (signUnit (M.mixedSign q)) (signUnit (M.mixedSign r)) κ := by
  intro R E _ _ ν _ A n hcap
  let P := fun i z => (cappedStatisticLaw (M.law i) ν p₀ p₁ (signUnit (q i)) A n).real {z}
  let Q := fun i z => (cappedStatisticLaw (M.law i) ν p₀ p₁ (signUnit (r i)) A n).real {z}
  let res := fun z => (tapeStatisticLaw ν (M.residual.map p₀) A n).real {z}
  have hmix := finite_mixture_loss (fun i => (M.weight i : ℝ)) (fun i => (M.weight i).property)
    P Q (fun _ _ => measureReal_nonneg) (fun _ _ => measureReal_nonneg) res
    (fun _ => measureReal_nonneg) (M.statistic_mass_balance ν p₀ h₀ A n)
  rw [capped_affinity_real μ ν p₀ p₁ _ _ h₀ h₁ (measurable_signUnit _) (measurable_signUnit _) A n hcap]
  simp_rw [M.statistic_mass ν p₀ p₁ h₀ h₁ q hq A n,M.statistic_mass ν p₀ p₁ h₀ h₁ r hr A n]
  apply hmix.trans
  calc
    _ ≤ ∑ i, (M.weight i : ℝ)*(κ*(populationExpectedWork (M.law i) ν p₀ p₁ (fun _ => 0) A).toReal) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (M.weight i).property
      have h := hloc i ν A n hcap
      rw [capped_affinity_real (M.law i) ν p₀ p₁ _ _ h₀ h₁
        (measurable_signUnit _) (measurable_signUnit _) A n hcap] at h
      exact h
    _ = κ*∑ i, (M.weight i : ℝ)*(populationExpectedWork (M.law i) ν p₀ p₁ (fun _ => 0) A).toReal := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (M.component_work_le ν p₀ p₁ (fun _ => 0) A n hcap) hκ

end ThresholdHC.AdditiveConfidence
