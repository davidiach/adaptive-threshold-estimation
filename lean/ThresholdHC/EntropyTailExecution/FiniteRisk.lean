import ThresholdHC.EntropyTailExecution.ScheduledFamily
import ThresholdHC.EntropyTailExecution.AllocatedEstimator

/-! A finite terminal level gives an actual expected-budget minimax bound.
No component label or sign is observed by the estimator. -/

noncomputable section
open MeasureTheory Set Real
open scoped ENNReal BigOperators

namespace ThresholdHC.EntropyTailExecution
open ThresholdHC.Tier6 ThresholdHC.EntropyTailQuantile ThresholdHC.EntropyTailUpper
open ThresholdHC.EntropyTailAssembly ThresholdHC.ObservableSimulation ThresholdHC.RareAboveTwo

theorem finite_level_minimax (σ τ ζ : Measure Gap)
    [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)]
    {t ρ B : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ))
    (hN : bandEdge N < t) (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4) (hB : 0 < B)
    (hm : ρ/128 < (σ+τ).real univ) (J : ℕ) (hzJ : ζ.real univ ≤ levelAccuracy ρ J/8) :
    rareMinimaxRisk (σ+τ+ζ) ρ B ≤ ENNReal.ofReal (levelAccuracy ρ J+
      28000*(sqrt (ρ*costEntropy (fun j : Fin N => bandCost σ j.val))+
        (∫ d : Gap, (d:ℝ)⁻¹ ∂τ))/sqrt B) := by
  let μ := σ+τ+ζ
  let Γ := costEntropy (fun j : Fin N => bandCost σ j.val)
  let C := levelWorkCertificate σ τ ρ Γ (ζ.real univ) hρ
  let A := bankFamily μ (σ+τ) (referenceWeights σ) (referenceWeights_probability σ ht hs hN) hρ hρ1
  let K := bankFamilyCap (σ+τ) hρ
  let D : Fin (J+1) → FiniteCall := fun i => incrementCall A i.val
  let v : Fin (J+1) → ℝ := fun i => 17*levelAccuracy ρ i.val
  let c : Fin (J+1) → ℝ := fun i => adjacentCost C i.val
  have hK : ∀ l ω, ((A l).cost ω:ℝ) ≤ K l := bankFamily_cost_bound μ (σ+τ) _ _ hρ hρ1
  have hbin : ∀ l ω, (A l).value ω = 0 ∨ (A l).value ω = 1 := bankFamily_binary μ (σ+τ) _ _ hρ hρ1
  have hz : ζ.real univ ≤ ρ := by
    have h := levelAccuracy_le_first hρ.le J
    linarith
  have hwork : ∀ (q : SignLaw), RarePrior μ ρ q → ∀ l,
      (∫ ω, ((A l).cost ω:ℝ) ∂originalPopulationTapeLaw μ q) ≤ C l := by
    intro q hq l
    exact bankFamily_work σ τ ζ ht hs hN hτ hρ hρ1 hz q hq l
  have hCpos : ∀ l, 0 < C l := by
    intro l
    have hq : RarePrior μ ρ allNegativeSignLaw := by
      change (∫ d, (0:ℝ) ∂μ) ≤ ρ
      simpa using hρ.le
    have h := (call_cost_mean_ge_one (originalPopulationTapeLaw μ allNegativeSignLaw)
      (A l) (hK l)).trans (hwork allNegativeSignLaw hq l)
    linarith
  have hc : ∀ i, 0 < c i := by
    intro i
    dsimp only [c]
    unfold adjacentCost
    split_ifs
    · exact hCpos i.val
    · exact add_pos (hCpos i.val) (hCpos (i.val-1))
  have hv : ∀ i, 0 < v i := fun i => mul_pos (by norm_num) (levelAccuracy_pos hρ i.val)
  have hD : ∀ i ω, ((D i).cost ω:ℝ) ≤ adjacentCost K i.val :=
    fun i => incrementCall_cost_bound A K hK i.val
  have hU : ∀ i ω, ‖(D i).value ω‖ ≤ (1:ℝ) := fun i => incrementCall_bounded A hbin i.val
  have hb : RareBudget μ (allocatedEstimator B v c D) ρ B := by
    intro q hq
    exact allocated_work_bound hB hv hc D hD μ q
      (fun i => incrementCall_work_bound (originalPopulationTapeLaw μ q) A K C hK (hwork q hq) i.val)
  have hAΓ : (∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ) ≤ Γ := by
    rw [inverseSquare_eq_band_total σ hs hN]
    exact costTotal_le_costEntropy (fun j => bandCost_nonneg σ j.val)
  have hcert : allocationCertificate v c ≤
      28000*(sqrt (ρ*Γ)+(∫ d : Gap, (d:ℝ)⁻¹ ∂τ)) := by
    have h := multilevel_budget_certificate σ τ (inverseSquare_integrable_of_support σ ht hs) hτ
      hρ (costEntropy_nonneg (fun j : Fin N => bandCost_nonneg σ j.val))
      (measureReal_nonneg) hAΓ hm J hzJ
    change (∑ i : Fin (J+1), (fun l : ℕ => sqrt (17*levelAccuracy ρ l*adjacentCost C l)) i.val) ≤ _
    rw [Fin.sum_univ_eq_sum_range (fun l : ℕ => sqrt (17*levelAccuracy ρ l*adjacentCost C l)) (J+1)]
    exact h
  apply (show rareMinimaxRisk μ ρ B ≤ rareRisk μ (allocatedEstimator B v c D) ρ from
    sInf_le ⟨Fin (J+1) → ℕ, inferInstance, allocatedEstimator B v c D, hb, rfl⟩).trans
  apply iSup_le
  intro q
  apply iSup_le
  intro hq
  have hV : ∀ i, (∫ ω, ((D i).value ω)^2 ∂originalPopulationTapeLaw μ q) ≤ v i := by
    intro i
    exact bankFamily_second μ (σ+τ) ζ rfl _ _ hρ hρ1 q hq i.val
      (hzJ.trans (div_le_div_of_nonneg_right (levelAccuracy_antitone hρ.le (by omega)) (by norm_num)))
  have hbias : |(∑ i, ∫ ω, (D i).value ω ∂originalPopulationTapeLaw μ q)-signMean μ q.val|
      ≤ levelAccuracy ρ J := by
    rw [incrementCall_mean_sum _ A hbin J]
    exact bankFamily_bias μ (σ+τ) ζ rfl _ _ hρ hρ1 q hq J hzJ
  exact (allocated_rootRisk_bound hB hv hc D (fun _ => by norm_num) hU μ q _ hV
    (levelAccuracy_pos hρ J).le hbias).trans
    (ENNReal.ofReal_le_ofReal (add_le_add (le_refl _) (div_le_div_of_nonneg_right hcert (sqrt_nonneg B))))

end ThresholdHC.EntropyTailExecution
