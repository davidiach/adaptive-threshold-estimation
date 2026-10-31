import ThresholdHC.Genie.CompactPriorDomain
import ThresholdHC.Genie.CompactDecreasingMaximum
import ThresholdHC.Genie.InfiniteDualLimit
import ThresholdHC.Genie.InfiniteComparison
import ThresholdHC.StoppingProgram.StrongDuality

/-! The exact four-prior dual of the infinite-cap program. Compactness uses
one common image of all count moments, so attainment survives the cap limit. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.Genie
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram

def infiniteDualValue (μ : Measure Gap) (ρ B : ℝ) : ℝ≥0∞ :=
  ⨆ (Q : FourPriors) (_ : Admissible μ ρ Q), infiniteDualRatio μ B Q

theorem infinite_weak_duality (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 < ρ) (hρhalf : ρ ≤ 1/2) (hB : 0 < B)
    (Q : FourPriors) (hQ : Admissible μ ρ Q) :
    infiniteDualRatio μ B Q ≤ infiniteProgramValue μ ρ B ^ 2 := by
  rw [infiniteDualRatio_eq_iInf,infiniteProgramValue_sq]
  apply iInf_mono
  intro N
  rw [(strong_four_prior_duality (N+1) μ hρ hρhalf hB).1]
  exact le_iSup_of_le Q (le_iSup_of_le hQ le_rfl)

theorem infinite_four_prior_duality (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 < ρ) (hρhalf : ρ ≤ 1/2) (hB : 0 < B) :
    infiniteProgramValue μ ρ B ^ 2 = infiniteDualValue μ ρ B ∧
      ∃ Q : FourPriors, Admissible μ ρ Q ∧
        infiniteDualRatio μ B Q = infiniteProgramValue μ ρ B ^ 2 := by
  letI : Nonempty (PriorDomain μ ρ) := priorDomain_nonempty μ hρ.le
  obtain ⟨x,hx⟩ := compact_decreasing_maximum
    (fun N : ℕ => fun x : PriorDomain μ ρ => dualRatio μ B (N+1) (domainPriors μ ρ x))
    (fun N => domain_dualRatio_upperSemicontinuous μ ρ B (N+1))
    (fun x n m hnm => dualRatio_antitone μ B (domainPriors μ ρ x) (by omega))
  have he : infiniteProgramValue μ ρ B ^ 2 =
      ⨅ N : ℕ, ⨆ y : PriorDomain μ ρ, dualRatio μ B (N+1) (domainPriors μ ρ y) := by
    rw [infiniteProgramValue_sq]
    apply iInf_congr
    intro N
    rw [(strong_four_prior_duality (N+1) μ hρ hρhalf hB).1,dualValue_eq_domain_sup]
  have hvalue : infiniteDualRatio μ B (domainPriors μ ρ x) = infiniteProgramValue μ ρ B ^ 2 := by
    rw [infiniteDualRatio_eq_iInf,he]
    exact hx.symm
  refine ⟨le_antisymm ?_ ?_,domainPriors μ ρ x,domainPriors_admissible μ ρ x,hvalue⟩
  · rw [←hvalue]
    exact le_iSup_of_le (domainPriors μ ρ x)
      (le_iSup_of_le (domainPriors_admissible μ ρ x) le_rfl)
  · apply iSup_le
    intro Q
    apply iSup_le
    exact infinite_weak_duality μ hρ hρhalf hB Q

theorem infinite_dual_positive_attained (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 < ρ) (hρquarter : ρ ≤ 1/4) (hB : 0 < B) :
    ∃ Q : FourPriors, Admissible μ ρ Q ∧
      infiniteDualRatio μ B Q = infiniteProgramValue μ ρ B ^ 2 ∧
      0 < infiniteProgramValue μ ρ B ^ 2 ∧ infiniteInformationRatio μ Q < ⊤ := by
  obtain ⟨Q,hQ,he⟩ := (infinite_four_prior_duality μ hρ (by linarith) hB).2
  have hp : 0 < infiniteProgramValue μ ρ B ^ 2 := by
    exact ENNReal.pow_pos (infinite_program_positive μ ρ B hρ hρquarter hB) 2
  refine ⟨Q,hQ,he,hp,lt_top_iff_ne_top.mpr ?_⟩
  intro htop
  have hb : ENNReal.ofReal B ≠ 0 := (ENNReal.ofReal_pos.mpr hB).ne'
  have hz : infiniteDualRatio μ B Q = 0 := by simp [infiniteDualRatio,htop,hb]
  rw [hz] at he
  exact hp.ne' he.symm

end ThresholdHC.Genie
