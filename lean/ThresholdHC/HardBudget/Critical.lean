import ThresholdHC.HardBudget.BudgetScale
import ThresholdHC.HardBudget.CriticalTransport
import ThresholdHC.HardBudget.RareModel
import ThresholdHC.CriticalEntropy.CriticalMinimax

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.HardBudget
open ThresholdHC.Tier6 ThresholdHC.CriticalEntropy ThresholdHC.CriticalUpper
open ThresholdHC.ConfidenceTransfer ThresholdHC.RareAboveTwo

def criticalRate (ρ B : ℝ) : ℝ := min ρ (Real.sqrt (ρ*criticalLogFactor ρ/B))

theorem critical_rate_small {ρ B : ℝ} (hr : 0 < ρ) (hu : ρ ≤ 1/4) (hb : 0 < B) (hb' : B < 4) :
    criticalRate ρ B = ρ := by
  have h₁ := Real.log_nonneg ((one_le_div hr).2 (by linarith : ρ ≤ 1))
  have h₂ := Real.log_nonneg (show 1 ≤ 1+Real.log (1/ρ) by linarith)
  have hf : 1 ≤ criticalLogFactor ρ := by
    unfold criticalLogFactor; nlinarith [mul_nonneg h₁ h₂]
  apply min_eq_left
  apply Real.le_sqrt_of_sq_le
  apply (le_div_iff₀ hb).2
  have hρB : ρ*B ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_left hb'.le hr.le]
  nlinarith [mul_le_mul_of_nonneg_left hρB hr.le,mul_le_mul_of_nonneg_left hf hr.le]

theorem critical_rate_scale {ρ b B : ℝ} (hr : 0 < ρ) (hu : ρ ≤ 1/4) (hb : 0 < b) (hB : b ≤ B) :
    criticalRate ρ b ≤ Real.sqrt (B/b)*criticalRate ρ B := by
  obtain ⟨ha,he⟩ := budget_scale hb hB
  have hpos := (mul_pos hr (criticalLogFactor_pos ρ hr (by linarith))).le
  have hroot : Real.sqrt (ρ*criticalLogFactor ρ/b) = Real.sqrt (B/b)*Real.sqrt (ρ*criticalLogFactor ρ/B) := by
    rw [Real.sqrt_div hpos,Real.sqrt_div hpos]
    calc _ = Real.sqrt (ρ*criticalLogFactor ρ)*(1/Real.sqrt b) := by ring
         _ = _ := by rw [he]; ring
  unfold criticalRate
  by_cases hl : ρ ≤ Real.sqrt (ρ*criticalLogFactor ρ/B)
  · rw [min_eq_left hl]
    exact (min_le_left _ _).trans (by nlinarith [mul_le_mul_of_nonneg_right ha hr.le])
  · rw [min_eq_right (le_of_not_ge hl)]
    exact (min_le_right _ _).trans_eq hroot

theorem critical_hard_family {ρ : ℝ} (hr : 0 < ρ) (hu : ρ ≤ 1/4) :
    ∃ rule : ℝ → AdaptiveEstimator (ℕ → CriticalSeed), (∀ B : ℝ, 0 ≤ B → PathwiseCap (rule B) ⌊B⌋₊) ∧
      ∀ B : ℝ, 0 < B → rareRisk criticalPositiveLaw (rule B) ρ ≤ ENNReal.ofReal (570000*criticalRate ρ B) := by
  let base (j : ℕ) := criticalBudgetEstimator ρ (stageAllowance j)
  obtain ⟨rule,hcap,hfam⟩ := rms_family base ρ hr.le
  refine ⟨rule,hcap,?_⟩
  intro B hB
  apply iSup_le; intro q; apply iSup_le; intro hq
  apply hfam B hB criticalPositiveLaw q 100000 570000 (criticalRate ρ) hq (by norm_num) (by norm_num) (by norm_num)
  · exact fun b _ => le_min hr.le (Real.sqrt_nonneg _)
  · exact fun b hb hu' => critical_rate_small hr hu hb hu'
  · exact fun b b' hb hbb => critical_rate_scale hr hu (by linarith) hbb
  · intro j
    have hp : 0 < (stageAllowance j:ℝ) := by dsimp [stageAllowance]; positivity
    have hw := (critical_budget_equivalence (base j) ρ (stageAllowance j)).mp
      (criticalBudget_uniformBudget ρ hr (by linarith) _)
    have hR := criticalBudget_maximalRMSRisk ρ hr (by linarith) _ hp
    rw [critical_risk_equivalence] at hR
    refine ⟨by simpa only [ENNReal.ofReal_natCast] using hw q hq,?_⟩
    exact (rms_le_rare criticalPositiveLaw (base j) ρ q hq).trans hR

theorem critical_hard_minimax :
    ∃ c : ℝ, 0 < c ∧ ∀ {ρ B : ℝ}, 0 < ρ → ρ ≤ 1/4 → 0 < B →
      ENNReal.ofReal (c*criticalRate ρ B) ≤ hardRareMinimaxRisk criticalPositiveLaw ρ B ∧
        hardRareMinimaxRisk criticalPositiveLaw ρ B ≤ ENNReal.ofReal (570000*criticalRate ρ B) := by
  obtain ⟨c,hc,hlower⟩ := critical_algorithm_lower_bound
  refine ⟨c,hc,?_⟩
  intro ρ B hr hu hb
  obtain ⟨rule,hcap,hR⟩ := critical_hard_family hr hu
  constructor
  · apply le_sInf; rintro t ⟨R,mR,A,hA,rfl⟩
    let rho : unitInterval := ⟨ρ,hr.le,by linarith⟩
    let B' := max 1 B
    have hbudget : RareBudget criticalPositiveLaw A ρ B' := fun q _ =>
      (pathwise_expected _ A q hb.le hA).trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))
    have h := hlower rho hr hu B' (le_max_left _ _) R A ((critical_budget_equivalence _ _ _).mpr hbudget)
    rw [critical_risk_equivalence] at h
    change ENNReal.ofReal (c*criticalRate ρ B') ≤ _ at h
    by_cases hcase : 1 ≤ B
    · simpa only [B',max_eq_right hcase] using h
    · dsimp only [B'] at h
      rwa [max_eq_left (le_of_not_ge hcase),critical_rate_small hr hu (by norm_num) (by norm_num),
        ← critical_rate_small hr hu hb (by linarith)] at h
  · apply le_trans _ (hR B hb)
    apply sInf_le
    exact ⟨ℕ → CriticalSeed,inferInstance,rule B,hcap B hb.le,rfl⟩

end ThresholdHC.HardBudget
