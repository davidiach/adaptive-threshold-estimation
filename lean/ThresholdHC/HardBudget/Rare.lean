import ThresholdHC.HardBudget.SelectionScale
import ThresholdHC.HardBudget.RareModel

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.HardBudget
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.EntropyTail ThresholdHC.StoppingProgram


/-- A known law supplies an expected-budget base rule with strict slack over the minimax infimum. -/
theorem rare_base (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ b : ℝ}
    (hr : 0 < ρ) (hu : ρ ≤ 1/4) (hb : 0 < b) :
    ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R),
      RareBudget μ A ρ b ∧ rareRisk μ A ρ ≤ ENNReal.ofReal (28001*(selection μ ρ b).toReal) := by
  have hupper := entropy_tail_upper_explicit μ hr hu hb
  have hfloor := bernoulli_label_minimax_floor μ ρ b hr hu hb
  have hmin : 0 < min ρ (Real.sqrt (ρ/b)) := lt_min hr (Real.sqrt_pos.mpr (div_pos hr hb))
  have hp : 0 < rareMinimaxRisk μ ρ b := (ENNReal.ofReal_pos.mpr (mul_pos (by norm_num) hmin)).trans_le hfloor
  have hk : selection μ ρ b ≠ 0 := by
    intro h; rw [h,mul_zero] at hupper; exact hp.not_ge hupper
  have hk' := ENNReal.toReal_pos hk (finite_selection μ ρ b)
  have hstrict : rareMinimaxRisk μ ρ b < ENNReal.ofReal (28001*(selection μ ρ b).toReal) := by
    apply hupper.trans_lt
    rw [← ENNReal.ofReal_toReal (finite_selection μ ρ b),← ENNReal.ofReal_mul (by norm_num : 0 ≤ (28000:ℝ))]
    rw [ENNReal.toReal_ofReal hk'.le]
    apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mpr
    linarith
  obtain ⟨t,⟨R,mR,A,hA,rfl⟩,ht⟩ := sInf_lt_iff.mp hstrict
  exact ⟨R,mR,A,hA,ht.le⟩

theorem rare_hard_family (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ}
    (hr : 0 < ρ) (hu : ρ ≤ 1/4) :
    ∃ (R : Type) (_ : MeasurableSpace R) (rule : ℝ → AdaptiveEstimator R), ∀ B : ℝ, 0 < B →
      PathwiseCap (rule B) ⌊B⌋₊ ∧ rareRisk μ (rule B) ρ ≤ 160000*selection μ ρ B := by
  classical
  have hb (j : ℕ) : 0 < (stageAllowance j:ℝ) := by dsimp [stageAllowance]; positivity
  choose R mR base hbudget hrisk using fun j => rare_base μ hr hu (hb j)
  let (j : ℕ) := mR j
  obtain ⟨rule,hcap,hfamily⟩ := rms_family base ρ hr.le
  refine ⟨(∀ j, R j),inferInstance,rule,?_⟩
  intro B hB
  refine ⟨hcap _ hB.le,?_⟩
  have he : ENNReal.ofReal (160000*(selection μ ρ B).toReal) = 160000*selection μ ρ B := by
    rw [ENNReal.ofReal_mul (by norm_num : 0 ≤ (160000:ℝ)),ENNReal.ofReal_toReal (finite_selection _ _ _)]
    norm_num
  rw [← he]
  apply iSup_le; intro q; apply iSup_le; intro hq
  apply hfamily B hB μ q 28001 160000 (fun b => (selection μ ρ b).toReal) hq
    (by norm_num) (by norm_num) (by norm_num)
  · exact fun _ _ => ENNReal.toReal_nonneg
  · intro b hb hu'; rw [selection_saturates μ hr (by linarith) hb hu',ENNReal.toReal_ofReal hr.le]
  · intro b b' hb hbb
    have hs := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (finite_selection μ ρ b'))
      (selection_budget_scale μ ρ (by linarith : 0 < b) hbb)
    rwa [ENNReal.toReal_mul,ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at hs
  · intro j
    refine ⟨by simpa only [ENNReal.ofReal_natCast] using hbudget j q hq,?_⟩
    exact (rms_le_rare μ (base j) ρ q hq).trans (hrisk j)

theorem rare_hard_minimax (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B : ℝ}
    (hr : 0 < ρ) (hu : ρ ≤ 1/4) (hb : 0 < B) :
    ENNReal.ofReal ((10:ℝ)⁻¹^17)*selection μ ρ B ≤ hardRareMinimaxRisk μ ρ B ∧
      hardRareMinimaxRisk μ ρ B ≤ 160000*selection μ ρ B := by
  obtain ⟨R,mR,rule,hrule⟩ := rare_hard_family μ hr hu
  constructor
  · apply le_sInf; rintro t ⟨S,mS,A,hA,rfl⟩
    exact ThresholdHC.EntropyTailSharp.estimator_entropy_tail_lower μ hr hu hb A
      (fun q _ => pathwise_expected μ A q hb.le hA)
  · apply le_trans _ (hrule B hb).2
    apply sInf_le
    exact ⟨R,mR,rule B,(hrule B hb).1,rfl⟩

end ThresholdHC.HardBudget
