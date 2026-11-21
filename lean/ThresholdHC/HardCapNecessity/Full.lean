import ThresholdHC.HardCapNecessity.Controllers
import ThresholdHC.HardBudget.Full

/-! The hard-cap counterexamples. The independent controller is the one of
`HardBudget.observable_fallback`, fed the base family; the shared-seed
controller runs `HardBudget.estimator` on the constant seed array; the single
fallback is one capped run with the midpoint on timeout. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.HardCapNecessity
open ThresholdHC.Tier6 ThresholdHC.ObservableSimulation ThresholdHC.HardBudget

theorem rare_rate : RareRateStatement := rare_rate_holds

theorem hard_cap_necessity : HardCapNecessityStatement := by
  obtain ⟨ctrl, hctrl⟩ := observable_fallback (fun _ => Bool × Unit) capBase (1/4) (by norm_num)
  refine ⟨Bool × Unit, inferInstance, capBase, capBase_seed_zero, capBase_premise, ⟨ctrl, ?_⟩,
    ⟨fun B => sharedController capBase (1/4) (stageCount B), ?_⟩, ladder_floor, ?_⟩
  · intro B hB
    obtain ⟨h1, h2, -, h4, h5⟩ := hctrl B hB
    refine ⟨h1, h2, h4, ?_⟩
    intro hB4 q hq
    have h := h5 (Measure.dirac halfGap) q 1 rareRate hB4 (signMean_bounds _ q).1 hq (by norm_num)
      (fun b _ => rate_nonneg b) rate_half (fun _ _ hb hbb => rate_scale hb hbb)
      (fun j => capBase_premise q hq j)
    rwa [one_pow, mul_one] at h
  · intro B hB
    refine ⟨rfl, ?_, ?_, ?_⟩
    · intro r x hx
      exact (shared_cap capBase (1/4) (stageCount B) r x hx).trans (Nat.cast_le.mpr (paid_fits B))
    · intro hsmall r s
      rw [shared_output, count_zero_of_small hB hsmall]
      change (1/4 : ℝ)/2 = 1/8
      norm_num
    · intro m hlo hhi r s
      rw [shared_output, count_at_checkpoint hB m hlo hhi]
  · intro j hj
    refine ⟨⟨singleFallback (capBase j) (1/4) (stageCap j), rfl, single_cap _ _ _, fun r s => ?_⟩,
      single_floor j hj⟩
    rw [single_output]
    norm_num

end ThresholdHC.HardCapNecessity
