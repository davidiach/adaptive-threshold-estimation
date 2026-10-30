import Mathlib.Probability.CDF
import Mathlib.Tactic

/-! Quantile thresholds for right-continuous distribution functions. The
threshold includes a possible atom; continuity from the left is not assumed. -/

noncomputable section
open Set Filter
open scoped Topology

namespace ThresholdHC.EntropyTail

def levelThreshold (f : StieltjesFunction ℝ) (ρ : ℝ) : ℝ :=
  sInf {t : ℝ | ρ ≤ f t}

theorem stieltjes_threshold_properties (f : StieltjesFunction ℝ) {ρ a : ℝ}
    (hρ : 0 < ρ) (hf0 : f 0 = 0) (ha : ρ ≤ f a) :
    0 < levelThreshold f ρ ∧ levelThreshold f ρ ≤ a ∧
    ρ ≤ f (levelThreshold f ρ) ∧
    ∀ r < levelThreshold f ρ, f r < ρ := by
  let S : Set ℝ := {t | ρ ≤ f t}
  have hne : S.Nonempty := ⟨a, ha⟩
  have hb : BddBelow S := by
    refine ⟨0, ?_⟩
    intro x hx
    by_contra h
    have hfx := f.mono (le_of_lt (lt_of_not_ge h))
    rw [hf0] at hfx
    exact (not_le_of_gt hρ) (hx.trans hfx)
  have hattain : ρ ≤ f (levelThreshold f ρ) := by
    rw [← f.iInf_Ioi_eq (levelThreshold f ρ)]
    apply le_ciInf
    intro r
    obtain ⟨x, hx, hxr⟩ := exists_lt_of_csInf_lt hne r.property
    exact hx.trans (f.mono hxr.le)
  have ht : 0 < levelThreshold f ρ := by
    by_contra h
    have hfx := f.mono (le_of_not_gt h)
    rw [hf0] at hfx
    exact (not_le_of_gt hρ) (hattain.trans hfx)
  refine ⟨ht, csInf_le hb ha, hattain, ?_⟩
  intro r hr
  by_contra h
  have hs : r ∈ S := le_of_not_gt h
  exact (not_le_of_gt hr) (csInf_le hb hs)

end ThresholdHC.EntropyTail
