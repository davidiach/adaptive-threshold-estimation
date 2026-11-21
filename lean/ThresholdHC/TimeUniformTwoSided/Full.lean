import ThresholdHC.TimeUniformTwoSided.Online
import ThresholdHC.TimeUniformTwoSided.Scale

/-! The time-uniform upper procedure in the original observable experiment, and
the two-sided order of the time-uniform half-width in that one model. -/
noncomputable section
namespace ThresholdHC.TimeUniformTwoSided
open MeasureTheory
open scoped ENNReal
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.AnytimeLower ThresholdHC.HardBudget

/-- The stage family of `ThresholdHC.Anytime.known_anytime`, run as one online
policy, has joint coverage and width control in the original experiment. The
envelope is `ρ/2` at budget `0` and `1500002 K(n/Λ(n,δ))` at every `n ≥ 1`. -/
theorem online_upper : OnlineUpperStatement := by
  intro μ _ ρ δ hr hu hd hd4
  obtain ⟨R,mR,base,-,hcov,-,hwidth⟩ := ThresholdHC.Anytime.known_anytime μ hr hu hd hd4
  let t : ℕ → ℝ := fun n => if n = 0 then ρ/2 else
    1500002*(ThresholdHC.EntropyTail.selection μ ρ
      ((n:ℝ)/ThresholdHC.Anytime.inflation (n:ℝ) δ)).toReal
  have hw (n : ℕ) (z : (∀ j, R j) × Table) :
      (ThresholdHC.Anytime.observedInterval base ρ (ThresholdHC.Anytime.radius μ ρ δ)
          (stageCount (n:ℝ)) z).2 -
        (ThresholdHC.Anytime.observedInterval base ρ (ThresholdHC.Anytime.radius μ ρ δ)
          (stageCount (n:ℝ)) z).1 ≤ 2*t n := by
    by_cases hn : n = 0
    · have h0 : stageCount (n:ℝ) = 0 := count_zero_of_small (by positivity)
        (by rw [hn,Nat.cast_zero]; norm_num)
      rw [h0,ThresholdHC.Anytime.observedInterval_eq]
      simp only [t,hn,ite_true]
      change ρ-0 ≤ 2*(ρ/2)
      linarith
    · have h := hwidth (n:ℝ) (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn) z
      simp only [t,hn,ite_false]
      unfold ThresholdHC.Anytime.halfWidth at h
      have hm := le_max_right 0
        ((ThresholdHC.Anytime.observedInterval base ρ (ThresholdHC.Anytime.radius μ ρ δ)
          (stageCount (n:ℝ)) z).2 -
        (ThresholdHC.Anytime.observedInterval base ρ (ThresholdHC.Anytime.radius μ ρ δ)
          (stageCount (n:ℝ)) z).1)
      linarith
  refine ⟨∀ j, R j,inferInstance,limitEstimator base,
    fun n y => (onlineInterval base ρ (ThresholdHC.Anytime.radius μ ρ δ) n y).1,
    fun n y => (onlineInterval base ρ (ThresholdHC.Anytime.radius μ ρ δ) n y).2,t,
    fun n => (measurable_onlineInterval base ρ _ n).fst,
    fun n => (measurable_onlineInterval base ρ _ n).snd,?_,
    online_coverage μ base ρ (ThresholdHC.Anytime.radius μ ρ δ) ρ hd.le t hcov hw,?_,?_⟩
  · intro n
    by_cases hn : n = 0
    · simp only [t,hn,ite_true]
      positivity
    · simp only [t,hn,ite_false]
      positivity
  · intro n hn
    simp only [t,show n ≠ 0 by omega,ite_false]
    exact le_refl _
  · intro n hn
    simp only [t,show n ≠ 0 by omega,ite_false]
    exact envelope_scale μ ρ hd hd4 hn

/-- Two-sided order of the time-uniform half-width in one model: the
constructed procedure, which has joint coverage and width control, has an
envelope at most `3000004 K(n/λ(n))` for `n ≥ 3` and at least
`10^{-22} K(n/λ(n))` at arbitrarily late budgets; and every procedure with
measurable endpoints and a nonnegative envelope satisfying
`OnlineIntervalCoverage` obeys the same lower bound. -/
theorem time_uniform_two_sided : TimeUniformTwoSidedStatement := by
  intro μ _ ρ δ hr hu hd hd4
  refine ⟨?_,fun R _ A L U hL hU t ht hc M =>
    law_dependent_interval_lower μ hr hu ⟨hd,hd4⟩ A L U hL hU t ht hc M⟩
  obtain ⟨R,mR,A,L,U,t,hL,hU,ht,hc,-,h3⟩ := online_upper μ ρ δ hr hu hd hd4
  exact ⟨R,mR,A,L,U,t,hL,hU,ht,hc,h3,
    fun M => law_dependent_interval_lower μ hr hu ⟨hd,hd4⟩ A L U hL hU t ht hc M⟩

end ThresholdHC.TimeUniformTwoSided
