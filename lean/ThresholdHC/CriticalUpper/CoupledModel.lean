import ThresholdHC.CriticalUpper.Calibration
import ThresholdHC.Uniform713.Estimator

/-! An observable single-term estimator with a random level and two shared-prefix classifiers. -/

noncomputable section
namespace ThresholdHC.CriticalUpper
open MeasureTheory Set ThresholdHC.CriticalEntropy ThresholdHC.Uniform713
open scoped ENNReal

def calibratedValue (ρ : ℝ) (j : ℕ) (ω : ℕ → Bool) : ℝ :=
  (calibratedScreen ρ j).output ((),ω)

def calibratedCost (ρ : ℝ) (j : ℕ) : (ℕ → Bool) → ℕ :=
  screenCost (screenThreshold (screenLevel ρ j) (screenAccuracy j))
    (screenThreshold (screenLevel ρ j) (screenAccuracy j)+Real.log (1/ρ)) (screenLevel ρ j)

theorem measurable_calibratedValue (ρ : ℝ) (j : ℕ) : Measurable (calibratedValue ρ j) :=
  (calibratedScreen ρ j).measurable_output.comp (measurable_const.prodMk measurable_id)

theorem measurable_calibratedCost (ρ : ℝ) (j : ℕ) : Measurable (calibratedCost ρ j) :=
  measurable_screenCost _ _ _

theorem calibratedValue_binary (ρ : ℝ) (j : ℕ) (ω : ℕ → Bool) :
    calibratedValue ρ j ω = 0 ∨ calibratedValue ρ j ω = 1 :=
  screenDecision_zero_or_one (screenThreshold (screenLevel ρ j) (screenAccuracy j))
    (screenThreshold (screenLevel ρ j) (screenAccuracy j)+Real.log (1/ρ))
    (fun k => dyadicMean Tier2.observations k ω) (screenLevel ρ j)

theorem calibrated_prefix_ext (ρ : ℝ) (j : ℕ) (ω ω' : ℕ → Bool)
    (h : Tier2.tapePrefix (calibratedCost ρ j ω) ω = Tier2.tapePrefix (calibratedCost ρ j ω) ω') :
    calibratedCost ρ j ω' = calibratedCost ρ j ω ∧ calibratedValue ρ j ω' = calibratedValue ρ j ω :=
  screen_prefix_ext _ _ _ ω ω' h

def coupledCost (ρ : ℝ) : ℕ → (ℕ → Bool) → ℕ
  | 0, ω => calibratedCost ρ 0 ω
  | j+1, ω => max (calibratedCost ρ (j+1) ω) (calibratedCost ρ j ω)

def coupledValue (ρ : ℝ) (j : ℕ) (ω : ℕ → Bool) : ℝ :=
  increment (fun k => calibratedValue ρ k ω) j / levelProb j

theorem measurable_coupledCost (ρ : ℝ) (j : ℕ) : Measurable (coupledCost ρ j) := by
  cases j with
  | zero => exact measurable_calibratedCost ρ 0
  | succ j => exact (measurable_calibratedCost ρ (j+1)).max (measurable_calibratedCost ρ j)

theorem measurable_coupledValue (ρ : ℝ) (j : ℕ) : Measurable (coupledValue ρ j) :=
  (measurable_increment (measurable_calibratedValue ρ) j).div_const _

/-- Two classifiers share the same observed prefix. Both have finished when
the larger stopped count is reached; their outputs need not be independent. -/
theorem coupled_prefix_ext (ρ : ℝ) (j : ℕ) (ω ω' : ℕ → Bool)
    (h : Tier2.tapePrefix (coupledCost ρ j ω) ω = Tier2.tapePrefix (coupledCost ρ j ω) ω') :
    coupledCost ρ j ω' = coupledCost ρ j ω ∧ coupledValue ρ j ω' = coupledValue ρ j ω := by
  cases j with
  | zero =>
    have he := calibrated_prefix_ext ρ 0 ω ω' h
    exact ⟨he.1,by simp only [coupledValue,increment,he.2]⟩
  | succ j =>
    have ha := calibrated_prefix_ext ρ (j+1) ω ω' (prefix_eq_restrict h (le_max_left _ _))
    have hb := calibrated_prefix_ext ρ j ω ω' (prefix_eq_restrict h (le_max_right _ _))
    constructor
    · simp only [coupledCost,ha.1,hb.1]
    · simp only [coupledValue,increment,ha.2,hb.2]

def criticalUnbiasedProcedure (ρ : ℝ) : StoppedProcedure ℕ ℝ :=
  BlindUpper.finiteStoppedProcedure (fun z => coupledCost ρ z.1 z.2)
    (fun z => coupledValue ρ z.1 z.2)
    (measurable_from_prod_countable_right (measurable_coupledCost ρ))
    (measurable_from_prod_countable_right (measurable_coupledValue ρ))
    (coupled_prefix_ext ρ)

theorem criticalUnbiasedProcedure_output (ρ : ℝ) :
    (criticalUnbiasedProcedure ρ).output = estimator (calibratedValue ρ) := rfl

theorem criticalUnbiasedProcedure_work (ρ : ℝ) (z : ℕ × (ℕ → Bool)) :
    stoppedProcedureWork (criticalUnbiasedProcedure ρ) z =
      ENNReal.ofReal (coupledCost ρ z.1 z.2 : ℝ) := by
  simp [criticalUnbiasedProcedure,BlindUpper.finiteStoppedProcedure,stoppedProcedureWork]

theorem coupledCost_succ_le (ρ : ℝ) (j : ℕ) (ω : ℕ → Bool) :
    coupledCost ρ (j+1) ω ≤ calibratedCost ρ (j+1) ω+calibratedCost ρ j ω := by
  exact max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)

theorem binary_difference_sq_le (x y : ℝ) (hx : x=0 ∨ x=1) (hy : y=0 ∨ y=1) (b : Bool) :
    (x-y)^2 ≤ |x-Tier2.bit b|+|y-Tier2.bit b| := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> cases b <;> norm_num [Tier2.bit]

theorem binary_difference_sq_le_one (x y : ℝ) (hx : x=0 ∨ x=1) (hy : y=0 ∨ y=1) :
    (x-y)^2 ≤ 1 := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> norm_num

end ThresholdHC.CriticalUpper
