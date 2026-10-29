import ThresholdHC.RareAboveTwo.PopulationError
import ThresholdHC.Uniform713.Estimator

/-! Adjacent finite classifiers coupled on the same observed prefix. -/
noncomputable section
namespace ThresholdHC.RareAboveTwo
open MeasureTheory Set ThresholdHC.CriticalEntropy ThresholdHC.Uniform713
open scoped ENNReal

def coupledCost (a ρ : ℝ) : ℕ → (ℕ → Bool) → ℕ
  | 0, ω => calibratedCost a ρ 0 ω
  | j+1, ω => max (calibratedCost a ρ (j+1) ω) (calibratedCost a ρ j ω)

def coupledValue (a ρ : ℝ) (j : ℕ) (ω : ℕ → Bool) : ℝ :=
  increment (fun k => calibratedValue a ρ k ω) j / levelProb j

theorem measurable_coupledCost (a ρ : ℝ) (j : ℕ) : Measurable (coupledCost a ρ j) := by
  cases j with
  | zero => exact measurable_calibratedCost a ρ 0
  | succ j => exact (measurable_calibratedCost a ρ (j+1)).max (measurable_calibratedCost a ρ j)

theorem measurable_coupledValue (a ρ : ℝ) (j : ℕ) : Measurable (coupledValue a ρ j) :=
  (measurable_increment (measurable_calibratedValue a ρ) j).div_const _

/-- Two classifiers share the same observed prefix. Both have finished when
the larger stopped count is reached; their outputs need not be independent. -/
theorem coupled_prefix_ext (a ρ : ℝ) (j : ℕ) (ω ω' : ℕ → Bool)
    (h : Tier2.tapePrefix (coupledCost a ρ j ω) ω = Tier2.tapePrefix (coupledCost a ρ j ω) ω') :
    coupledCost a ρ j ω' = coupledCost a ρ j ω ∧ coupledValue a ρ j ω' = coupledValue a ρ j ω := by
  cases j with
  | zero =>
    have he := calibrated_prefix_ext a ρ 0 ω ω' h
    exact ⟨he.1,by simp only [coupledValue,increment,he.2]⟩
  | succ j =>
    have ha := calibrated_prefix_ext a ρ (j+1) ω ω' (prefix_eq_restrict h (le_max_left _ _))
    have hb := calibrated_prefix_ext a ρ j ω ω' (prefix_eq_restrict h (le_max_right _ _))
    constructor
    · simp only [coupledCost,ha.1,hb.1]
    · simp only [coupledValue,increment,ha.2,hb.2]

def rareUnbiasedProcedure (a ρ : ℝ) : StoppedProcedure ℕ ℝ :=
  BlindUpper.finiteStoppedProcedure (fun z => coupledCost a ρ z.1 z.2)
    (fun z => coupledValue a ρ z.1 z.2)
    (measurable_from_prod_countable_right (measurable_coupledCost a ρ))
    (measurable_from_prod_countable_right (measurable_coupledValue a ρ))
    (coupled_prefix_ext a ρ)

theorem rareUnbiasedProcedure_output (a ρ : ℝ) :
    (rareUnbiasedProcedure a ρ).output = estimator (calibratedValue a ρ) := rfl

theorem rareUnbiasedProcedure_work (a ρ : ℝ) (z : ℕ × (ℕ → Bool)) :
    stoppedProcedureWork (rareUnbiasedProcedure a ρ) z =
      ENNReal.ofReal (coupledCost a ρ z.1 z.2 : ℝ) := by
  simp [rareUnbiasedProcedure,BlindUpper.finiteStoppedProcedure,stoppedProcedureWork]

theorem coupledCost_succ_le (a ρ : ℝ) (j : ℕ) (ω : ℕ → Bool) :
    coupledCost a ρ (j+1) ω ≤ calibratedCost a ρ (j+1) ω+calibratedCost a ρ j ω := by
  exact max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)

theorem binary_difference_sq_le (x y : ℝ) (hx : x=0 ∨ x=1) (hy : y=0 ∨ y=1) (b : Bool) :
    (x-y)^2 ≤ |x-Tier2.bit b|+|y-Tier2.bit b| := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> cases b <;> norm_num [Tier2.bit]

theorem binary_difference_sq_le_one (x y : ℝ) (hx : x=0 ∨ x=1) (hy : y=0 ∨ y=1) :
    (x-y)^2 ≤ 1 := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> norm_num

end ThresholdHC.RareAboveTwo
