import FeedbackTable
import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

namespace PilotFeedback
noncomputable section
open MeasureTheory
open scoped ENNReal

/-- Unnormalized squared loss at the four possible values of p. -/
def loss (a b c d : ℕ) (x : ℝ) : ℝ :=
  a*x^2 + b*(x-3/10)^2 + c*(x-7/10)^2 + d*(x-1)^2

theorem floor_le_loss (a b c d : ℕ) (x : ℝ) :
    (varianceFloor a b c d : ℝ) * massDen ≤ scale * loss a b c d x := by
  by_cases zero : a+b+c+d = 0
  · have : a=0 ∧ b=0 ∧ c=0 ∧ d=0 := by omega
    obtain ⟨rfl,rfl,rfl,rfl⟩ := this
    simp [varianceFloor,pairSum,loss]
  have pos : 0 < (a:ℝ)+b+c+d := by exact_mod_cast Nat.pos_of_ne_zero zero
  have fl := Nat.div_mul_le_self (scale * pairSum a b c d) (100*massDen*(a+b+c+d))
  change varianceFloor a b c d * (100*massDen*(a+b+c+d)) ≤ _ at fl
  have flr : (varianceFloor a b c d : ℝ) * (100*massDen*((a:ℝ)+b+c+d)) ≤
      scale * (pairSum a b c d : ℝ) := by exact_mod_cast fl
  have id : 100*((a:ℝ)+b+c+d)*loss a b c d x =
      (10*((a:ℝ)+b+c+d)*x-(3*b+7*c+10*d : ℝ))^2 + (pairSum a b c d : ℝ) := by
    unfold pairSum loss
    push_cast
    ring
  have bound : (pairSum a b c d : ℝ) ≤ 100*((a:ℝ)+b+c+d)*loss a b c d x := by
    rw [id]; linarith [sq_nonneg (10*((a:ℝ)+b+c+d)*x-(3*b+7*c+10*d : ℝ))]
  have ineq := flr.trans (mul_le_mul_of_nonneg_left bound (Nat.cast_nonneg scale))
  apply le_of_mul_le_mul_left (a := 100*((a:ℝ)+b+c+d)) _ (by positivity)
  linarith only [ineq]

def cellLoss (j h t a b c : ℕ) (x : ℝ) : ℝ :=
  let m := mass j h t a b c
  loss (m 0 2) (m 3 3) (m 7 3) (m 10 2) x

private theorem sum_dom (n : ℕ) (v : ℕ → ℕ) (w : ℕ → ℝ)
    (point : ∀ i < n, (v i : ℝ)*massDen ≤ scale*w i) :
    ((sumTo v n : ℕ) : ℝ)*massDen ≤ scale*sumTo w n := by
  induction n with
  | zero => simp [sumTo]
  | succ n ih =>
    simp only [sumTo, Nat.cast_add, add_mul, mul_add]
    exact add_le_add (ih (fun i hi => point i (by omega))) (point n (by omega))

/-- The design selects the numbers of distinct pilot heads and tails to revisit.
The remaining suffix positions use new coins. The estimate uses all three
group counts as well as the pilot count. -/
structure Rule where
  heads : ℕ → ℕ
  tails : ℕ → ℕ
  valid : ∀ j < 19, legal j (heads j) (tails j)
  estimate : ℕ → ℕ → ℕ → ℕ → ℝ

def rowLoss (r : Rule) (j : ℕ) : ℝ :=
  cells (r.heads j) (r.tails j) (fun a b c =>
    cellLoss j (r.heads j) (r.tails j) a b c (r.estimate j a b c))

/-- Prior-averaged MSE in the grouped-count experiment. -/
def bayesMSE (r : Rule) : ℝ := sumTo (rowLoss r) 19 / massDen

theorem precommitted_lower (r : Rule) :
    (18735887/100000000 : ℝ)^2 < bayesMSE r := by
  have row (j : ℕ) (hj : j < 19) : (rowBound j : ℝ)*massDen ≤ scale*rowLoss r j := by
    have hv := r.valid j hj
    have H := hv.2.2
    have cert := all_rows ⟨j,hj⟩ ⟨r.heads j,by omega⟩ ⟨r.tails j,by omega⟩ hv
    have le : (rowBound j : ℝ) ≤ (rowFloor j (r.heads j) (r.tails j) : ℝ) := by exact_mod_cast cert
    apply (mul_le_mul_of_nonneg_right le (Nat.cast_nonneg massDen)).trans
    unfold rowFloor rowLoss cells
    apply sum_dom
    intro a _
    apply sum_dom
    intro b _
    apply sum_dom
    intro c _
    exact floor_le_loss ..
  have total := sum_dom 19 rowBound (rowLoss r) row
  rw [total_bound] at total
  unfold bayesMSE
  apply (lt_div_iff₀ (by norm_num [massDen] : 0 < (massDen:ℝ))).2
  norm_num [massDen,scale] at total ⊢
  linarith only [total]

/-- Any prior-independent seed may choose both the design and the estimator.
The nonnegative integral also covers unbounded (or infinite-risk) outputs. -/
theorem randomized_lower {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (r : Ω → Rule) :
    ENNReal.ofReal ((18735887/100000000 : ℝ)^2) ≤
      ∫⁻ z, ENNReal.ofReal (bayesMSE (r z)) ∂μ := by
  calc
    _ = ∫⁻ _ : Ω, ENNReal.ofReal ((18735887/100000000 : ℝ)^2) ∂μ := by simp
    _ ≤ _ := lintegral_mono fun z => ENNReal.ofReal_le_ofReal (precommitted_lower (r z)).le

end
end PilotFeedback
