import FeedbackRisk
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

namespace PilotFeedback
noncomputable section
open MeasureTheory
open scoped ENNReal

def point (i : Fin 4) : ℕ := ![0,3,7,10] i
def prior (i : Fin 4) : ℝ := (![2,3,3,2] i : ℝ)/10

theorem prior_nonneg (i : Fin 4) : 0 ≤ prior i := by fin_cases i <;> norm_num [prior]

private theorem sumTo_eq (v : ℕ → ℝ) (n : ℕ) :
    sumTo v n = ∑ k ∈ Finset.range n, v k := by
  induction n with
  | zero => simp [sumTo]
  | succ n ih => rw [sumTo,ih,Finset.sum_range_succ]

/-- The contribution of one grouped transcript to the risk at p=u/10. -/
def pointLoss (j h t a b c u : ℕ) (x : ℝ) : ℝ :=
  (mass j h t a b c u 1 : ℝ) / (100:ℝ)^25 * (x - (u:ℝ)/10)^2

def pointMSE (r : Rule) (i : Fin 4) : ℝ :=
  ∑ j ∈ Finset.range 19,
  ∑ a ∈ Finset.range (r.heads j+1),
  ∑ b ∈ Finset.range (r.tails j+1),
  ∑ c ∈ Finset.range (7-r.heads j-r.tails j+1),
    pointLoss j (r.heads j) (r.tails j) a b c (point i) (r.estimate j a b c)

theorem pointMSE_nonneg (r : Rule) (i : Fin 4) : 0 ≤ pointMSE r i := by
  unfold pointMSE pointLoss
  positivity

private theorem cell_mixture (j h t a b c : ℕ) (x : ℝ) :
    cellLoss j h t a b c x / massDen =
      ∑ i : Fin 4, prior i * pointLoss j h t a b c (point i) x := by
  have weight (u w : ℕ) : mass j h t a b c u w = w * mass j h t a b c u 1 := by
    simp [mass,mul_assoc]
  simp only [cellLoss,loss]
  rw [weight 0 2,weight 3 3,weight 7 3,weight 10 2]
  norm_num [Fin.sum_univ_succ,point,prior,pointLoss,massDen]
  ring

theorem bayes_mixture (r : Rule) : bayesMSE r = ∑ i : Fin 4, prior i * pointMSE r i := by
  simp only [bayesMSE,rowLoss,cells,sumTo_eq,Finset.sum_div,cell_mixture,
    pointMSE,Finset.mul_sum]
  conv_lhs =>
    enter [2,j,2,a,2,b]
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2,j,2,a]
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2,j]
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]

/-- Worst MSE among the four sign probabilities, after averaging over the seed. -/
def worstFour {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (r : Ω → Rule) : ℝ≥0∞ :=
  ⨆ i : Fin 4, ∫⁻ z, ENNReal.ofReal (pointMSE (r z) i) ∂μ

theorem worstFour_lower {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (r : Ω → Rule)
    (hm : ∀ i, Measurable fun z => ENNReal.ofReal (pointMSE (r z) i)) :
    ENNReal.ofReal ((18735887/100000000 : ℝ)^2) ≤ worstFour μ r := by
  have mix (z : Ω) : ENNReal.ofReal (bayesMSE (r z)) =
      ∑ i : Fin 4, ENNReal.ofReal (prior i) * ENNReal.ofReal (pointMSE (r z) i) := by
    rw [bayes_mixture,ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (prior_nonneg i) (pointMSE_nonneg _ _))]
    simp only [ENNReal.ofReal_mul (prior_nonneg _)]
  apply (randomized_lower μ r).trans
  simp_rw [mix]
  rw [lintegral_finsetSum (μ := μ) (f := fun i z => ENNReal.ofReal (prior i) *
    ENNReal.ofReal (pointMSE (r z) i)) Finset.univ (fun i _ => measurable_const.mul (hm i))]
  simp_rw [lintegral_const_mul _ (hm _)]
  calc
    _ ≤ ∑ i : Fin 4, ENNReal.ofReal (prior i) * worstFour μ r := by
      apply Finset.sum_le_sum
      intro i _
      gcongr
      exact le_iSup (fun k : Fin 4 => ∫⁻ z, ENNReal.ofReal (pointMSE (r z) k) ∂μ) i
    _ = _ := by
      rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => prior_nonneg i)]
      norm_num [Fin.sum_univ_succ,prior]

end
end PilotFeedback
