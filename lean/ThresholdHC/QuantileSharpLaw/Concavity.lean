import ThresholdHC.QuantileSharpLaw.Lipschitz
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

noncomputable section
open Real
open scoped BigOperators
namespace ThresholdHC.QuantileSharpLaw
open ThresholdHC.EntropyTailQuantile

theorem rootEntropy_mix {ι : Type*} [Fintype ι] {x y : ι → ℝ} {s t : ℝ}
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i) (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s+t=1) :
    s*sqrt (costEntropy x)+t*sqrt (costEntropy y) ≤
      sqrt (costEntropy (fun i => s*x i+t*y i)) := by
  have he := costEntropy_superadditive (fun i => mul_nonneg hs (hx i))
    (fun i => mul_nonneg ht (hy i))
  rw [costEntropy_smul,costEntropy_smul] at he
  have hr := strictConcaveOn_sqrt.concaveOn.2 (costEntropy_nonneg hx) (costEntropy_nonneg hy)
    hs ht hst
  simp only [smul_eq_mul] at hr
  exact hr.trans (sqrt_le_sqrt he)

def corePrice {ι : Type*} [Fintype ι] (e m w v : ι → ℝ) : ℝ :=
  sqrt (costEntropy (fun i => v i+e i))+∑ i, m i*(w i-v i)

theorem corePrice_concaveOn {ι : Type*} [Fintype ι] (e m w : ι → ℝ)
    (he : ∀ i, 0 ≤ e i) :
    ConcaveOn ℝ (Set.Icc (0 : ι → ℝ) w) (corePrice e m w) := by
  refine ⟨convex_Icc _ _,?_⟩
  intro x hx y hy s t hs ht hst
  have hr := rootEntropy_mix (fun i => add_nonneg (hx.1 i) (he i))
    (fun i => add_nonneg (hy.1 i) (he i)) hs ht hst
  have heq : (fun i => s*(x i+e i)+t*(y i+e i)) =
      (fun i => (s*x i+t*y i)+e i) := by
    funext i
    nlinarith only [congrArg (fun z : ℝ => z*e i) hst]
  rw [heq] at hr
  have hsums : (∑ i, m i*(w i-(s*x i+t*y i))) =
      s*(∑ i, m i*(w i-x i))+t*(∑ i, m i*(w i-y i)) := by
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    nlinarith only [congrArg (fun z : ℝ => z*(m i*w i)) hst]
  simp only [corePrice,Pi.smul_apply,Pi.add_apply,smul_eq_mul,hsums]
  nlinarith only [hr]

end ThresholdHC.QuantileSharpLaw
