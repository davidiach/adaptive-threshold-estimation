import ThresholdHC.OptimalQuantile.WeightedPrice

noncomputable section
open Real
open scoped BigOperators
namespace ThresholdHC.OptimalQuantile
open ThresholdHC.EntropyTailQuantile

def dyadicCost (n : ℕ) (x : Option (Fin n) → ℝ) : ℝ :=
  ∑ j, (2 : ℝ)^j.val*x (some j)

def finiteVectorBound (n : ℕ) (k : ℝ) : Prop :=
  ∀ x : Option (Fin n) → ℝ, (∀ i, 0 ≤ x i) →
    1+sqrt (costEntropy x) ≤ k*(sqrt (1+x none)+dyadicCost n x)

def tangentWeight {n : ℕ} (u : ℝ) : Option (Fin n) → ℝ
  | none => 1/(2*u)
  | some j => (2 : ℝ)^j.val

def tangentOffset (k u : ℝ) : ℝ := k*(u+1/u)/2-1

def dualPrice (k u : ℝ) : ℝ := 2*k^2*(u+1/u)-4*k

def finitePartition (n : ℕ) (k u : ℝ) : ℝ :=
  exp (1-dualPrice k u/(2*u))+∑ j : Fin n, exp (1-dualPrice k u*(2 : ℝ)^j.val)

theorem tangentWeight_pos {n : ℕ} {u : ℝ} (hu : 0 < u) (i : Option (Fin n)) :
    0 < tangentWeight u i := by
  cases i with
  | none => dsimp [tangentWeight]; positivity
  | some j => dsimp [tangentWeight]; positivity

theorem tangentOffset_nonneg {k u : ℝ} (hk : 1 ≤ k) (hu : 1 ≤ u) :
    0 ≤ tangentOffset k u := by
  have hu0 : 0 < u := by linarith
  have hA : 1 ≤ (u+1/u)/2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    have h : 2-u ≤ 1/u := (le_div_iff₀ hu0).mpr (by nlinarith only [sq_nonneg (u-1)])
    linarith
  have hm := mul_le_mul hk hA (by norm_num : (0 : ℝ) ≤ 1) (by linarith : 0 ≤ k)
  dsimp [tangentOffset]
  nlinarith only [hm]

theorem tangent_price_identity (n : ℕ) (k u : ℝ) (x : Option (Fin n) → ℝ) :
    k*((u+(1+x none)/u)/2+dyadicCost n x) =
      1+tangentOffset k u+k*(∑ i, tangentWeight u i*x i) := by
  rw [Fintype.sum_option]
  simp only [tangentWeight,tangentOffset,dyadicCost,div_eq_mul_inv,mul_inv_rev]
  ring

theorem finitePartition_eq_sum (n : ℕ) (k u : ℝ) :
    finitePartition n k u = ∑ i : Option (Fin n), exp (1-(4*k*tangentOffset k u)*tangentWeight u i) := by
  have hp : 4*k*tangentOffset k u = dualPrice k u := by
    unfold tangentOffset dualPrice
    ring
  rw [hp,Fintype.sum_option]
  simp only [finitePartition,tangentWeight,div_eq_mul_inv,one_mul]

end ThresholdHC.OptimalQuantile
