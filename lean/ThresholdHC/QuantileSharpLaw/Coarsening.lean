import ThresholdHC.QuantileSharpLaw.BinarySlope

noncomputable section
open Real
open scoped BigOperators
namespace ThresholdHC.QuantileSharpLaw
open ThresholdHC.EntropyTailQuantile

theorem negMulLog_sum_le {ι : Type*} [Fintype ι] (v : ι → ℝ) (hv : ∀ i, 0 ≤ v i) :
    negMulLog (costTotal v) ≤ ∑ i, negMulLog (v i) := by
  have h (s : Finset ι) : negMulLog (∑ i ∈ s, v i) ≤ ∑ i ∈ s, negMulLog (v i) := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi,Finset.sum_insert hi]
      exact (negMulLog_add_le (hv i) (Finset.sum_nonneg (fun j _ => hv j))).trans
        (add_le_add le_rfl ih)
  exact h Finset.univ

def bumpedCost {ι : Type*} (a : ℝ) (v : ι → ℝ) (y : ℝ) : Option ι → ℝ
  | none => a+y^2
  | some i => v i

theorem bumpedCost_nonneg {ι : Type*} {a : ℝ} {v : ι → ℝ}
    (ha : 0 ≤ a) (hv : ∀ i, 0 ≤ v i) (y : ℝ) (i : Option ι) :
    0 ≤ bumpedCost a v y i := by
  cases i with
  | none => exact add_nonneg ha (sq_nonneg _)
  | some i => exact hv i

theorem bumpedCost_total {ι : Type*} [Fintype ι] (a : ℝ) (v : ι → ℝ) (y : ℝ) :
    costTotal (bumpedCost a v y) = a+y^2+costTotal v := by
  simp [costTotal,Fintype.sum_option,bumpedCost]

theorem bumpedCost_entropy {ι : Type*} [Fintype ι] (a : ℝ) (v : ι → ℝ) (y : ℝ) :
    costEntropy (bumpedCost a v y) = a+y^2+costTotal v+
      negMulLog (a+y^2)+(∑ i, negMulLog (v i))-negMulLog (a+y^2+costTotal v) := by
  simp only [costEntropy,bumpedCost_total,Fintype.sum_option,bumpedCost]
  ring

theorem binary_homogeneous_identity {q A : ℝ} (hM : 0 < q+A) :
    q+A+negMulLog q+negMulLog A-negMulLog (q+A) =
      (q+A)*(1+binEntropy (q/(q+A))) := by
  have hp : (q+A)*(q/(q+A)) = q := by field_simp
  have hq : (q+A)*(1-q/(q+A)) = A := by field_simp; ring
  rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  have he1 := negMulLog_mul (q+A) (q/(q+A))
  have he2 := negMulLog_mul (q+A) (1-q/(q+A))
  rw [hp] at he1
  rw [hq] at he2
  nlinarith only [he1,he2]

theorem bumpedCost_binary_lower {ι : Type*} [Fintype ι] {a y : ℝ} {v : ι → ℝ}
    (ha : 0 ≤ a) (hv : ∀ i, 0 ≤ v i) (hy : 0 < y) :
    (a+y^2+costTotal v)*(1+binEntropy ((a+y^2)/(a+y^2+costTotal v))) ≤
      costEntropy (bumpedCost a v y) := by
  have hM : 0 < (a+y^2)+costTotal v := by
    have hV := costTotal_nonneg hv
    nlinarith only [hV,ha,hy]
  rw [← binary_homogeneous_identity hM,bumpedCost_entropy]
  linarith only [negMulLog_sum_le v hv]

end ThresholdHC.QuantileSharpLaw
