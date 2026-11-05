import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Tactic

noncomputable section
open MeasureTheory ProbabilityTheory Real
open scoped BigOperators ENNReal NNReal
namespace ThresholdHC.LawAdaptation

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

/-- Bounded parity observations have sub-Gaussian parameter one after centering. -/
theorem centered_subgaussian (X : Ω → ℝ) (hm : AEMeasurable X P)
    (hb : ∀ᵐ ω ∂P, X ω ∈ Set.Icc (-1:ℝ) 1) :
    HasSubgaussianMGF (fun ω => X ω - ∫ x, X x ∂P) 1 P := by
  have h := hasSubgaussianMGF_of_mem_Icc hm hb
  norm_num at h
  exact h

/-- A two-sided exponential bound for an average of independent bounded observations. -/
theorem bounded_average_tail {n : ℕ} (hn : 0 < n) (X : Fin n → Ω → ℝ)
    (hm : ∀ i, AEMeasurable (X i) P)
    (hb : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Set.Icc (-1:ℝ) 1)
    (hi : iIndepFun X P) {a ε : ℝ} (hmean : ∀ i, ∫ ω, X i ω ∂P = a)
    (hε : 0 ≤ ε) :
    P.real {ω | ε < |(∑ i, X i ω)/(n:ℝ)-a|} ≤ 2*exp (-(n:ℝ)*ε^2/2) := by
  let Y := fun i ω => X i ω-a
  have hy (i : Fin n) : HasSubgaussianMGF (Y i) 1 P := by
    simpa only [hmean i] using centered_subgaussian P (X i) (hm i) (hb i)
  have hind : iIndepFun Y P := hi.comp (fun _ x => x-a) (fun _ => measurable_id.sub_const a)
  have hs : HasSubgaussianMGF (fun ω => ∑ i, Y i ω) (n:ℝ≥0) P := by
    simpa using HasSubgaussianMGF.sum_of_iIndepFun hind
      (s := Finset.univ) (fun i _ => hy i)
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hu := hs.measure_ge_le (mul_nonneg hnR.le hε)
  have hl := hs.neg.measure_ge_le (mul_nonneg hnR.le hε)
  have hcalc : -((n:ℝ)*ε)^2/(2*(n:ℝ)) = -(n:ℝ)*ε^2/2 := by
    field_simp
  simp only [NNReal.coe_natCast, hcalc] at hu hl
  calc
    _ ≤ P.real ({ω | (n:ℝ)*ε ≤ ∑ i, Y i ω} ∪
        {ω | (n:ℝ)*ε ≤ -(∑ i, Y i ω)}) := by
      refine measureReal_mono ?_ (measure_ne_top _ _)
      intro ω hω
      have he : (∑ i, Y i ω) = (∑ i, X i ω) - (n:ℝ)*a := by
        simp [Y, Finset.sum_sub_distrib]
      have ha : ε < (∑ i, X i ω)/(n:ℝ)-a ∨
          ε < -((∑ i, X i ω)/(n:ℝ)-a) := lt_abs.mp hω
      have heq : (∑ i, X i ω)/(n:ℝ)*n = ∑ i, X i ω := by
        exact div_mul_cancel₀ _ hnR.ne'
      rcases ha with h | h
      · left
        dsimp only [Set.mem_ofPred_eq]
        have hh := mul_lt_mul_of_pos_right h hnR
        rw [he]
        nlinarith
      · right
        dsimp only [Set.mem_ofPred_eq]
        have hh := mul_lt_mul_of_pos_right h hnR
        rw [he]
        nlinarith
    _ ≤ _ := (measureReal_union_le _ _).trans (by simpa only [Pi.neg_apply, two_mul] using add_le_add hu hl)

end ThresholdHC.LawAdaptation

