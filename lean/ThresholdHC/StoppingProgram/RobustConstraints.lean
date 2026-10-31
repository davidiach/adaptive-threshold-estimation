import ThresholdHC.StoppingProgram.ProgramGeometry
import ThresholdHC.StoppingProgram.MomentImage
import ThresholdHC.StoppingProgram.CompactMaximum

/-! The four robust inequalities as attained maxima over the actual rare
moment image. This representation preserves the original feasible set. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap SignLaw signMean)
open ThresholdHC.RareAboveTwo

def coordinateMean {N : ℕ} (u : Option (CountState N) → ℝ) (z : CountState N → ℝ) : ℝ :=
  ∑ s, u (some s)*z s

theorem coordinateMean_combo_right {N : ℕ} (u : Option (CountState N) → ℝ)
    (z w : CountState N → ℝ) (a b : ℝ) :
    coordinateMean u (a • z+b • w) = a*coordinateMean u z+b*coordinateMean u w := by
  simp only [coordinateMean,Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_add,
    Finset.sum_add_distrib,Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro s _ <;> ring

theorem coordinateMean_combo_left {N : ℕ} (u v : Option (CountState N) → ℝ)
    (z : CountState N → ℝ) (a b : ℝ) :
    coordinateMean (a • u+b • v) z = a*coordinateMean u z+b*coordinateMean v z := by
  simp only [coordinateMean,Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_mul,
    Finset.sum_add_distrib,Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro s _ <;> ring

def pointResidual {N : ℕ} (B : ℝ) (j : Fin 4) (u : Option (CountState N) → ℝ)
    (x : ProgramPoint N) : ℝ :=
  ![x.1 0+coordinateMean u (x.2 2)-u none-x.1 1,
    u none-x.1 0-coordinateMean u (x.2 2)-x.1 1,
    coordinateMean u (x.2 3)-x.1 2,
    coordinateMean u (x.2 1)-B] j

theorem pointResidual_continuous_prior {N : ℕ} (B : ℝ) (j : Fin 4) (x : ProgramPoint N) :
    Continuous (fun u => pointResidual B j u x) := by
  fin_cases j <;> dsimp [pointResidual,coordinateMean] <;> fun_prop

theorem pointResidual_continuous_point {N : ℕ} (B : ℝ) (j : Fin 4) (u : Option (CountState N) → ℝ) :
    Continuous (pointResidual B j u) := by
  change Continuous (fun x => pointResidual B j u x)
  fin_cases j <;> dsimp [pointResidual,coordinateMean] <;> fun_prop

theorem pointResidual_combo_point {N : ℕ} (B : ℝ) (j : Fin 4) (u : Option (CountState N) → ℝ)
    (x y : ProgramPoint N) (a b : ℝ) (hab : a+b=1) :
    pointResidual B j u (a • x+b • y) = a*pointResidual B j u x+b*pointResidual B j u y := by
  have hm (k : Fin 4) : coordinateMean u ((a • x+b • y).2 k) =
      a*coordinateMean u (x.2 k)+b*coordinateMean u (y.2 k) :=
    coordinateMean_combo_right u (x.2 k) (y.2 k) a b
  fin_cases j <;> simp only [pointResidual,hm,Prod.fst_add,Prod.smul_fst,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  all_goals simp only [Matrix.cons_val_zero',Matrix.cons_val_succ']
  all_goals nlinarith [congrArg (fun t : ℝ => t*u none) hab,congrArg (fun t : ℝ => t*B) hab]

theorem pointResidual_combo_prior {N : ℕ} (B : ℝ) (j : Fin 4)
    (u v : Option (CountState N) → ℝ) (x : ProgramPoint N) (a b : ℝ) (hab : a+b=1) :
    pointResidual B j (a • u+b • v) x = a*pointResidual B j u x+b*pointResidual B j v x := by
  fin_cases j <;> simp only [pointResidual,coordinateMean_combo_left,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  all_goals simp only [Matrix.cons_val_zero',Matrix.cons_val_succ']
  all_goals nlinarith [congrArg (fun t : ℝ => t*x.1 0) hab,
    congrArg (fun t : ℝ => t*x.1 1) hab,congrArg (fun t : ℝ => t*x.1 2) hab,
    congrArg (fun t : ℝ => t*B) hab]

def robustResidual {N : ℕ} (μ : Measure Gap) (ρ B : ℝ) (j : Fin 4) (x : ProgramPoint N) : ℝ :=
  compactMaximum (priorMomentImage N μ ρ) (fun u => pointResidual B j u x)

theorem robustResidual_convex {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (hρ : 0 ≤ ρ) (B : ℝ) (j : Fin 4) :
    ConvexOn ℝ (programDomain N) (robustResidual μ ρ B j) := by
  apply compactMaximum_convex _ (priorMomentImage_nonempty N μ hρ)
    (priorMomentImage_compact_convex N μ ρ).1 _ (programDomain_convex N)
    (fun u x => pointResidual B j u x)
    (fun x => (pointResidual_continuous_prior B j x).continuousOn)
  intro u hu
  refine ⟨programDomain_convex N,?_⟩
  intro x hx y hy a b ha hb hab
  exact (pointResidual_combo_point B j u x y a b hab).le

theorem robustResidual_nonpos_iff {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (hρ : 0 ≤ ρ) (B : ℝ) (j : Fin 4) (x : ProgramPoint N) :
    robustResidual μ ρ B j x ≤ 0 ↔
      ∀ q : SignLaw, RarePrior μ ρ q → pointResidual B j (priorCoordinates N μ q) x ≤ 0 := by
  rw [robustResidual,compactMaximum_le_iff _ (priorMomentImage_nonempty N μ hρ)
    (priorMomentImage_compact_convex N μ ρ).1 _
    (pointResidual_continuous_prior B j x).continuousOn]
  constructor
  · intro h q hq
    exact h _ (priorMomentImage_mem N μ ρ q hq)
  · rintro h u ⟨q,hq,rfl⟩
    exact h q hq

theorem point_feasible_iff {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (hρ : 0 ≤ ρ) (B : ℝ) (x : ProgramPoint N) :
    Feasible μ ρ B (pointCertificate x) ↔
      x ∈ programDomain N ∧ ∀ j, robustResidual μ ρ B j x ≤ 0 := by
  simp only [robustResidual_nonpos_iff μ hρ]
  constructor
  · intro h
    refine ⟨⟨h.cone,h.bias_nonneg,h.variance_nonneg⟩,?_⟩
    intro j q hq
    have hb := abs_le.mp (h.bias_bound q hq)
    have hv := h.variance_bound q hq
    have hw := h.work_bound q hq
    dsimp only [pointCertificate,pointFlow,countMean] at hb hv hw
    fin_cases j <;> dsimp [pointResidual,coordinateMean,priorCoordinates] <;> linarith
  · rintro ⟨hx,h⟩
    refine ⟨hx.1,hx.2.1,hx.2.2,?_,?_,?_⟩
    · intro q hq
      have h0 := h 0 q hq
      have h1 := h 1 q hq
      simp only [pointResidual,Matrix.cons_val_zero,Matrix.cons_val_one,coordinateMean,priorCoordinates] at h0 h1
      apply abs_le.mpr
      dsimp only [pointCertificate,pointFlow,countMean]
      constructor <;> linarith
    · intro q hq
      have h2 := h 2 q hq
      simpa [pointResidual,coordinateMean,priorCoordinates,pointCertificate,pointFlow,countMean] using h2
    · intro q hq
      have h3 := h 3 q hq
      simpa [pointResidual,coordinateMean,priorCoordinates,pointCertificate,pointFlow,countMean] using h3

end ThresholdHC.StoppingProgram
