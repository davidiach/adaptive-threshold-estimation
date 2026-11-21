import ThresholdHC.FiniteQuantileFormula.Split
import ThresholdHC.EntropyTailQuantile.ScaleSeparated

/-! The closed quantile value of a finite law is the explicit expression of eqs. (67)-(69):
the tail modulus is `T_h`, the band costs of the core are `a*_j`, the measure
cost entropy of the core is `Γ_κ`, and the general-law closed value is `Q(B)`. -/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators Classical
namespace ThresholdHC.FiniteQuantileFormula
open ThresholdHC.Tier6 ThresholdHC.EntropyTailQuantile

variable {n : ℕ}

theorem tailSum_nonneg (d : Fin n → Gap) (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (ρ : ℝ)
    {h : ℝ} (hh : 0 ≤ h) : 0 ≤ tailSum d w ρ h :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (tailWeight_nonneg w hw ρ i)
    (le_min zero_le_one (div_nonneg hh (d i).2.1.le)))

theorem tailModulus_atoms (d : Fin n → Gap) (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (ρ h : ℝ) :
    tailModulus (∑ i, ENNReal.ofReal (tailWeight w ρ i) • Measure.dirac (d i)) h =
      tailSum d w ρ h :=
  atoms_integral d _ (tailWeight_nonneg w hw ρ) _

theorem finiteCoreCost_nonneg (d : Fin n → Gap) (w : Fin n → ℝ) (ρ : ℝ) (j : ℕ) :
    0 ≤ finiteCoreCost d w ρ j := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact div_nonneg (sub_nonneg.mpr (tailWeight_le w ρ i)) (sq_nonneg _)
  · exact le_rfl

theorem bandCost_atoms (d : Fin n → Gap) (w : Fin n → ℝ) (ρ : ℝ) (j : ℕ) :
    bandCost (∑ i, ENNReal.ofReal (w i - tailWeight w ρ i) • Measure.dirac (d i)) j =
      finiteCoreCost d w ρ j := by
  have hc : ∀ i, 0 ≤ w i - tailWeight w ρ i := fun i => sub_nonneg.mpr (tailWeight_le w ρ i)
  have hn (i : Fin n) : 0 ≤ (if d i ∈ band j then w i - tailWeight w ρ i else 0) := by
    split_ifs
    · exact hc i
    · exact le_rfl
  rw [bandCost, atoms_restrict, atoms_integral d _ hn]
  unfold finiteCoreCost
  apply Finset.sum_congr rfl
  intro i _
  split_ifs
  · rw [inv_pow]
    exact (div_eq_mul_inv _ _).symm
  · exact zero_mul _

theorem coreGamma_eq_costEntropy (d : Fin n → Gap) (w : Fin n → ℝ) (ρ : ℝ) (N : ℕ) :
    coreGamma d w ρ N = costEntropy (fun j : Fin N => finiteCoreCost d w ρ j) := by
  rw [costEntropy_eq_log_sum (a := fun j : Fin N => finiteCoreCost d w ρ j)
    (fun j => finiteCoreCost_nonneg d w ρ j)]
  unfold coreGamma costTotal
  rw [Fin.sum_univ_eq_sum_range (fun j => finiteCoreCost d w ρ j) N,
    Fin.sum_univ_eq_sum_range (fun j => finiteCoreCost d w ρ j *
      Real.log ((∑ l ∈ Finset.range N, finiteCoreCost d w ρ l) / finiteCoreCost d w ρ j)) N]

theorem coreGamma_nonneg (d : Fin n → Gap) (w : Fin n → ℝ) (ρ : ℝ) (N : ℕ) :
    0 ≤ coreGamma d w ρ N := by
  rw [coreGamma_eq_costEntropy]
  exact costEntropy_nonneg (a := fun j : Fin N => finiteCoreCost d w ρ j)
    (fun j => finiteCoreCost_nonneg d w ρ j)

private theorem ofReal_min_eq (x y : ℝ) :
    min (ENNReal.ofReal x) (ENNReal.ofReal y) = ENNReal.ofReal (min x y) := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, min_eq_left (ENNReal.ofReal_le_ofReal h)]
  · rw [min_eq_right h, min_eq_right (ENNReal.ofReal_le_ofReal h)]

theorem finite_formula_of_le_one (d : Fin n → Gap) (w : Fin n → ℝ) (μ : Measure Gap)
    [IsProbabilityMeasure μ] (hd : StrictMono (fun i => (d i : ℝ))) (hw : ∀ i, 0 < w i)
    (hsum : ∑ i, w i = 1) (hμ : μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i))
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (B : ℝ) {N : ℕ} (hN : ∀ i, bandEdge N < (d i : ℝ)) :
    quantileTail μ ρ = ∑ i, ENNReal.ofReal (tailWeight w ρ i) • Measure.dirac (d i) ∧
      quantileCore μ ρ = ∑ i, ENNReal.ofReal (w i - tailWeight w ρ i) • Measure.dirac (d i) ∧
      closedQuantileValue μ ρ B = ENNReal.ofReal (finiteQuantile d w ρ B N) := by
  have hw0 : ∀ i, 0 ≤ w i := fun i => (hw i).le
  obtain ⟨k, ht, htail, hcore⟩ := finite_split d w μ hd hw hsum hμ hρ hρ1
  refine ⟨htail, hcore, ?_⟩
  have hE : measureCostEntropy (quantileCore μ ρ) = ENNReal.ofReal (coreGamma d w ρ N) := by
    rw [measureCostEntropy_eq_prefix_of_support _ (quantileCore_support μ ρ)
      (by rw [ht]; exact hN k), hcore]
    have hfun : (fun j : Fin N => bandCost
        (∑ i, ENNReal.ofReal (w i - tailWeight w ρ i) • Measure.dirac (d i)) (j : ℕ)) =
        fun j : Fin N => finiteCoreCost d w ρ j :=
      funext (fun j => bandCost_atoms d w ρ j)
    rw [hfun, coreGamma_eq_costEntropy]
  have hh : 0 ≤ (Real.sqrt B)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg B)
  have hΓ := coreGamma_nonneg d w ρ N
  unfold closedQuantileValue EntropyTailQuantile.budgetScale
  rw [htail, tailModulus_atoms d w hw0, hE, ← ENNReal.ofReal_mul hρ.le,
    ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hρ.le hΓ) (by norm_num), ← Real.sqrt_eq_rpow,
    ← ENNReal.ofReal_mul hh, ← ENNReal.ofReal_add (tailSum_nonneg d w hw0 ρ hh)
      (mul_nonneg hh (Real.sqrt_nonneg _)), ofReal_min_eq]
  rfl

end ThresholdHC.FiniteQuantileFormula
