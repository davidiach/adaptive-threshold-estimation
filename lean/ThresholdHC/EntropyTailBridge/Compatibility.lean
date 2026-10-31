import ThresholdHC.EntropyTail.Model
import ThresholdHC.EntropyTail.Specification
import ThresholdHC.EntropyTailQuantile.MeasureEntropy
import ThresholdHC.EntropyTailQuantile.TailModulus

/-! Compatibility with the separately frozen entropy-tail interface on main.
Both original mathematical definitions are retained; equality is proved on
finite measures, the domain relevant to probability submeasures. -/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace ThresholdHC.EntropyTailBridge
open ThresholdHC.EntropyTailQuantile
open ThresholdHC.Tier6

theorem canonical_band_eq (j : ℕ) : ThresholdHC.EntropyTail.band j = band j := by
  ext d
  simp only [ThresholdHC.EntropyTail.band,band,bandEdge,Set.mem_setOf_eq]
  have hpow : ((1/2:ℝ)^(j+2)) = (2:ℝ)⁻¹^(j+1)/2 := by
    rw [show j+2 = (j+1)+1 by omega,pow_succ]
    norm_num [div_eq_mul_inv]
  rw [hpow]
  norm_num [div_eq_mul_inv]

theorem canonical_bandCost_eq (σ : Measure Gap) [IsFiniteMeasure σ] (j : ℕ) :
    ThresholdHC.EntropyTail.bandCost σ j = ENNReal.ofReal (bandCost σ j) := by
  rw [ThresholdHC.EntropyTail.bandCost,canonical_band_eq]
  exact (ofReal_integral_eq_lintegral_ofReal (band_inverseSquare_integrable σ j)
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))).symm

theorem canonical_costEntropy_eq {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ThresholdHC.EntropyTail.costEntropy a = costEntropy a := by
  rw [costEntropy_eq_log_sum ha]
  rfl

theorem canonical_gamma_eq (σ : Measure Gap) [IsFiniteMeasure σ] :
    ThresholdHC.EntropyTail.gamma σ = measureCostEntropy σ := by
  have hfin (j : ℕ) : ThresholdHC.EntropyTail.bandCost σ j ≠ ⊤ := by
    rw [canonical_bandCost_eq]
    exact ENNReal.ofReal_ne_top
  have he (J : ℕ) :
      (if ∀ j : Fin (J+1), ThresholdHC.EntropyTail.bandCost σ j ≠ ⊤ then
        ENNReal.ofReal (ThresholdHC.EntropyTail.costEntropy (fun j : Fin (J+1) =>
          (ThresholdHC.EntropyTail.bandCost σ j).toReal)) else ⊤) =
        ENNReal.ofReal (costEntropy (fun j : Fin (J+1) => bandCost σ j)) := by
    rw [if_pos (fun j : Fin (J+1) => hfin j)]
    simp_rw [canonical_bandCost_eq,ENNReal.toReal_ofReal (bandCost_nonneg σ _)]
    rw [canonical_costEntropy_eq _ (fun i => bandCost_nonneg σ i)]
  unfold ThresholdHC.EntropyTail.gamma measureCostEntropy
  simp_rw [he]
  apply le_antisymm
  · exact iSup_le (fun n => le_iSup
      (fun k : ℕ => ENNReal.ofReal (costEntropy (fun j : Fin k => bandCost σ j))) (n+1))
  · apply iSup_le
    intro n
    cases n with
    | zero => simp [costEntropy,costTotal]
    | succ n =>
      exact le_iSup
        (fun k : ℕ => ENNReal.ofReal (costEntropy (fun j : Fin (k+1) => bandCost σ j))) n

theorem canonical_tailCost_eq (ν : Measure Gap) [IsFiniteMeasure ν] (h : ℝ) (hh : 0 ≤ h) :
    ThresholdHC.EntropyTail.tailCost ν h = ENNReal.ofReal (tailModulus ν h) :=
  (ofReal_integral_eq_lintegral_ofReal (tailKernel_integrable ν hh)
    (Filter.Eventually.of_forall (tailKernel_nonneg hh))).symm

theorem canonical_selectionObjective_eq (μ σ : Measure Gap) [IsFiniteMeasure μ]
    (hσ : σ ≤ μ) (ρ B : ℝ) :
    ThresholdHC.EntropyTail.selectionObjective μ ρ B σ = selectionCost μ σ ρ (budgetScale B) := by
  haveI : IsFiniteMeasure σ := isFiniteMeasure_of_le μ hσ
  unfold ThresholdHC.EntropyTail.selectionObjective selectionCost budgetScale
  rw [canonical_gamma_eq,canonical_tailCost_eq _ _ (by positivity)]
  simp only [one_div]

theorem canonical_selection_eq (μ : Measure Gap) [IsFiniteMeasure μ] (ρ B : ℝ) :
    ThresholdHC.EntropyTail.selection μ ρ B = selectionValue μ ρ B := by
  unfold ThresholdHC.EntropyTail.selection selectionValue
  congr 1
  apply iInf_congr
  intro σ
  apply iInf_congr
  intro hσ
  exact canonical_selectionObjective_eq μ σ hσ ρ B

end ThresholdHC.EntropyTailBridge
