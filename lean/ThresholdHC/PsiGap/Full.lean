import ThresholdHC.PsiGap.Entropy
import ThresholdHC.PsiSelection.Full
import ThresholdHC.EntropyTail.Upper
import ThresholdHC.EntropyTailExecution.UpperTheorem

/-! The distance of `Ψ` from the rate (v6 Theorem 14.11) against the locked
statements. With `Γ_κ = A_κ (1 + E_κ)` the core term of `Q` is `√(1 + E_κ)`
times that of `Q⁰`, which gives `Q ≤ √(1 + E_κ) Q⁰`; the checked closed form
`Q⁰ ≤ √2 Ψ` and the checked bounds `10^{-17} Q ≤ R ≤ 30001 Q` give the rest. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.PsiGap
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.PsiClosedForm
open ThresholdHC.EntropyTailQuantile (quantileTail quantileCore quantileThreshold
  closedQuantileValue measureCostEntropy quantileTail_le quantileTail_mass
  quantileTail_add_core quantileCore_support quantileThreshold_properties)

theorem core_entropy : CoreEntropyStatement := by
  intro μ _ ρ hρ hρ4
  have hρ1 : ρ ≤ 1 := by linarith
  have hκ : IsFiniteMeasure (quantileCore μ ρ) :=
    isFiniteMeasure_of_le μ (quantileCore_le μ ρ)
  have ht := quantileThreshold_properties μ hρ hρ1
  have hne : quantileCore μ ρ univ ≠ 0 := by
    intro h0
    have hadd := quantileTail_add_core μ hρ hρ1
    have h1 : μ univ = ENNReal.ofReal ρ := by
      rw [← hadd, Measure.add_apply, h0, add_zero, quantileTail_mass μ hρ hρ1]
    rw [measure_univ] at h1
    have h2 := congrArg ENNReal.toReal h1
    rw [ENNReal.toReal_one, ENNReal.toReal_ofReal hρ.le] at h2
    linarith
  obtain ⟨A, E, hA, hE, hinv, hEdef, hgamma, hlog⟩ :=
    core_entropy_real (quantileCore μ ρ) ht.1 ht.2.1 (quantileCore_support μ ρ) hne
  have hcost : coreCost μ ρ = A := by
    unfold coreCost
    rw [hinv, ENNReal.toReal_ofReal hA.le]
  have hent : coreEntropy μ ρ = E := by
    unfold coreEntropy
    rw [hcost, hEdef]
  rw [hcost, hent]
  exact ⟨hA, hinv, hE, hgamma, hlog⟩

/-- `Q` written with the extended tail cost at the resolution `1/√B`. -/
theorem closedQuantile_eq (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (B : ℝ) :
    closedQuantileValue μ ρ B =
      min (ENNReal.ofReal ρ)
        (ThresholdHC.EntropyTail.tailCost (quantileTail μ ρ) (1 / Real.sqrt B) +
          ENNReal.ofReal (1 / Real.sqrt B) *
            (ENNReal.ofReal ρ * measureCostEntropy (quantileCore μ ρ)) ^ (1/2 : ℝ)) := by
  have hν : IsFiniteMeasure (quantileTail μ ρ) :=
    isFiniteMeasure_of_le μ (quantileTail_le μ hρ hρ1)
  have hh : (0 : ℝ) ≤ 1 / Real.sqrt B := by positivity
  have e : (Real.sqrt B)⁻¹ = 1 / Real.sqrt B := (one_div _).symm
  unfold ThresholdHC.EntropyTailQuantile.closedQuantileValue
    ThresholdHC.EntropyTailQuantile.budgetScale
  rw [e, ThresholdHC.EntropyTail.quantile_tailModulus_eq _ hh]

/-- The core term of `Q` is `√(1 + E_κ)` times the core term of `Q⁰`. -/
theorem core_root (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) :
    (ENNReal.ofReal ρ * measureCostEntropy (quantileCore μ ρ)) ^ (1/2 : ℝ) =
      ENNReal.ofReal (Real.sqrt (1 + coreEntropy μ ρ)) *
        (ENNReal.ofReal ρ * inverseSquareCost (quantileCore μ ρ)) ^ (1/2 : ℝ) := by
  obtain ⟨hA, hinv, hE, hgamma, -⟩ := core_entropy μ ρ hρ hρ4
  have h1E : 0 ≤ 1 + coreEntropy μ ρ := by linarith
  rw [hgamma, hinv, mul_comm (coreCost μ ρ), ENNReal.ofReal_mul h1E,
    mul_left_comm, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1/2),
    ENNReal.ofReal_rpow_of_nonneg h1E (by norm_num), ← Real.sqrt_eq_rpow]

theorem one_le_root {E : ℝ} (hE : 0 ≤ E) : 1 ≤ ENNReal.ofReal (Real.sqrt (1 + E)) :=
  ENNReal.one_le_ofReal.2 (Real.one_le_sqrt.2 (by linarith))

/-- `Q ≤ √(1 + E_κ) Q⁰`. -/
theorem closedQuantile_le_root_quantileZero (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (B : ℝ) :
    closedQuantileValue μ ρ B ≤
      ENNReal.ofReal (Real.sqrt (1 + coreEntropy μ ρ)) * quantileZero μ ρ B := by
  have hs := one_le_root (core_entropy μ ρ hρ hρ4).2.2.1
  rw [closedQuantile_eq μ hρ (by linarith) B, core_root μ hρ hρ4]
  unfold quantileZero
  rcases le_total (ENNReal.ofReal ρ)
      (ThresholdHC.EntropyTail.tailCost (quantileTail μ ρ) (1 / Real.sqrt B) +
        ENNReal.ofReal (1 / Real.sqrt B) *
          (ENNReal.ofReal ρ * inverseSquareCost (quantileCore μ ρ)) ^ (1/2 : ℝ)) with hle | hle
  · rw [min_eq_left hle]
    exact (min_le_left _ _).trans (le_mul_of_one_le_left' hs)
  · rw [min_eq_right hle]
    refine (min_le_right _ _).trans ?_
    rw [mul_add]
    exact add_le_add (le_mul_of_one_le_left' hs) (le_of_eq (by ring))

theorem sqrt_two_mul (E : ℝ) :
    Real.sqrt (2 * (1 + E)) = Real.sqrt (1 + E) * Real.sqrt 2 := by
  rw [Real.sqrt_mul (by norm_num), mul_comm]

/-- `Q ≤ √(2 (1 + E_κ)) Ψ`. -/
theorem closedQuantile_le_root_psi (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) :
    closedQuantileValue μ ρ B ≤
      ENNReal.ofReal (Real.sqrt (2 * (1 + coreEntropy μ ρ))) *
        rarePsi μ ρ (1 / Real.sqrt B) := by
  rw [sqrt_two_mul, ENNReal.ofReal_mul (Real.sqrt_nonneg _), mul_assoc]
  exact (closedQuantile_le_root_quantileZero μ hρ hρ4 B).trans
    (mul_le_mul_right (psi_closed_form μ ρ B hρ hρ4 hB).1 _)

theorem psi_gap : PsiGapStatement := by
  intro μ _ ρ B hρ hρ4 hB
  exact ⟨ThresholdHC.PsiSelection.psi_le_selection μ ρ B hB,
    (ThresholdHC.EntropyTail.selection_quantile_comparison μ hρ hρ4 hB).1,
    closedQuantile_le_root_quantileZero μ hρ hρ4 B, closedQuantile_le_root_psi μ hρ hρ4 hB⟩

theorem psi_gap_risk : PsiGapRiskStatement := by
  intro μ _ ρ B hρ hρ4 hB
  refine ⟨ThresholdHC.PsiSelection.psi_risk_lower μ ρ B hρ hρ4 hB, ?_⟩
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 30001), mul_assoc]
  exact (ThresholdHC.EntropyTailExecution.closed_quantile_upper_30001 μ hρ hρ4 hB).trans
    (mul_le_mul_right (closedQuantile_le_root_psi μ hρ hρ4 hB) _)

theorem psi_gap_reverse : PsiGapReverseStatement := by
  intro μ _ ρ B hρ hρ4 hB htail hcap
  have hE := (core_entropy μ ρ hρ hρ4).2.2.1
  have hQ : closedQuantileValue μ ρ B =
      ThresholdHC.EntropyTail.tailCost (quantileTail μ ρ) (1 / Real.sqrt B) +
        ENNReal.ofReal (1 / Real.sqrt B) *
          (ENNReal.ofReal ρ * measureCostEntropy (quantileCore μ ρ)) ^ (1/2 : ℝ) := by
    rw [closedQuantile_eq μ hρ (by linarith) B, min_eq_right hcap]
  have hhalf : ENNReal.ofReal (Real.sqrt (1 + coreEntropy μ ρ)) =
      ENNReal.ofReal (Real.sqrt (1 + coreEntropy μ ρ) / 2) +
        ENNReal.ofReal (Real.sqrt (1 + coreEntropy μ ρ) / 2) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  have hfirst : ENNReal.ofReal (Real.sqrt (1 + coreEntropy μ ρ) / 2) * quantileZero μ ρ B ≤
      closedQuantileValue μ ρ B := by
    rw [hQ, core_root μ hρ hρ4]
    unfold quantileZero
    calc ENNReal.ofReal (Real.sqrt (1 + coreEntropy μ ρ) / 2) *
          min (ENNReal.ofReal ρ)
            (ThresholdHC.EntropyTail.tailCost (quantileTail μ ρ) (1 / Real.sqrt B) +
              ENNReal.ofReal (1 / Real.sqrt B) *
                (ENNReal.ofReal ρ * inverseSquareCost (quantileCore μ ρ)) ^ (1/2 : ℝ))
        ≤ ENNReal.ofReal (Real.sqrt (1 + coreEntropy μ ρ) / 2) *
            (ENNReal.ofReal (1 / Real.sqrt B) *
                (ENNReal.ofReal ρ * inverseSquareCost (quantileCore μ ρ)) ^ (1/2 : ℝ) +
              ENNReal.ofReal (1 / Real.sqrt B) *
                (ENNReal.ofReal ρ * inverseSquareCost (quantileCore μ ρ)) ^ (1/2 : ℝ)) :=
          mul_le_mul_right ((min_le_right _ _).trans (add_le_add htail le_rfl)) _
      _ = ENNReal.ofReal (1 / Real.sqrt B) *
            (ENNReal.ofReal (Real.sqrt (1 + coreEntropy μ ρ)) *
              (ENNReal.ofReal ρ * inverseSquareCost (quantileCore μ ρ)) ^ (1/2 : ℝ)) := by
          rw [hhalf]; ring
      _ ≤ _ := le_add_self
  refine ⟨hfirst, ?_⟩
  have hpsi : rarePsi μ ρ (1 / Real.sqrt B) ≤ quantileZero μ ρ B :=
    (psi_closed_form μ ρ B hρ hρ4 hB).2.1.trans (psi_closed_form μ ρ B hρ hρ4 hB).2.2
  rw [ENNReal.ofReal_mul (by positivity), mul_assoc]
  exact (mul_le_mul_right ((mul_le_mul_right hpsi _).trans hfirst) _).trans
    (ThresholdHC.EntropyTailSharp.closed_quantile_lower_explicit μ hρ hρ4 hB)

end ThresholdHC.PsiGap
