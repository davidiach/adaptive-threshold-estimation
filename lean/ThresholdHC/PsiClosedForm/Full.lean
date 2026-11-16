import ThresholdHC.PsiClosedForm.Lower

/-! The closed form of `Ψ` (v6 Proposition 14.9) against the locked
statements: the comparisons after (W1), the chain (W2), and the regime in
which the resolution is at least the quantile threshold. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.PsiClosedForm
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.EntropyTail
open ThresholdHC.EntropyTailQuantile (quantileTail quantileCore quantileThreshold
  quantileTail_le quantileTail_mass quantileTail_add_core quantileTail_support
  quantileCore_support)

/-- The optimizer's allocation is feasible, so its objective is at most `Ψ`. -/
theorem allocation_le_rarePsi (μ : Measure Gap) {ρ h c : ℝ}
    (hfeas : Tier3.FeasibleAllocation μ ρ (fun d : Gap => Tier3.allocation c (d : ℝ))) :
    ENNReal.ofReal (Tier3.rareObjective μ (fun d : Gap => (d : ℝ)) h
      (fun d : Gap => Tier3.allocation c (d : ℝ))) ≤ rarePsi μ ρ h := by
  unfold rarePsi
  exact le_iSup₂ (f := fun (v : Gap → ℝ) (_ : Tier3.FeasibleAllocation μ ρ v) =>
    ENNReal.ofReal (Tier3.rareObjective μ (fun d : Gap => (d : ℝ)) h v)) _ hfeas

/-- `min{ρ, T_h + h√(ρ A_κ)} ≤ √2 Ψ_{μ,ρ}(h)` at every positive resolution. -/
theorem quantile_form_le (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ h : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hh : 0 < h) :
    min (ENNReal.ofReal ρ)
        (tailCost (quantileTail μ ρ) h +
          ENNReal.ofReal h *
            (ENNReal.ofReal ρ * inverseSquareCost (quantileCore μ ρ)) ^ (1/2 : ℝ)) ≤
      ENNReal.ofReal (Real.sqrt 2) * rarePsi μ ρ h := by
  obtain ⟨c, hc, -, hm, -, hfeas, hopt⟩ :=
    Tier3.arbitrary_law_optimizer Gap μ (fun d : Gap => (d : ℝ)) ρ measurable_subtype_coe
      (Filter.Eventually.of_forall fun d => d.2) hρ hρ1
  have hν : IsFiniteMeasure (quantileTail μ ρ) :=
    isFiniteMeasure_of_le μ (quantileTail_le μ hρ hρ1.le)
  have hκ : IsFiniteMeasure (quantileCore μ ρ) :=
    isFiniteMeasure_of_le μ (quantileCore_le μ ρ)
  have hadd := quantileTail_add_core μ hρ hρ1.le
  have hmass := quantileTail_mass μ hρ hρ1.le
  have h2 : 1 ≤ Real.sqrt 2 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by norm_num)
  refine le_trans ?_ (mul_le_mul_right (allocation_le_rarePsi μ hfeas) _)
  rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg 2)]
  rcases le_or_gt c h with hch | hhc
  · rw [(hopt h hh).2.1 hch]
    exact (min_le_left _ _).trans (ENNReal.ofReal_le_ofReal (by nlinarith))
  · have hct : c < quantileThreshold μ ρ :=
      cutoff_lt_threshold μ (quantileTail μ ρ) (quantileCore μ ρ) hρ hρ1 hc hadd hmass
        (quantileTail_support μ ρ) hm
    have hκc : ∀ᵐ d : Gap ∂quantileCore μ ρ, c < (d : ℝ) :=
      (quantileCore_support μ ρ).mono fun d hd => hct.trans_le hd
    obtain ⟨w, hw, hA, hmain⟩ :=
      closed_form_real μ (quantileTail μ ρ) (quantileCore μ ρ) hρ hh hhc hadd hmass hκc hm
    refine (min_le_right _ _).trans ?_
    have hT : tailCost (quantileTail μ ρ) h =
        ENNReal.ofReal (∫ d, tailKernel h d ∂quantileTail μ ρ) :=
      (quantile_tailModulus_eq (quantileTail μ ρ) hh.le).symm
    have hT0 : 0 ≤ ∫ d, tailKernel h d ∂quantileTail μ ρ :=
      integral_nonneg (tailKernel_nonneg hh.le)
    have hroot : Real.sqrt (ρ * (w / c ^ 2)) = Real.sqrt (ρ * w) / c := by
      rw [← mul_div_assoc, Real.sqrt_div' _ (sq_nonneg c), Real.sqrt_sq hc.le]
    have hprod : 0 ≤ ρ * (w / c ^ 2) := mul_nonneg hρ.le (div_nonneg hw (sq_nonneg c))
    rw [hA, hT, ← ENNReal.ofReal_mul hρ.le, ENNReal.ofReal_rpow_of_nonneg hprod (by norm_num),
      ← Real.sqrt_eq_rpow, hroot, ← ENNReal.ofReal_mul hh.le,
      ← ENNReal.ofReal_add hT0 (mul_nonneg hh.le (div_nonneg (Real.sqrt_nonneg _) hc.le))]
    refine ENNReal.ofReal_le_ofReal (le_trans (le_of_eq ?_) hmain)
    ring

theorem entropy_free_order : EntropyFreeOrderStatement := by
  intro μ _ ρ B hρ hρ4 _
  have hρ1 : ρ ≤ 1 := by linarith
  exact ⟨selectionZero_le_selection μ ρ B, quantileZero_le_closedQuantile μ hρ hρ1 B,
    selectionZero_le_quantileZero μ hρ hρ1 B⟩

theorem psi_closed_form : PsiClosedFormStatement := by
  intro μ _ ρ B hρ hρ4 hB
  have hρ1 : ρ ≤ 1 := by linarith
  have hh : 0 < 1 / Real.sqrt B := by positivity
  exact ⟨quantile_form_le μ hρ (by linarith) hh, rarePsi_le_selectionZero μ ρ hB,
    selectionZero_le_quantileZero μ hρ hρ1 B⟩

theorem psi_trivial_regime : PsiTrivialRegimeStatement := by
  intro μ _ ρ B hρ hρ4 hB hth
  have hρ1 : ρ < 1 := by linarith
  have hh : 0 < 1 / Real.sqrt B := by positivity
  obtain ⟨c, hc, -, hm, -, hfeas, hopt⟩ :=
    Tier3.arbitrary_law_optimizer Gap μ (fun d : Gap => (d : ℝ)) ρ measurable_subtype_coe
      (Filter.Eventually.of_forall fun d => d.2) hρ hρ1
  have hν : IsFiniteMeasure (quantileTail μ ρ) :=
    isFiniteMeasure_of_le μ (quantileTail_le μ hρ hρ1.le)
  have hκ : IsFiniteMeasure (quantileCore μ ρ) :=
    isFiniteMeasure_of_le μ (quantileCore_le μ ρ)
  have hmass := quantileTail_mass μ hρ hρ1.le
  have hct : c < quantileThreshold μ ρ :=
    cutoff_lt_threshold μ (quantileTail μ ρ) (quantileCore μ ρ) hρ hρ1 hc
      (quantileTail_add_core μ hρ hρ1.le) hmass (quantileTail_support μ ρ) hm
  constructor
  · refine le_antisymm ?_ ?_
    · unfold rarePsi
      exact iSup₂_le fun v hv => (ThresholdHC.PsiSelection.rareObjective_le μ hh hv).1
    · have := allocation_le_rarePsi (h := 1 / Real.sqrt B) μ hfeas
      rwa [(hopt _ hh).2.1 (hct.le.trans hth)] at this
  · unfold quantileZero
    apply min_eq_left
    have hT : tailCost (quantileTail μ ρ) (1 / Real.sqrt B) = ENNReal.ofReal ρ := by
      unfold tailCost
      have hcongr : ∫⁻ d : Gap, ENNReal.ofReal (min 1 (1 / Real.sqrt B / (d : ℝ)))
          ∂quantileTail μ ρ = ∫⁻ _d : Gap, 1 ∂quantileTail μ ρ :=
        lintegral_congr_ae ((quantileTail_support μ ρ).mono fun d hd => by
          show ENNReal.ofReal (min 1 (1 / Real.sqrt B / (d : ℝ))) = 1
          rw [min_eq_left ((one_le_div d.2.1).2 (hd.trans hth)), ENNReal.ofReal_one])
      rw [hcongr, lintegral_one, hmass]
    rw [hT]
    exact le_self_add

end ThresholdHC.PsiClosedForm
