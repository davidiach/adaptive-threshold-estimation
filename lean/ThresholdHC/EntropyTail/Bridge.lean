import ThresholdHC.EntropyTail.Model
import ThresholdHC.EntropyTailQuantile.MeasureEntropy
import ThresholdHC.EntropyTailQuantile.TailModulus

/-! Bridge from the quantile development's selection functional
`ThresholdHC.EntropyTailQuantile.selectionValue` to the locked functional
`selection` of this specification. Both use the canonical dyadic bands, the
homogeneous cost entropy of the band costs with its prefix supremum, and the
truncated tail cost at `h = B^{-1/2}`. The quantile development writes band
and tail costs as Bochner integrals and the entropy with `negMulLog`; here
those forms are compared with the extended-real integrals of the
specification. The quantile functional is at most `selection` for every
measure, and the two are equal for every finite measure, in particular for
every probability law. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.EntropyTail
open ThresholdHC.Tier6

/-- The two descriptions of the canonical band `(2^{-(j+2)}, 2^{-(j+1)}]` agree. -/
theorem quantile_band_eq (j : ℕ) : ThresholdHC.EntropyTailQuantile.band j = band j := by
  have e₁ : ThresholdHC.EntropyTailQuantile.bandEdge j / 2 = (1/2 : ℝ)^(j+2) := by
    unfold ThresholdHC.EntropyTailQuantile.bandEdge
    ring
  have e₂ : ThresholdHC.EntropyTailQuantile.bandEdge j = (1/2 : ℝ)^(j+1) := by
    unfold ThresholdHC.EntropyTailQuantile.bandEdge
    ring
  ext d
  simp only [ThresholdHC.EntropyTailQuantile.band, band, Set.mem_setOf_eq]
  rw [e₁, e₂]

/-- The Bochner band cost is the real value of the extended band cost. -/
theorem quantile_bandCost_eq (σ : Measure Gap) (j : ℕ) :
    ThresholdHC.EntropyTailQuantile.bandCost σ j = (bandCost σ j).toReal := by
  unfold ThresholdHC.EntropyTailQuantile.bandCost bandCost
  rw [quantile_band_eq j]
  have h0 : 0 ≤ᵐ[σ.restrict (band j)] fun d : Gap => (d:ℝ)⁻¹ ^ 2 :=
    Filter.Eventually.of_forall (fun d => sq_nonneg _)
  have hm : AEStronglyMeasurable (fun d : Gap => (d:ℝ)⁻¹ ^ 2) (σ.restrict (band j)) := by
    fun_prop
  exact integral_eq_lintegral_of_nonneg_ae h0 hm

/-- On a finite measure every band cost is finite. -/
theorem quantile_bandCost_lt_top (σ : Measure Gap) [IsFiniteMeasure σ] (j : ℕ) :
    bandCost σ j < ∞ := by
  have hint : IntegrableOn (fun d : Gap => (d:ℝ)⁻¹ ^ 2) (band j) σ := by
    rw [← quantile_band_eq j]
    exact ThresholdHC.EntropyTailQuantile.band_inverseSquare_integrable σ j
  unfold bandCost
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall (fun d => sq_nonneg _))]
  exact ENNReal.ofReal_lt_top

/-- The two formulas for the homogeneous cost entropy agree on nonnegative vectors. -/
theorem quantile_costEntropy_eq {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ThresholdHC.EntropyTailQuantile.costEntropy a = costEntropy a := by
  rw [ThresholdHC.EntropyTailQuantile.costEntropy_eq_log_sum ha]
  rfl

/-- Each finite prefix of the two cost entropies agrees. -/
theorem quantile_prefix_eq (σ : Measure Gap) (n : ℕ) :
    ThresholdHC.EntropyTailQuantile.costEntropy
        (fun j : Fin n => ThresholdHC.EntropyTailQuantile.bandCost σ j.val) =
      costEntropy (fun j : Fin n => (bandCost σ j).toReal) := by
  rw [quantile_costEntropy_eq _ (fun i => ThresholdHC.EntropyTailQuantile.bandCost_nonneg σ i.val)]
  simp only [quantile_bandCost_eq]

/-- The quantile development's cost entropy is at most `Γ_σ`, which is infinite
whenever some band cost is. -/
theorem quantile_measureCostEntropy_le (σ : Measure Gap) :
    ThresholdHC.EntropyTailQuantile.measureCostEntropy σ ≤ gamma σ := by
  unfold ThresholdHC.EntropyTailQuantile.measureCostEntropy
  refine iSup_le fun n => ?_
  cases n with
  | zero =>
    simp [ThresholdHC.EntropyTailQuantile.costEntropy, ThresholdHC.EntropyTailQuantile.costTotal]
  | succ J =>
    unfold gamma
    refine le_iSup_of_le J ?_
    split_ifs with h
    · exact ENNReal.ofReal_le_ofReal (le_of_eq (quantile_prefix_eq σ (J+1)))
    · exact le_top

/-- On a finite measure, `Γ_σ` is at most the quantile development's cost entropy. -/
theorem gamma_le_quantile_measureCostEntropy (σ : Measure Gap) [IsFiniteMeasure σ] :
    gamma σ ≤ ThresholdHC.EntropyTailQuantile.measureCostEntropy σ := by
  unfold gamma ThresholdHC.EntropyTailQuantile.measureCostEntropy
  refine iSup_le fun J => ?_
  split_ifs with h
  · exact le_iSup_of_le (J+1)
      (ENNReal.ofReal_le_ofReal (le_of_eq (quantile_prefix_eq σ (J+1)).symm))
  · exact (h fun j => (quantile_bandCost_lt_top σ j).ne).elim

/-- The real tail modulus is at most the extended tail cost. -/
theorem quantile_tailModulus_le (ν : Measure Gap) {h : ℝ} (hh : 0 ≤ h) :
    ENNReal.ofReal (ThresholdHC.EntropyTailQuantile.tailModulus ν h) ≤ tailCost ν h := by
  unfold ThresholdHC.EntropyTailQuantile.tailModulus tailCost
  have h0 : 0 ≤ᵐ[ν] fun d : Gap => min 1 (h / (d:ℝ)) :=
    Filter.Eventually.of_forall (ThresholdHC.EntropyTailQuantile.tailKernel_nonneg hh)
  have hm : AEStronglyMeasurable (fun d : Gap => min 1 (h / (d:ℝ))) ν :=
    (measurable_const.min (measurable_const.div measurable_subtype_coe)).aestronglyMeasurable
  rw [integral_eq_lintegral_of_nonneg_ae h0 hm]
  exact ENNReal.ofReal_toReal_le

/-- On a finite measure the real tail modulus equals the extended tail cost. -/
theorem quantile_tailModulus_eq (ν : Measure Gap) [IsFiniteMeasure ν] {h : ℝ} (hh : 0 ≤ h) :
    ENNReal.ofReal (ThresholdHC.EntropyTailQuantile.tailModulus ν h) = tailCost ν h := by
  unfold ThresholdHC.EntropyTailQuantile.tailModulus tailCost
  exact ofReal_integral_eq_lintegral_ofReal
    (ThresholdHC.EntropyTailQuantile.tailKernel_integrable ν hh)
    (Filter.Eventually.of_forall (ThresholdHC.EntropyTailQuantile.tailKernel_nonneg hh))

/-- The quantile development's selection functional is at most the locked one. -/
theorem quantile_selectionValue_le (μ : Measure Gap) (ρ B : ℝ) :
    ThresholdHC.EntropyTailQuantile.selectionValue μ ρ B ≤ selection μ ρ B := by
  unfold ThresholdHC.EntropyTailQuantile.selectionValue selection
  refine min_le_min le_rfl (iInf₂_mono fun σ _ => ?_)
  have hh : (0:ℝ) ≤ (Real.sqrt B)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg B)
  unfold ThresholdHC.EntropyTailQuantile.selectionCost ThresholdHC.EntropyTailQuantile.budgetScale
    selectionObjective
  rw [one_div (Real.sqrt B)]
  exact add_le_add
    (mul_le_mul_right (ENNReal.rpow_le_rpow
      (mul_le_mul_right (quantile_measureCostEntropy_le σ) _) (by norm_num)) _)
    (quantile_tailModulus_le (μ - σ) hh)

/-- For every finite law the two selection functionals coincide. -/
theorem quantile_selectionValue_eq (μ : Measure Gap) [IsFiniteMeasure μ] (ρ B : ℝ) :
    ThresholdHC.EntropyTailQuantile.selectionValue μ ρ B = selection μ ρ B := by
  refine le_antisymm (quantile_selectionValue_le μ ρ B) ?_
  unfold ThresholdHC.EntropyTailQuantile.selectionValue selection
  refine min_le_min le_rfl (iInf₂_mono fun σ hσ => ?_)
  have : IsFiniteMeasure σ := isFiniteMeasure_of_le μ hσ
  have : IsFiniteMeasure (μ - σ) := isFiniteMeasure_of_le μ Measure.sub_le
  have hh : (0:ℝ) ≤ (Real.sqrt B)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg B)
  unfold ThresholdHC.EntropyTailQuantile.selectionCost ThresholdHC.EntropyTailQuantile.budgetScale
    selectionObjective
  rw [one_div (Real.sqrt B), quantile_tailModulus_eq (μ - σ) hh]
  exact add_le_add
    (mul_le_mul_right (ENNReal.rpow_le_rpow
      (mul_le_mul_right (gamma_le_quantile_measureCostEntropy σ) _) (by norm_num)) _)
    le_rfl

end ThresholdHC.EntropyTail
