import ThresholdHC.ZeroAtomSplit.Specification

/-! The zero-atom split of the selection functional.

A selection that charges zero has infinite entropy, so only selections below the
positive part count. Adding a zero atom of mass `z` adds `z` to each of their
objectives, through the tail weight one at zero. Scaling a gap law by `c > 0`
scales each objective by `c` and divides the rarity by `c`, since
`√(ρ c Γ) = c √((ρ/c) Γ)`. Together, with `c = 1 - z`,

  `K_{zδ₀+(1-z)η,ρ} = min{ρ, z + K_{(1-z)η,ρ}} = min{ρ, z + (1 - z) K_{η,ρ/(1-z)}}`. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.ZeroAtomSplit
open ThresholdHC.ArbitraryLawAdaptation ThresholdHC.EntropyTail
open ThresholdHC.Tier6 (Gap)

/-- Adding a zero atom of mass `z` to the law adds `z` to the objective of
every selection below the original law. -/
theorem zeroObjective_add_zeroAtom {ν σ : Measure ℝ} [IsFiniteMeasure ν] (hσ : σ ≤ ν)
    (z ρ B : ℝ) :
    zeroObjective (ENNReal.ofReal z • Measure.dirac 0 + ν) ρ B σ =
      ENNReal.ofReal z + zeroObjective ν ρ B σ := by
  have : IsFiniteMeasure σ := isFiniteMeasure_of_le ν hσ
  have hres : ENNReal.ofReal z • Measure.dirac 0 + ν - σ =
      ENNReal.ofReal z • Measure.dirac 0 + (ν - σ) := by
    have he : ENNReal.ofReal z • Measure.dirac 0 + (ν - σ) + σ =
        ENNReal.ofReal z • Measure.dirac 0 + ν := by
      rw [add_assoc, Measure.sub_add_cancel_of_le hσ]
    rw [← he, Measure.add_sub_cancel]
  unfold zeroObjective
  rw [hres, zeroTailCost_add, zeroTailCost_smul, zeroTailCost_dirac_zero, mul_one]
  ring

/-- A selection below `z δ₀ + ν` with no mass at zero lies below `ν`. -/
theorem le_of_le_zeroAtom_add {ν σ : Measure ℝ} {z : ℝ}
    (hσ : σ ≤ ENNReal.ofReal z • Measure.dirac 0 + ν) (h0 : σ {0} = 0) : σ ≤ ν := by
  refine Measure.le_iff.mpr fun s hs => ?_
  have hs0 : MeasurableSet (s \ {0}) := hs.diff (measurableSet_singleton 0)
  calc σ s = σ (s \ {0}) := (measure_sdiff_null h0).symm
    _ ≤ (ENNReal.ofReal z • Measure.dirac 0 + ν : Measure ℝ) (s \ {0}) := hσ _
    _ = ν (s \ {0}) := by
        have h0s : (0 : ℝ) ∉ s \ {0} := fun h => h.2 rfl
        rw [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ hs0,
          Set.indicator_of_notMem h0s, smul_eq_mul, mul_zero, zero_add]
    _ ≤ ν s := measure_mono Set.sdiff_subset

/-- A selection that charges zero has infinite objective. -/
theorem zeroObjective_eq_top {μ σ : Measure ℝ} (hs : σ {0} ≠ 0) {ρ B : ℝ} (hρ : 0 < ρ)
    (hB : 0 < B) : zeroObjective μ ρ B σ = ∞ := by
  have hh : 0 < 1 / Real.sqrt B := by positivity
  unfold zeroObjective
  rw [zeroGamma_of_atom hs, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hρ).ne',
    ENNReal.top_rpow_of_pos (by norm_num), ENNReal.mul_top (ENNReal.ofReal_pos.mpr hh).ne',
    top_add]

/-- Adding a zero atom of mass `z` to a finite law `ν`:
`K_{zδ₀+ν,ρ} = min{ρ, z + K_{ν,ρ}}`. -/
theorem zeroSelection_add_zeroAtom (ν : Measure ℝ) [IsFiniteMeasure ν] {z ρ B : ℝ}
    (hρ : 0 < ρ) (hB : 0 < B) :
    zeroSelection (ENNReal.ofReal z • Measure.dirac 0 + ν) ρ B =
      min (ENNReal.ofReal ρ) (ENNReal.ofReal z + zeroSelection ν ρ B) := by
  apply le_antisymm
  · refine le_min (min_le_left _ _) ?_
    have hY : zeroSelection (ENNReal.ofReal z • Measure.dirac 0 + ν) ρ B ≤
        ENNReal.ofReal z + ⨅ (σ : Measure ℝ) (_ : σ ≤ ν), zeroObjective ν ρ B σ := by
      rw [ENNReal.add_iInf]
      refine le_iInf fun σ => ?_
      rw [ENNReal.add_iInf]
      refine le_iInf fun hσ => ?_
      exact (min_le_right _ _).trans ((iInf₂_le σ (Measure.le_add_left hσ)).trans_eq
        (zeroObjective_add_zeroAtom hσ z ρ B))
    calc zeroSelection (ENNReal.ofReal z • Measure.dirac 0 + ν) ρ B
        ≤ min (ENNReal.ofReal z + ENNReal.ofReal ρ)
            (ENNReal.ofReal z + ⨅ (σ : Measure ℝ) (_ : σ ≤ ν), zeroObjective ν ρ B σ) :=
          le_min ((min_le_left _ _).trans le_add_self) hY
      _ = ENNReal.ofReal z + zeroSelection ν ρ B := by
          rw [min_add_add_left]
          rfl
  · refine le_min (min_le_left _ _) (le_iInf₂ fun σ hσ => ?_)
    by_cases h0 : σ {0} = 0
    · have hν := le_of_le_zeroAtom_add hσ h0
      rw [zeroObjective_add_zeroAtom hν]
      exact (min_le_right _ _).trans
        (add_le_add le_rfl ((min_le_right _ _).trans (iInf₂_le σ hν)))
    · rw [zeroObjective_eq_top h0 hρ hB]
      exact le_top

/-- Scaling a selection scales the objective and divides the rarity:
`J_{cη,ρ}(cτ) = c J_{η,ρ/c}(τ)` for `τ ≤ η`, `c > 0` and `ρ ≥ 0`. -/
theorem selectionObjective_smul {η τ : Measure Gap} [IsFiniteMeasure η] (hτ : τ ≤ η)
    {c ρ : ℝ} (hc : 0 < c) (hρ : 0 ≤ ρ) (B : ℝ) :
    selectionObjective (ENNReal.ofReal c • η) ρ B (ENNReal.ofReal c • τ) =
      ENNReal.ofReal c * selectionObjective η (ρ / c) B τ := by
  have : IsFiniteMeasure τ := isFiniteMeasure_of_le η hτ
  have : IsFiniteMeasure (ENNReal.ofReal c • τ) := τ.smul_finite ENNReal.ofReal_ne_top
  have hres : ENNReal.ofReal c • η - ENNReal.ofReal c • τ =
      ENNReal.ofReal c • (η - τ) := by
    have he : ENNReal.ofReal c • (η - τ) + ENNReal.ofReal c • τ =
        ENNReal.ofReal c • η := by
      rw [← smul_add, Measure.sub_add_cancel_of_le hτ]
    rw [← he, Measure.add_sub_cancel]
  have hsq : ENNReal.ofReal c = (ENNReal.ofReal (c ^ 2)) ^ (1 / 2 : ℝ) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow,
      Real.sqrt_sq hc.le]
  have hkey : ENNReal.ofReal ρ * (ENNReal.ofReal c * gamma τ) =
      ENNReal.ofReal (c ^ 2) * (ENNReal.ofReal (ρ / c) * gamma τ) := by
    rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul hρ,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    rw [sq, mul_assoc, mul_div_cancel₀ _ hc.ne', mul_comm]
  unfold selectionObjective
  rw [canonicalGamma_smul τ hc.le, hres, tailCost_smul, mul_add, hkey,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← hsq]
  ring

/-- Scaling a gap law by `c > 0` scales the functional and divides the rarity:
`K_{cη,ρ} = c K_{η,ρ/c}` for `ρ ≥ 0`. -/
theorem selection_smul (η : Measure Gap) [IsFiniteMeasure η] {c ρ : ℝ} (hc : 0 < c)
    (hρ : 0 ≤ ρ) (B : ℝ) :
    selection (ENNReal.ofReal c • η) ρ B = ENNReal.ofReal c * selection η (ρ / c) B := by
  have hcne : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.mpr hc).ne'
  apply le_antisymm
  · unfold selection
    rw [mul_min, ← ENNReal.ofReal_mul hc.le, mul_div_cancel₀ _ hc.ne']
    refine min_le_min le_rfl ?_
    rw [ENNReal.mul_iInf_of_ne hcne ENNReal.ofReal_ne_top]
    refine le_iInf fun τ => ?_
    rw [ENNReal.mul_iInf_of_ne hcne ENNReal.ofReal_ne_top]
    refine le_iInf fun hτ => ?_
    rw [← selectionObjective_smul hτ hc hρ B]
    apply iInf₂_le
    exact smul_le_smul_left _ hτ
  · exact smul_selection_le η hc (div_nonneg hρ hc.le) (by rw [mul_div_cancel₀ _ hc.ne'])

/-- The zero-atom split for a finite gap law `η` and `z < 1`:
`K_{zδ₀+(1-z)η,ρ} = min{ρ, z + (1 - z) K_{η,ρ/(1-z)}}`. -/
theorem zeroSelection_zeroAtomLaw (η : Measure Gap) [IsFiniteMeasure η] {z ρ B : ℝ}
    (hz1 : z < 1) (hρ : 0 < ρ) (hB : 0 < B) :
    zeroSelection (zeroAtomLaw z η) ρ B =
      min (ENNReal.ofReal ρ)
        (ENNReal.ofReal z + ENNReal.ofReal (1 - z) * selection η (ρ / (1 - z)) B) := by
  have hc : 0 < 1 - z := by linarith
  have : IsFiniteMeasure (ENNReal.ofReal (1 - z) • η) := η.smul_finite ENNReal.ofReal_ne_top
  have hα : zeroAtomLaw z η =
      ENNReal.ofReal z • Measure.dirac 0 + (ENNReal.ofReal (1 - z) • η).map Subtype.val := by
    rw [map_val_smul]
    rfl
  rw [hα, zeroSelection_add_zeroAtom _ hρ hB, zeroSelection_map, selection_smul η hc hρ.le]

end ThresholdHC.ZeroAtomSplit
