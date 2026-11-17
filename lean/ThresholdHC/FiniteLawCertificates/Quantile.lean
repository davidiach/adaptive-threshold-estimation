import ThresholdHC.FiniteLawCertificates.Atomic
import ThresholdHC.EntropyTailQuantile.CutDecomposition

/-! Finite rational data connected to the original measure-level definitions. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal Classical
namespace ThresholdHC.FiniteLawCertificates
open ThresholdHC.Tier6

theorem quantileThreshold_eq_of_mass (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ t : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hbelow : μ.real {x : Gap | (x:ℝ) < t} < ρ)
    (habove : ρ ≤ μ.real {x : Gap | (x:ℝ) ≤ t}) :
    ThresholdHC.EntropyTailQuantile.quantileThreshold μ ρ = t := by
  have hp := ThresholdHC.EntropyTailQuantile.quantileThreshold_properties μ hρ hρ1
  apply le_antisymm
  · by_contra h
    exact (not_lt_of_ge habove) (hp.2.2.2 t (lt_of_not_ge h))
  · by_contra h
    have ht : ThresholdHC.EntropyTailQuantile.quantileThreshold μ ρ < t := lt_of_not_ge h
    have hm : μ.real {x : Gap | (x:ℝ) ≤ ThresholdHC.EntropyTailQuantile.quantileThreshold μ ρ} ≤
        μ.real {x : Gap | (x:ℝ) < t} :=
      measureReal_mono (fun x hx => hx.trans_lt ht)
    exact (not_le_of_gt hbelow) (hp.2.2.1.trans hm)

theorem quantileCore_atomic {n : ℕ} (d : Fin n → Gap) (w s : Fin n → ℚ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    {ρ t : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : ℚ) (hr : r ≤ 1)
    (hbelow : (∑ i, if (d i:ℝ) < t then (w i:ℝ) else 0) < ρ)
    (habove : ρ ≤ ∑ i, if (d i:ℝ) ≤ t then (w i:ℝ) else 0)
    (hboundary : (r:ℝ) =
      (ρ-(∑ i, if (d i:ℝ) < t then (w i:ℝ) else 0)) /
        (∑ i, if (d i:ℝ) = t then (w i:ℝ) else 0))
    (hs : ∀ i, s i = if (d i:ℝ) < t then 0 else if (d i:ℝ) = t then 1-r else 1) :
    ThresholdHC.EntropyTailQuantile.quantileCore (atomicMeasure d w) ρ =
      atomicMeasure d (fun i => w i*s i) := by
  let := atomicMeasure_probability d w hw hsum
  have ht : ThresholdHC.EntropyTailQuantile.quantileThreshold (atomicMeasure d w) ρ = t := by
    apply quantileThreshold_eq_of_mass _ hρ hρ1
    · simpa only [atomicMeasure_real d w hw, Set.mem_ofPred_eq] using hbelow
    · simpa only [atomicMeasure_real d w hw, Set.mem_ofPred_eq] using habove
  have hb : ThresholdHC.EntropyTailQuantile.quantileBoundaryFraction (atomicMeasure d w) ρ = (r:ℝ) := by
    simpa only [ThresholdHC.EntropyTailQuantile.quantileBoundaryFraction, ht,
      atomicMeasure_real d w hw, Set.mem_ofPred_eq] using hboundary.symm
  have hpos (i : Fin n) : 0 ≤ (if t < (d i:ℝ) then w i else 0) := by
    split_ifs <;> simp_all
  have heq (i : Fin n) : 0 ≤ (1-r)*(if (d i:ℝ) = t then w i else 0) :=
    mul_nonneg (sub_nonneg.mpr hr) (by split_ifs <;> simp_all)
  rw [ThresholdHC.EntropyTailQuantile.quantileCore_eq_upperCut _ hρ hρ1, ht, hb,
    ThresholdHC.EntropyTailQuantile.upperCut, atomicMeasure_restrict, atomicMeasure_restrict]
  have hc : (1-(r:ℝ)) = ((1-r:ℚ):ℝ) := by push_cast; rfl
  rw [hc, ← atomicMeasure_smul d _ (1-r) (sub_nonneg.mpr hr)]
  simp only [Set.mem_ofPred_eq]
  rw [← atomicMeasure_add d _ _ hpos heq]
  congr 1
  funext i
  rw [hs i]
  rcases lt_trichotomy (d i:ℝ) t with hi | hi | hi
  · simp [hi, hi.ne, not_lt_of_ge hi.le]
  · simp [hi]
    ring
  · simp [hi, hi.ne', not_lt_of_ge hi.le]

end ThresholdHC.FiniteLawCertificates
