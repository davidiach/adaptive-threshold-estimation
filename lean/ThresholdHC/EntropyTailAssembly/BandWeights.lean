import ThresholdHC.EntropyTail.ScaleSeparated
import ThresholdHC.EntropyTail.EntropyMoment
import ThresholdHC.EntropyTailUpper.BankWork

/-! Finite active-band normalization for a selected submeasure supported away
from zero. The remaining general-law approximation will use these banks. -/

noncomputable section
open MeasureTheory Set Real
open scoped NNReal ENNReal BigOperators

namespace ThresholdHC.EntropyTailAssembly
open ThresholdHC.Tier6 ThresholdHC.EntropyTail

theorem inverseSquare_integrable_of_support (σ : Measure Gap) [IsFiniteMeasure σ]
    {t : ℝ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) :
    Integrable (fun d : Gap => (d:ℝ)⁻¹^2) σ := by
  apply (integrable_const (t⁻¹^2)).mono' (by fun_prop)
  filter_upwards [hs] with d hd
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (inv_nonneg.mpr d.property.1.le) (inv_anti₀ ht hd) 2

theorem ae_finite_band_cover (σ : Measure Gap) {t : ℝ} {N : ℕ}
    (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : bandEdge N < t) :
    ∀ᵐ d : Gap ∂σ, d ∈ ⋃ j : Fin N, band j.val := by
  filter_upwards [hs] with d hd
  have hmem : d ∈ ⋃ j : ℕ, band j := by rw [iUnion_band]; trivial
  obtain ⟨j, hj⟩ := mem_iUnion.mp hmem
  have hjN : j < N := by
    by_contra hn
    have he := bandEdge_antitone (le_of_not_gt hn)
    exact (not_lt_of_ge hd) (hj.2.trans he |>.trans_lt hN)
  exact mem_iUnion.mpr ⟨⟨j,hjN⟩,hj⟩

theorem integral_eq_sum_bands (σ : Measure Gap) {t : ℝ} {N : ℕ}
    (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : bandEdge N < t)
    (f : Gap → ℝ) (hf : ∀ j : Fin N, IntegrableOn f (band j.val) σ) :
    (∫ d, f d ∂σ) = ∑ j : Fin N, ∫ d in band j.val, f d ∂σ := by
  calc
    _ = ∫ d in ⋃ j : Fin N, band j.val, f d ∂σ := by
      rw [Measure.restrict_eq_self_of_ae_mem (ae_finite_band_cover σ hs hN)]
    _ = _ := integral_iUnion_fintype (fun j : Fin N => measurableSet_band j.val)
      (fun i j hij => bands_disjoint (Fin.val_injective.ne hij)) hf

theorem inverseSquare_eq_band_total (σ : Measure Gap) [IsFiniteMeasure σ] {t : ℝ} {N : ℕ}
    (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : bandEdge N < t) :
    (∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ) = costTotal (fun j : Fin N => bandCost σ j.val) :=
  integral_eq_sum_bands σ hs hN _ (fun j => band_inverseSquare_integrable σ j.val)

theorem bandCost_hasSum (σ : Measure Gap) [IsFiniteMeasure σ] {t : ℝ} {N : ℕ}
    (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : bandEdge N < t) :
    HasSum (bandCost σ) (∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ) := by
  rw [inverseSquare_eq_band_total σ hs hN]
  unfold costTotal
  rw [Fin.sum_univ_eq_sum_range (bandCost σ)]
  apply hasSum_sum_of_ne_finset_zero
  intro j hj
  exact bandCost_eq_zero_of_support σ hs
    ((bandEdge_antitone (show N ≤ j by simpa using hj)).trans_lt hN)

def bandWeights (σ : Measure Gap) (j : ℕ) : ℝ≥0 :=
  Real.toNNReal (bandCost σ j / (∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ))

theorem bandWeights_coe (σ : Measure Gap) (j : ℕ) :
    (bandWeights σ j : ℝ) = bandCost σ j / (∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ) := by
  exact Real.coe_toNNReal _ (div_nonneg (bandCost_nonneg σ j) (integral_nonneg (fun _ => sq_nonneg _)))

theorem bandWeights_probability (σ : Measure Gap) [IsFiniteMeasure σ] {t : ℝ} {N : ℕ}
    (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : bandEdge N < t)
    (hA : 0 < ∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ) : HasSum (bandWeights σ) 1 := by
  apply NNReal.hasSum_coe.mp
  simp_rw [bandWeights_coe]
  convert (bandCost_hasSum σ hs hN).div_const (∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ) using 1
  exact (div_self hA.ne').symm

theorem bandWeights_le_one (σ : Measure Gap) [IsFiniteMeasure σ] {t : ℝ} {N : ℕ}
    (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : bandEdge N < t)
    (hA : 0 < ∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ) (j : ℕ) : (bandWeights σ j : ℝ) ≤ 1 := by
  have hh := bandWeights_probability σ hs hN hA
  have h := ENNReal.le_tsum j (f := fun j => (bandWeights σ j:ℝ≥0∞))
  rw [ENNReal.tsum_coe_eq hh] at h
  exact_mod_cast h

theorem bandCost_zero_measure (σ : Measure Gap) [IsFiniteMeasure σ] (j : ℕ)
    (hz : bandCost σ j = 0) : σ (band j) = 0 := by
  have hae := (integral_eq_zero_iff_of_nonneg (fun d : Gap => sq_nonneg ((d:ℝ)⁻¹))
    (band_inverseSquare_integrable σ j)).mp hz
  have hf : ∀ᵐ d : Gap ∂σ.restrict (band j), False := by
    filter_upwards [hae] with d hd
    exact (sq_pos_of_pos (inv_pos.mpr d.property.1)).ne' hd
  simpa only [ae_iff, not_false_eq_true, Set.ofPred_true, Measure.restrict_apply_univ] using hf

end ThresholdHC.EntropyTailAssembly
