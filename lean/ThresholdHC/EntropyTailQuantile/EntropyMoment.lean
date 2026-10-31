import ThresholdHC.EntropyTail.BandGeometry
import ThresholdHC.EntropyTail.TailModulus

/-! The full inverse-square moment is dominated by cost entropy. All moment
bounds retain extended values, including nonintegrable gap laws. -/

noncomputable section
open MeasureTheory Set Real
open scoped ENNReal BigOperators

namespace ThresholdHC.EntropyTail
open ThresholdHC.Tier6

theorem iUnion_band : (⋃ j : ℕ, band j) = univ := by
  apply eq_univ_of_forall
  intro d
  obtain ⟨N, hN, hb⟩ := exists_band_cutoff d.property.1
  cases N with
  | zero =>
    have hd : (d:ℝ) ≤ bandEdge 0 := by simpa [bandEdge] using d.property.2
    exact False.elim ((not_lt_of_ge hd) hN)
  | succ n =>
    apply mem_iUnion.mpr
    refine ⟨n, ?_⟩
    exact ⟨by simpa only [bandEdge_succ] using hN, hb n (Nat.lt_succ_self n)⟩

theorem inverseSquare_lintegral_le_entropy (σ : Measure Gap) [IsFiniteMeasure σ] :
    (∫⁻ d : Gap, ENNReal.ofReal ((d:ℝ)⁻¹^2) ∂σ) ≤ measureCostEntropy σ := by
  have he : (∫⁻ d : Gap, ENNReal.ofReal ((d:ℝ)⁻¹^2) ∂σ) =
      ∑' j : ℕ, ENNReal.ofReal (bandCost σ j) := by
    conv_lhs => rw [← Measure.restrict_univ (μ := σ), ← iUnion_band]
    rw [lintegral_iUnion measurableSet_band bands_disjoint]
    congr 1
    funext j
    exact (ofReal_integral_eq_lintegral_ofReal (band_inverseSquare_integrable σ j)
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _))).symm
  rw [he, ENNReal.tsum_eq_iSup_nat]
  apply iSup_le
  intro n
  apply le_trans _ (le_iSup (fun k => ENNReal.ofReal
    (costEntropy (fun i : Fin k => bandCost σ i))) n)
  rw [← Fin.sum_univ_eq_sum_range]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun (i : Fin n) _ => bandCost_nonneg σ i)]
  exact ENNReal.ofReal_le_ofReal (costTotal_le_costEntropy (fun i : Fin n => bandCost_nonneg σ i))

theorem inverse_lintegral_le_sqrt_moment (ξ : Measure Gap) :
    (∫⁻ d : Gap, ENNReal.ofReal ((d:ℝ)⁻¹) ∂ξ) ≤
      (ξ univ * ∫⁻ d : Gap, ENNReal.ofReal ((d:ℝ)⁻¹^2) ∂ξ) ^ (1/(2:ℝ)) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ξ Real.HolderConjugate.two_two
    (f := fun _ => (1 : ℝ≥0∞)) (g := fun d : Gap => ENNReal.ofReal ((d:ℝ)⁻¹))
    measurable_const.aemeasurable (by fun_prop)
  simp only [Pi.mul_apply, one_mul, ENNReal.rpow_two] at h
  have hp (d : Gap) : ENNReal.ofReal ((d:ℝ)⁻¹^2) = (ENNReal.ofReal ((d:ℝ)⁻¹))^2 :=
    ENNReal.ofReal_pow (inv_nonneg.mpr d.property.1.le) 2
  simp_rw [← hp] at h
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  simpa using h

theorem tailModulus_le_sqrt_entropy {ξ σ : Measure Gap} [IsFiniteMeasure σ]
    (hξ : ξ ≤ σ) {ρ h : ℝ} (hmass : ξ univ ≤ ENNReal.ofReal ρ) (hh : 0 ≤ h) :
    ENNReal.ofReal (tailModulus ξ h) ≤
      ENNReal.ofReal h * (ENNReal.ofReal ρ * measureCostEntropy σ) ^ (1/(2:ℝ)) := by
  have : IsFiniteMeasure ξ := isFiniteMeasure_of_le σ hξ
  rw [tailModulus, ofReal_integral_eq_lintegral_ofReal (tailKernel_integrable ξ hh)
    (Filter.Eventually.of_forall (tailKernel_nonneg hh))]
  calc
    _ ≤ ∫⁻ d : Gap, ENNReal.ofReal h * ENNReal.ofReal ((d:ℝ)⁻¹) ∂ξ := by
      apply lintegral_mono
      intro d
      change ENNReal.ofReal (min 1 (h/(d:ℝ))) ≤ ENNReal.ofReal h * ENNReal.ofReal ((d:ℝ)⁻¹)
      rw [← ENNReal.ofReal_mul hh]
      apply ENNReal.ofReal_le_ofReal
      simpa only [div_eq_mul_inv] using min_le_right (1:ℝ) (h/(d:ℝ))
    _ = ENNReal.ofReal h * ∫⁻ d : Gap, ENNReal.ofReal ((d:ℝ)⁻¹) ∂ξ :=
      lintegral_const_mul _ (by fun_prop)
    _ ≤ ENNReal.ofReal h *
        (ξ univ * ∫⁻ d : Gap, ENNReal.ofReal ((d:ℝ)⁻¹^2) ∂ξ) ^ (1/(2:ℝ)) := by
      gcongr
      exact inverse_lintegral_le_sqrt_moment ξ
    _ ≤ _ := by
      gcongr
      exact (lintegral_mono' hξ le_rfl).trans (inverseSquare_lintegral_le_entropy σ)

end ThresholdHC.EntropyTail
