import ThresholdHC.Tier6.HardPair

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace ThresholdHC.UnbiasedConverse
open ThresholdHC.Tier6

def truncatedInverse (n : ℕ) (d : Gap) : ℝ := min ((n:ℝ)+1) (d:ℝ)⁻¹

theorem measurable_truncatedInverse (n : ℕ) : Measurable (truncatedInverse n) :=
  measurable_const.min measurable_subtype_coe.inv

theorem truncatedInverse_nonneg (n : ℕ) (d : Gap) : 0 ≤ truncatedInverse n d :=
  le_min (by positivity) (inv_nonneg.mpr d.property.1.le)

theorem integrable_truncatedInverse (μ : Measure Gap) [IsProbabilityMeasure μ] (n : ℕ) :
    Integrable (truncatedInverse n) μ := by
  apply (integrable_const ((n:ℝ)+1)).mono' (measurable_truncatedInverse n).aestronglyMeasurable
  filter_upwards [] with d
  rw [Real.norm_of_nonneg (truncatedInverse_nonneg n d)]
  exact min_le_left _ _

theorem truncatedInverse_eq_scaled (n : ℕ) (d : Gap) :
    truncatedInverse n d = ((n:ℝ)+1)*clippedGap (1/((n:ℝ)+1)) d := by
  have hn : 0 < (n:ℝ)+1 := by positivity
  unfold truncatedInverse clippedGap
  rw [mul_min_of_nonneg _ _ hn.le, mul_one]
  congr 1
  field_simp

/-- A uniform linear bound on the modulus forces integrability of the inverse
gap. Monotone convergence is applied to nonnegative truncated inverses. -/
theorem inverse_integrable_of_modulus_bound (μ : Measure Gap) [IsProbabilityMeasure μ]
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ h : ℝ, 0 < h → modulus μ h ≤ C*h) :
    Integrable (fun d : Gap => (d:ℝ)⁻¹) μ ∧ (∫ d : Gap, (d:ℝ)⁻¹ ∂μ) ≤ C := by
  have hint n : (∫ d, truncatedInverse n d ∂μ) ≤ C := by
    have hn : 0 < (n:ℝ)+1 := by positivity
    simp_rw [truncatedInverse_eq_scaled]
    rw [integral_const_mul]
    have hm := mul_le_mul_of_nonneg_left (hb (1/((n:ℝ)+1)) (by positivity)) hn.le
    have he : ((n:ℝ)+1)*(C*(1/((n:ℝ)+1))) = C := by field_simp
    simpa only [he, modulus] using hm
  have heq (d : Gap) : ENNReal.ofReal ((d:ℝ)⁻¹) =
      ⨆ n : ℕ, ENNReal.ofReal (truncatedInverse n d) := by
    apply le_antisymm
    · obtain ⟨n,hn⟩ := exists_nat_gt ((d:ℝ)⁻¹)
      have hf : truncatedInverse n d = (d:ℝ)⁻¹ := min_eq_right (by linarith)
      calc
        _ = ENNReal.ofReal (truncatedInverse n d) := congrArg ENNReal.ofReal hf.symm
        _ ≤ _ := le_iSup (fun n => ENNReal.ofReal (truncatedInverse n d)) n
    · apply iSup_le
      intro n
      exact ENNReal.ofReal_le_ofReal (min_le_right _ _)
  have hm : Monotone (fun n : ℕ => fun d : Gap => ENNReal.ofReal (truncatedInverse n d)) := by
    intro m n hmn d
    apply ENNReal.ofReal_le_ofReal
    apply min_le_min _ le_rfl
    exact_mod_cast Nat.add_le_add_right hmn 1
  have hlin : (∫⁻ d : Gap, ENNReal.ofReal ((d:ℝ)⁻¹) ∂μ) ≤ ENNReal.ofReal C := by
    simp_rw [heq]
    rw [lintegral_iSup (fun n => (measurable_truncatedInverse n).ennreal_ofReal) hm]
    apply iSup_le
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_truncatedInverse μ n)
      (ae_of_all _ (truncatedInverse_nonneg n))]
    exact ENNReal.ofReal_le_ofReal (hint n)
  have hi : Integrable (fun d : Gap => (d:ℝ)⁻¹) μ := by
    refine ⟨measurable_subtype_coe.inv.aestronglyMeasurable, ?_⟩
    have he : ∀ d : Gap, ‖(d:ℝ)⁻¹‖ₑ = ENNReal.ofReal ((d:ℝ)⁻¹) :=
      fun d => Real.enorm_of_nonneg (inv_nonneg.mpr d.property.1.le)
    have hh : (∫⁻ d : Gap, ‖(d:ℝ)⁻¹‖ₑ ∂μ) ≤ ENNReal.ofReal C := by
      simpa only [he] using hlin
    exact lt_of_le_of_lt hh ENNReal.ofReal_lt_top
  refine ⟨hi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun d => inv_nonneg.mpr d.property.1.le))] at hlin
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp hlin

end ThresholdHC.UnbiasedConverse
