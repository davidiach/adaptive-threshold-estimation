import ThresholdHC.CriticalEntropy.HellingerModel

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.CriticalEntropy

theorem affinity_density_scaling (s u v : ℝ≥0∞) (hs₀ : s ≠ 0) (hs_top : s ≠ ∞) :
    s * ((s⁻¹*u)*(s⁻¹*v))^(1/2 : ℝ) = (u*v)^(1/2 : ℝ) := by
  have he : (s⁻¹*u)*(s⁻¹*v) = (s⁻¹*s⁻¹)*(u*v) := by ring
  have hsqrt : (s⁻¹*s⁻¹)^(1/2 : ℝ) = s⁻¹ := by
    rw [← pow_two, ← ENNReal.rpow_natCast_mul]
    norm_num
  rw [he,ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1/2),hsqrt,
    ← mul_assoc,ENNReal.mul_inv_cancel hs₀ hs_top,one_mul]

theorem hellingerAffinity_withDensity {Ω : Type} [MeasurableSpace Ω]
    (ξ : Measure Ω) [SigmaFinite ξ] (f g : Ω → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g)
    (hf_top : ∀ x, f x ≠ ∞) (hg_top : ∀ x, g x ≠ ∞)
    (hs₀ : ∀ x, f x+g x ≠ 0) :
    hellingerAffinity (ξ.withDensity f) (ξ.withDensity g) =
      ∫⁻ z, (f z*g z)^(1/2 : ℝ) ∂ξ := by
  let : SigmaFinite (ξ.withDensity f) := SigmaFinite.withDensity_of_ne_top' hf_top
  let : SigmaFinite (ξ.withDensity g) := SigmaFinite.withDensity_of_ne_top' hg_top
  have hs_top : ∀ x, (f+g) x ≠ ∞ := fun x => ENNReal.add_ne_top.mpr ⟨hf_top x,hg_top x⟩
  have hsf : Measurable (f+g) := hf.add hg
  have hP := Measure.rnDeriv_withDensity_right (ξ.withDensity f) ξ hsf.aemeasurable
    (ae_of_all _ hs₀) (ae_of_all _ hs_top)
  have hQ := Measure.rnDeriv_withDensity_right (ξ.withDensity g) ξ hsf.aemeasurable
    (ae_of_all _ hs₀) (ae_of_all _ hs_top)
  have hPf := Measure.rnDeriv_withDensity ξ hf
  have hQg := Measure.rnDeriv_withDensity ξ hg
  unfold hellingerAffinity
  rw [← withDensity_add_left hf g]
  rw [lintegral_withDensity_eq_lintegral_mul ξ hsf (by fun_prop)]
  apply lintegral_congr_ae
  filter_upwards [hP,hQ,hPf,hQg] with x hxP hxQ hxf hxg
  dsimp only [Pi.mul_apply,Pi.add_apply]
  rw [hxP,hxQ,hxf,hxg]
  exact affinity_density_scaling _ _ _ (hs₀ x) (hs_top x)

theorem affinity_mass_scaling (a u v : ℝ≥0∞) :
    ((u*a)*(v*a))^(1/2 : ℝ) = (u*v)^(1/2 : ℝ)*a := by
  have he : (u*a)*(v*a) = (u*v)*(a*a) := by ring
  have ha : (a*a)^(1/2 : ℝ) = a := by
    rw [← pow_two,← ENNReal.rpow_natCast_mul]
    norm_num
  rw [he,ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1/2),ha]

theorem hellingerAffinity_finite_density {I : Type} [Fintype I]
    [MeasurableSpace I] [MeasurableSingletonClass I]
    (ξ : Measure I) [IsFiniteMeasure ξ] (f g : I → ℝ≥0∞)
    (hf_top : ∀ i, f i ≠ ∞) (hg_top : ∀ i, g i ≠ ∞)
    (hs₀ : ∀ i, f i+g i ≠ 0) :
    hellingerAffinity (ξ.withDensity f) (ξ.withDensity g) =
      finiteAffinity (fun i => (ξ.withDensity f) {i}) (fun i => (ξ.withDensity g) {i}) := by
  rw [hellingerAffinity_withDensity ξ f g (measurable_of_countable _)
    (measurable_of_countable _) hf_top hg_top hs₀,lintegral_fintype,finiteAffinity]
  apply Finset.sum_congr rfl
  intro i hi
  rw [withDensity_apply _ (measurableSet_singleton i),
    withDensity_apply _ (measurableSet_singleton i),lintegral_singleton,lintegral_singleton]
  exact (affinity_mass_scaling _ _ _).symm

end ThresholdHC.CriticalEntropy
