import ThresholdHC.CriticalEntropy.FiniteAffinity

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.ConfidenceLocalization
open ThresholdHC.CriticalEntropy

/-- Hellinger affinity may be computed under any common dominating measure,
including at points where both densities vanish. -/
theorem affinity_reference {X : Type} [MeasurableSpace X]
    (P Q ξ : Measure X) [SigmaFinite P] [SigmaFinite Q] [SigmaFinite ξ]
    (hP : P ≪ ξ) (hQ : Q ≪ ξ) :
    hellingerAffinity P Q =
      ∫⁻ x, (P.rnDeriv ξ x * Q.rnDeriv ξ x)^(1/2 : ℝ) ∂ξ := by
  let M := P+Q
  have hM : M ≪ ξ := hP.add_left hQ
  have hp : P.rnDeriv M * M.rnDeriv ξ =ᵐ[ξ] P.rnDeriv ξ :=
    Measure.rnDeriv_mul_rnDeriv (Measure.AbsolutelyContinuous.rfl.add_right Q)
  have hq : Q.rnDeriv M * M.rnDeriv ξ =ᵐ[ξ] Q.rnDeriv ξ :=
    Measure.rnDeriv_mul_rnDeriv (Measure.AbsolutelyContinuous.rfl.add_right' P)
  let H (x : X) := (P.rnDeriv M x * Q.rnDeriv M x)^(1/2 : ℝ)
  calc
    _ = ∫⁻ x, H x ∂ξ.withDensity (M.rnDeriv ξ) := by
      rw [Measure.withDensity_rnDeriv_eq _ _ hM]
      rfl
    _ = ∫⁻ x, M.rnDeriv ξ x * H x ∂ξ :=
      lintegral_withDensity_eq_lintegral_mul ξ (Measure.measurable_rnDeriv _ _) (by dsimp [H]; fun_prop)
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [hp,hq] with x hx hy
      dsimp only [Pi.mul_apply] at hx hy
      rw [← hx,← hy,affinity_mass_scaling]
      exact mul_comm _ _

theorem affinity_with_density {X : Type} [MeasurableSpace X]
    (ξ : Measure X) [SigmaFinite ξ] (f g : X → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g)
    (hf_top : ∀ x, f x ≠ ∞) (hg_top : ∀ x, g x ≠ ∞) :
    hellingerAffinity (ξ.withDensity f) (ξ.withDensity g) =
      ∫⁻ x, (f x*g x)^(1/2 : ℝ) ∂ξ := by
  let : SigmaFinite (ξ.withDensity f) := SigmaFinite.withDensity_of_ne_top' hf_top
  let : SigmaFinite (ξ.withDensity g) := SigmaFinite.withDensity_of_ne_top' hg_top
  rw [affinity_reference _ _ ξ (withDensity_absolutelyContinuous _ _) (withDensity_absolutelyContinuous _ _)]
  apply lintegral_congr_ae
  filter_upwards [Measure.rnDeriv_withDensity ξ hf,Measure.rnDeriv_withDensity ξ hg] with x hx hy
  rw [hx,hy]

theorem affinity_factored_statistic {X I : Type}
    [MeasurableSpace X] [MeasurableSpace I]
    (ξ : Measure X) [IsFiniteMeasure ξ] (T : X → I) (hT : Measurable T)
    (f g : I → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    (hf_top : ∀ i, f i ≠ ∞) (hg_top : ∀ i, g i ≠ ∞) :
    hellingerAffinity (ξ.withDensity (f ∘ T)) (ξ.withDensity (g ∘ T)) =
      hellingerAffinity ((ξ.withDensity (f ∘ T)).map T) ((ξ.withDensity (g ∘ T)).map T) := by
  rw [map_factored_density ξ T hT f hf,map_factored_density ξ T hT g hg,
    affinity_with_density ξ (f ∘ T) (g ∘ T) (hf.comp hT) (hg.comp hT)
      (fun x => hf_top (T x)) (fun x => hg_top (T x)),
    affinity_with_density (ξ.map T) f g hf hg hf_top hg_top,
    lintegral_map (by fun_prop) hT]
  rfl

end ThresholdHC.ConfidenceLocalization
