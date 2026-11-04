import ThresholdHC.HardBudget.Full
import ThresholdHC.BlindUpper.Full

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.HardBudget
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.ObservableSimulation ThresholdHC.StoppingProgram

theorem pathwise_expected {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (q : SignLaw) {B : ℝ} (hB : 0 ≤ B) (hc : PathwiseCap A ⌊B⌋₊) :
    expectedWork μ A q ≤ ENNReal.ofReal B := by
  calc expectedWork μ A q ≤ ∫⁻ _ : PopulationSeed R × ProcessTape, (⌊B⌋₊:ℝ≥0∞) ∂experimentLaw μ A q := by
         apply lintegral_mono_ae
         filter_upwards [original_path_valid μ A q] with z hz using hc z.1.1 z.2 hz
       _ ≤ _ := by simp only [lintegral_const,measure_univ,mul_one,← ENNReal.ofReal_natCast]; exact ENNReal.ofReal_le_ofReal (Nat.floor_le hB)

theorem square_from_rms {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (g : Ω → ℝ)
    (θ x : ℝ) (hx : 0 ≤ x) (h : rootMeanRisk P g θ ≤ ENNReal.ofReal x) :
    squaredRisk P g θ ≤ ENNReal.ofReal (x^2) := by
  have hh := pow_le_pow_left' h 2
  rw [rootMeanRisk,← ENNReal.rpow_mul_natCast,← ENNReal.ofReal_pow hx] at hh
  norm_num at hh
  exact hh

theorem rms_from_square {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (g : Ω → ℝ)
    (θ x : ℝ) (hx : 0 ≤ x) (h : squaredRisk P g θ ≤ ENNReal.ofReal (x^2)) :
    rootMeanRisk P g θ ≤ ENNReal.ofReal x := by
  have hh := ENNReal.rpow_le_rpow h (by norm_num : (0:ℝ) ≤ 1/2)
  rwa [ofReal_square_rpow_half x hx] at hh

/-- A single transformed family works for all subsequently supplied laws.
Every positive budget is covered, including the zero-work midpoint regime. -/
theorem rms_family {R : ℕ → Type} [∀ j, MeasurableSpace (R j)] (base : ∀ j, AdaptiveEstimator (R j))
    (M : ℝ) (hM : 0 ≤ M) : ∃ rule : ℝ → AdaptiveEstimator (∀ j, R j),
    (∀ B : ℝ, 0 ≤ B → PathwiseCap (rule B) ⌊B⌋₊) ∧
    ∀ (B : ℝ), 0 < B → ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
      (C K : ℝ) (f : ℝ → ℝ), signMean μ q.val ≤ M → 1/2 ≤ C → 1/2 ≤ K →
      32*C^2 ≤ K^2 → (∀ b, 0 < b → 0 ≤ f b) → (∀ b, 0 < b → b < 4 → f b = M) →
      (∀ b b', 1/2 ≤ b → b ≤ b' → f b ≤ Real.sqrt (b'/b)*f b') →
      (∀ j, expectedWork μ (base j) q ≤ stageAllowance j ∧
        rootMeanRisk (experimentLaw μ (base j) q) (populationOutput (base j)) (signMean μ q.val) ≤
          ENNReal.ofReal (C*f (stageAllowance j))) →
      rootMeanRisk (experimentLaw μ (rule B) q) (populationOutput (rule B)) (signMean μ q.val) ≤
        ENNReal.ofReal (K*f B) := by
  obtain ⟨rule,hr⟩ := observable_fallback R base M hM
  refine ⟨rule,fun B hb => (hr B hb).2.1,?_⟩
  intro B hb μ _ q C K f hθ hC hK hc hf hsmall hs hst
  have hθ0 := (signMean_bounds μ q).1
  have hK0 : 0 ≤ K := by linarith
  apply rms_from_square _ _ _ _ (mul_nonneg hK0 (hf B hb))
  by_cases hbig : 4 ≤ B
  · have hst' (j : ℕ) := square_from_rms _ _ _ _ (mul_nonneg (by linarith : 0 ≤ C)
      (hf (stageAllowance j) (by dsimp [stageAllowance]; positivity))) (hst j).2
    have hrisk := (hr B hb.le).2.2.2.2 μ q C f hbig hθ0 hθ hC (fun b h => hf b (by linarith))
      (hsmall _ (by norm_num) (by norm_num)) hs (fun j => ⟨(hst j).1,by simpa [mul_pow] using hst' j⟩)
    exact hrisk.trans (ENNReal.ofReal_le_ofReal (by rw [mul_pow]; exact mul_le_mul_of_nonneg_right hc (sq_nonneg _)))
  · let θ := signMean μ q.val
    have hidle := ((hr B hb.le).2.2.1 (lt_of_not_ge hbig)).2
    have h := original_observable_lintegral μ (rule B) q (fun z => loss θ ((rule B).output z))
      ((measurable_loss θ).comp (rule B).output_measurable)
    change (∫⁻ z, loss θ ((rule B).output (z.1.1,z.2)) ∂experimentLaw μ (rule B) q) ≤ _
    rw [h,hsmall B hb (lt_of_not_ge hbig)]
    simp_rw [hidle]
    let _ : IsProbabilityMeasure (originalSimulationLaw μ (rule B) q) := by unfold originalSimulationLaw; infer_instance
    rw [lintegral_const,measure_univ,mul_one]
    apply ENNReal.ofReal_le_ofReal
    have hmid : (M/2-θ)^2 ≤ (M/2)^2 := by dsimp [θ]; nlinarith [mul_nonneg hθ0 (sub_nonneg.mpr hθ)]
    exact hmid.trans (pow_le_pow_left₀ (by positivity) (by nlinarith [mul_le_mul_of_nonneg_right hK hM]) 2)

end ThresholdHC.HardBudget
