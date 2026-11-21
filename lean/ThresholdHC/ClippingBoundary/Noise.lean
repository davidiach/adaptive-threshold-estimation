import ThresholdHC.ClippingBoundary.Specification

/-! The seed noise and the abstract noise counterexample, as unbundled
component lemmas.

`seedNoise ε M` is a finite measure for all `ε`, `M` and a probability measure
for `0 ≤ ε ≤ 1`, with mean `0` and variance `εM²`. For a raw estimator `F₀`
under `P` and independent noise, `noisy_integrable` and `noisy_integral` need
only integrability of `F₀` (with `0 ≤ ε ≤ 1` for the integral),
`noisy_memLp` and `noisy_variance` need only `MemLp F₀ 2 P` (with
`0 ≤ ε ≤ 1` for the variance), and `noisy_clip_risk` needs only
almost-everywhere measurability, `0 ≤ ε` and `0 ≤ θ ≤ ρ`. On the atom `0` the clipped error is at most
the raw error (`clip_loss_le`); on the atoms `±M` both the clipped estimate and
`θ` lie in `[0,ρ]`, so the squared error is at most `ρ²`. -/
noncomputable section
namespace ThresholdHC.ClippingBoundary
open MeasureTheory
open ThresholdHC.Tier6 ThresholdHC.HardBudget

instance seedNoise_isFiniteMeasure (ε M : ℝ) : IsFiniteMeasure (seedNoise ε M) := by
  unfold seedNoise
  constructor
  simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  exact ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩,
    ENNReal.ofReal_lt_top⟩

theorem seedNoise_probability {ε : ℝ} (M : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    IsProbabilityMeasure (seedNoise ε M) := by
  constructor
  simp only [seedNoise, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by linarith) (by linarith),
    ← ENNReal.ofReal_add (by linarith) (by linarith)]
  rw [show 1 - ε + ε / 2 + ε / 2 = 1 by ring, ENNReal.ofReal_one]

theorem lintegral_seedNoise (ε M : ℝ) (f : ℝ → ENNReal) :
    ∫⁻ z, f z ∂seedNoise ε M =
      ENNReal.ofReal (1 - ε) * f 0 + ENNReal.ofReal (ε / 2) * f M +
        ENNReal.ofReal (ε / 2) * f (-M) := by
  simp only [seedNoise, lintegral_add_measure, lintegral_smul_measure, lintegral_dirac,
    smul_eq_mul]

/-- Every real function is integrable for the three-atom noise law. -/
theorem integrable_seedNoise (ε M : ℝ) (g : ℝ → ℝ) : Integrable g (seedNoise ε M) := by
  unfold seedNoise
  refine (((integrable_dirac ?_).smul_measure ENNReal.ofReal_ne_top).add_measure
    ((integrable_dirac ?_).smul_measure ENNReal.ofReal_ne_top)).add_measure
    ((integrable_dirac ?_).smul_measure ENNReal.ofReal_ne_top) <;> exact enorm_lt_top

theorem integral_seedNoise {ε : ℝ} (M : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (g : ℝ → ℝ) :
    ∫ z, g z ∂seedNoise ε M = (1 - ε) * g 0 + ε / 2 * g M + ε / 2 * g (-M) := by
  have hi : ∀ x : ℝ, ∀ c : ENNReal, c ≠ ⊤ → Integrable g (c • Measure.dirac x) :=
    fun x c hc => (integrable_dirac enorm_lt_top).smul_measure hc
  unfold seedNoise
  rw [integral_add_measure ((hi 0 _ ENNReal.ofReal_ne_top).add_measure
      (hi M _ ENNReal.ofReal_ne_top)) (hi (-M) _ ENNReal.ofReal_ne_top),
    integral_add_measure (hi 0 _ ENNReal.ofReal_ne_top) (hi M _ ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac, integral_dirac,
    ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (by linarith)]
  simp only [smul_eq_mul]

theorem memLp_id_seedNoise (ε M : ℝ) : MemLp id 2 (seedNoise ε M) :=
  (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2
    (integrable_seedNoise ε M _)

theorem integral_id_seedNoise {ε : ℝ} (M : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    ∫ z, z ∂seedNoise ε M = 0 := by
  rw [integral_seedNoise M h0 h1 (fun z => z)]
  ring

theorem variance_seedNoise {ε : ℝ} (M : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    ProbabilityTheory.variance id (seedNoise ε M) = ε * M ^ 2 := by
  rw [ProbabilityTheory.variance_eq_integral measurable_id.aemeasurable]
  have hm : ∫ z, id z ∂seedNoise ε M = 0 := integral_id_seedNoise M h0 h1
  simp only [id_eq] at hm ⊢
  rw [hm, integral_seedNoise M h0 h1 (fun z => (z - 0) ^ 2)]
  ring

section Abstract
variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem noisy_integrable (ε M : ℝ) {F₀ : Ω → ℝ} (hF : Integrable F₀ P) :
    Integrable (fun z : Ω × ℝ => F₀ z.1 + z.2) (P.prod (seedNoise ε M)) :=
  (hF.comp_fst _).add ((integrable_seedNoise ε M (fun z : ℝ => z)).comp_snd P)

theorem noisy_integral {ε : ℝ} (M : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {F₀ : Ω → ℝ}
    (hF : Integrable F₀ P) :
    (∫ z, F₀ z.1 + z.2 ∂P.prod (seedNoise ε M)) = ∫ ω, F₀ ω ∂P := by
  have := seedNoise_probability M h0 h1
  rw [integral_add (hF.comp_fst _) ((integrable_seedNoise ε M (fun z : ℝ => z)).comp_snd P),
    integral_fun_fst (fun ω => F₀ ω), integral_fun_snd (fun z : ℝ => z),
    integral_id_seedNoise M h0 h1]
  simp

theorem noisy_memLp (ε M : ℝ) {F₀ : Ω → ℝ} (hF : MemLp F₀ 2 P) :
    MemLp (fun z : Ω × ℝ => F₀ z.1 + z.2) 2 (P.prod (seedNoise ε M)) :=
  (hF.comp_fst _).add ((memLp_id_seedNoise ε M).comp_snd P)

theorem noisy_variance {ε : ℝ} (M : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {F₀ : Ω → ℝ}
    (hF : MemLp F₀ 2 P) :
    ProbabilityTheory.variance (fun z : Ω × ℝ => F₀ z.1 + z.2) (P.prod (seedNoise ε M)) =
      ProbabilityTheory.variance F₀ P + ε * M ^ 2 := by
  have := seedNoise_probability M h0 h1
  have h := ProbabilityTheory.variance_add_prod (Y := id) hF (memLp_id_seedNoise ε M)
  rw [variance_seedNoise M h0 h1] at h
  exact h

/-- The clipped squared error of the noisy estimator, pointwise in the raw value. -/
theorem noisy_clip_loss {ε : ℝ} (M : ℝ) (h0 : 0 ≤ ε) {θ ρ : ℝ} (hθ0 : 0 ≤ θ) (hθρ : θ ≤ ρ)
    (x : ℝ) :
    ∫⁻ z, ENNReal.ofReal ((clipEstimate ρ (x + z) - θ) ^ 2) ∂seedNoise ε M ≤
      ENNReal.ofReal ((x - θ) ^ 2) + ENNReal.ofReal (ε * ρ ^ 2) := by
  have hρ : 0 ≤ ρ := hθ0.trans hθρ
  have hfar : ∀ y : ℝ, ENNReal.ofReal ((clipEstimate ρ y - θ) ^ 2) ≤ ENNReal.ofReal (ρ ^ 2) := by
    intro y
    apply ENNReal.ofReal_le_ofReal
    have hc0 : 0 ≤ clipEstimate ρ y := le_max_left _ _
    have hcρ : clipEstimate ρ y ≤ ρ := max_le hρ (min_le_left _ _)
    nlinarith
  have hnear : ENNReal.ofReal (1 - ε) * ENNReal.ofReal ((clipEstimate ρ (x + 0) - θ) ^ 2) ≤
      ENNReal.ofReal ((x - θ) ^ 2) := by
    rw [add_zero]
    calc
      _ ≤ 1 * ENNReal.ofReal ((clipEstimate ρ x - θ) ^ 2) :=
        mul_le_mul_left (ENNReal.ofReal_le_one.2 (by linarith)) _
      _ = loss θ (clipEstimate ρ x) := one_mul _
      _ ≤ loss θ x := clip_loss_le ρ θ x ⟨hθ0, hθρ⟩
  rw [lintegral_seedNoise, add_assoc]
  refine add_le_add hnear ?_
  calc
    _ ≤ ENNReal.ofReal (ε / 2) * ENNReal.ofReal (ρ ^ 2) +
        ENNReal.ofReal (ε / 2) * ENNReal.ofReal (ρ ^ 2) :=
      add_le_add (mul_le_mul_right (hfar _) _) (mul_le_mul_right (hfar _) _)
    _ = ENNReal.ofReal (ε * ρ ^ 2) := by
      rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_add (by positivity)
        (by positivity)]
      congr 1
      ring

theorem noisy_clip_risk {ε : ℝ} (M : ℝ) (h0 : 0 ≤ ε) {F₀ : Ω → ℝ} (hF : AEMeasurable F₀ P)
    {θ ρ : ℝ} (hθ0 : 0 ≤ θ) (hθρ : θ ≤ ρ) :
    squaredRisk (P.prod (seedNoise ε M)) (fun z => clipEstimate ρ (F₀ z.1 + z.2)) θ ≤
      squaredRisk P F₀ θ + ENNReal.ofReal (ε * ρ ^ 2) := by
  have hpair : AEMeasurable (fun z : Ω × ℝ => (F₀ z.1, z.2)) (P.prod (seedNoise ε M)) :=
    (hF.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).prodMk
      measurable_snd.aemeasurable
  have hg : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal ((clipEstimate ρ (p.1 + p.2) - θ) ^ 2)) := by
    have := measurable_clip ρ
    fun_prop
  -- elaborated without an expected type: unifying the composition against the
  -- lambda first is very slow
  have hae₀ := hg.comp_aemeasurable hpair
  have hae : AEMeasurable (fun z : Ω × ℝ => ENNReal.ofReal ((clipEstimate ρ (F₀ z.1 + z.2) - θ) ^ 2))
      (P.prod (seedNoise ε M)) := hae₀
  show ∫⁻ z, ENNReal.ofReal ((clipEstimate ρ (F₀ z.1 + z.2) - θ) ^ 2) ∂P.prod (seedNoise ε M) ≤
    ∫⁻ ω, ENNReal.ofReal ((F₀ ω - θ) ^ 2) ∂P + ENNReal.ofReal (ε * ρ ^ 2)
  rw [lintegral_prod _ hae]
  calc
    _ ≤ ∫⁻ ω, (ENNReal.ofReal ((F₀ ω - θ) ^ 2) + ENNReal.ofReal (ε * ρ ^ 2)) ∂P :=
      lintegral_mono fun ω => noisy_clip_loss M h0 hθ0 hθρ (F₀ ω)
    _ = _ := by
      rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]

end Abstract

end ThresholdHC.ClippingBoundary
