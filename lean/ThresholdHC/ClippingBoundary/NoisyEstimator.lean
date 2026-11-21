import ThresholdHC.ClippingBoundary.Noise

/-! The noise counterexample inside the original experiment.

`noisyEstimator A M h0 h1` draws the seed of `A` together with an independent
noise coordinate, runs the policy of `A` on the first coordinate and adds the
noise to the output. The simulation identity
`ObservableSimulation.original_observable_lintegral` writes an observable
integral of either estimator as an integral over its seed and the tapes; for
the noisy estimator the seed law is a product with the noise law, and swapping
the noise integral with the tape integral gives `noisy_lintegral`: integrating
over the noisy experiment is integrating over the experiment of `A` and then
over the noise. `noisy_law` is the same identity for laws. The component
lemmas of `Noise.lean` then transfer through these identities, each with only
the hypotheses it needs. -/
noncomputable section
namespace ThresholdHC.ClippingBoundary
open MeasureTheory
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.HardBudget ThresholdHC.ObservableSimulation

/-- The noisy estimator: the noise is a second seed coordinate added to the output. -/
def noisyEstimator {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) {ε : ℝ} (M : ℝ)
    (h0 : 0 ≤ ε) (h1 : ε ≤ 1) : AdaptiveEstimator (R × ℝ) where
  randomLaw := A.randomLaw.prod (seedNoise ε M)
  probability := by
    have := seedNoise_probability M h0 h1
    infer_instance
  policy := fun u => A.policy u.1
  policy_measurable := fun xs a => measurable_fst (A.policy_measurable xs a)
  output := fun z => A.output (z.1.1, z.2) + z.1.2
  output_measurable :=
    (A.output_measurable.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).add
      (measurable_snd.comp measurable_fst)

section Law
variable {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
  (A : AdaptiveEstimator R) {ε : ℝ} (M : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (q : SignLaw)

/-- The observable coordinates of the noisy experiment: seed, tape and noise. -/
def noisyView (w : PopulationSeed (R × ℝ) × ProcessTape) : (R × ProcessTape) × ℝ :=
  ((w.1.1.1, w.2), w.1.1.2)

/-- The observable coordinates of the original experiment: seed and tape. -/
def plainView (y : PopulationSeed R × ProcessTape) : R × ProcessTape := (y.1.1, y.2)

theorem measurable_noisyView : Measurable (noisyView (R := R)) :=
  ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd).prodMk
    (measurable_snd.comp (measurable_fst.comp measurable_fst))

theorem measurable_plainView : Measurable (plainView (R := R)) :=
  (measurable_fst.comp measurable_fst).prodMk measurable_snd

include h0 h1 in
/-- Integrating over the noisy experiment is integrating over the experiment of
`A` and then over the independent noise. -/
theorem noisy_lintegral (f : (R × ProcessTape) × ℝ → ENNReal) (hf : Measurable f) :
    ∫⁻ w, f (noisyView w) ∂experimentLaw μ (noisyEstimator A M h0 h1) q =
      ∫⁻ y, ∫⁻ z, f (plainView y, z) ∂seedNoise ε M ∂experimentLaw μ A q := by
  have := seedNoise_probability M h0 h1
  set ν := seedNoise ε M with hν
  set T := Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q) with hT
  have hpath : Measurable (fun z : R × (ℕ → ℕ → Bool) => populationPath (A.policy z.1) z.2) :=
    measurable_seeded_populationPath A.policy (fun xs => measurable_to_countable' (A.policy_measurable xs))
  -- the integrand over seed, noise and tapes
  set h : (R × ℝ) × (ℕ → ℕ → Bool) → ENNReal :=
    fun u => f ((u.1.1, populationPath (A.policy u.1.1) u.2), u.1.2) with hh
  have hhm : Measurable h :=
    hf.comp ((measurable_fst.comp measurable_fst).prodMk
      (hpath.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
      |>.prodMk (measurable_snd.comp measurable_fst))
  have hF' : Measurable (fun x : (R × ℝ) × ProcessTape => f ((x.1.1, x.2), x.1.2)) :=
    hf.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd
      |>.prodMk (measurable_snd.comp measurable_fst))
  have hG : Measurable (fun y : R × ProcessTape => ∫⁻ z, f (y, z) ∂ν) := hf.lintegral_prod_right'
  have hL := original_observable_lintegral μ (noisyEstimator A M h0 h1) q
    (fun x => f ((x.1.1, x.2), x.1.2)) hF'
  have hR := original_observable_lintegral μ A q (fun y => ∫⁻ z, f (y, z) ∂ν) hG
  have hLeq : ∫⁻ w, f (noisyView w) ∂experimentLaw μ (noisyEstimator A M h0 h1) q =
      ∫⁻ u, h u ∂(A.randomLaw.prod ν).prod T := hL
  have hReq : ∫⁻ y, ∫⁻ z, f (plainView y, z) ∂ν ∂experimentLaw μ A q =
      ∫⁻ u, ∫⁻ z, h ((u.1, z), u.2) ∂ν ∂A.randomLaw.prod T := hR
  rw [hLeq, hReq, lintegral_prod _ hhm.aemeasurable,
    lintegral_prod _ (hhm.lintegral_prod_right').aemeasurable]
  have hR2 : Measurable (fun u : R × (ℕ → ℕ → Bool) => ∫⁻ z, h ((u.1, z), u.2) ∂ν) :=
    (hhm.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd
      |>.prodMk (measurable_snd.comp measurable_fst))).lintegral_prod_right'
  rw [lintegral_prod _ hR2.aemeasurable]
  refine lintegral_congr fun r => ?_
  apply lintegral_lintegral_swap
  exact (hhm.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)).aemeasurable

include h0 h1 in
/-- The observable law of the noisy experiment is the product of the observable
law of the original experiment with the noise law. -/
theorem noisy_law :
    (experimentLaw μ (noisyEstimator A M h0 h1) q).map noisyView =
      ((experimentLaw μ A q).map plainView).prod (seedNoise ε M) := by
  have := seedNoise_probability M h0 h1
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf measurable_noisyView, lintegral_prod _ hf.aemeasurable,
    lintegral_map hf.lintegral_prod_right' measurable_plainView]
  exact noisy_lintegral μ A M h0 h1 q f hf

/-- The output of the noisy estimator, seen through `noisyView`. -/
def noisyOutput (A : AdaptiveEstimator R) (p : (R × ProcessTape) × ℝ) : ℝ := A.output p.1 + p.2

theorem measurable_noisyOutput : Measurable (noisyOutput A) :=
  (A.output_measurable.comp measurable_fst).add measurable_snd

theorem populationOutput_noisy :
    populationOutput (noisyEstimator A M h0 h1) = noisyOutput A ∘ noisyView := rfl

theorem populationOutput_plain : populationOutput A = A.output ∘ plainView := rfl

theorem noisy_expectedWork :
    expectedWork μ (noisyEstimator A M h0 h1) q = expectedWork μ A q := by
  have := seedNoise_probability M h0 h1
  have hw : Measurable (fun p : (R × ProcessTape) × ℝ => totalProcessWork p.1.2) :=
    measurable_totalProcessWork (fun p : (R × ProcessTape) × ℝ => p.1.2) (fun n b =>
      measurableSet_eq_fun ((measurable_pi_apply n).comp (measurable_snd.comp measurable_fst))
        measurable_const)
  have h := noisy_lintegral μ A M h0 h1 q _ hw
  simp only [lintegral_const, measure_univ, mul_one] at h
  exact h

theorem noisy_clip_squaredRisk {θ ρ : ℝ} (hθ0 : 0 ≤ θ) (hθρ : θ ≤ ρ) :
    squaredRisk (experimentLaw μ (noisyEstimator A M h0 h1) q)
        (fun z => clipEstimate ρ (populationOutput (noisyEstimator A M h0 h1) z)) θ ≤
      squaredRisk (experimentLaw μ A q) (populationOutput A) θ + ENNReal.ofReal (ε * ρ ^ 2) := by
  have hf : Measurable (fun p : (R × ProcessTape) × ℝ =>
      ENNReal.ofReal ((clipEstimate ρ (noisyOutput A p) - θ) ^ 2)) :=
    ((((measurable_clip ρ).comp (measurable_noisyOutput A)).sub measurable_const).pow_const
      2).ennreal_ofReal
  have h := noisy_lintegral μ A M h0 h1 q _ hf
  unfold squaredRisk
  rw [show (∫⁻ x, ENNReal.ofReal
      ((clipEstimate ρ (populationOutput (noisyEstimator A M h0 h1) x) - θ) ^ 2)
        ∂experimentLaw μ (noisyEstimator A M h0 h1) q) =
      ∫⁻ w, ENNReal.ofReal ((clipEstimate ρ (noisyOutput A (noisyView w)) - θ) ^ 2)
        ∂experimentLaw μ (noisyEstimator A M h0 h1) q from rfl, h]
  calc
    _ ≤ ∫⁻ y, (ENNReal.ofReal ((populationOutput A y - θ) ^ 2) + ENNReal.ofReal (ε * ρ ^ 2))
        ∂experimentLaw μ A q :=
      lintegral_mono fun y => noisy_clip_loss M h0 hθ0 hθρ (populationOutput A y)
    _ = _ := by
      rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]

/-- Integrability and the mean transfer from integrability alone. -/
theorem noisy_mean (hA : Integrable (populationOutput A) (experimentLaw μ A q)) :
    Integrable (populationOutput (noisyEstimator A M h0 h1))
        (experimentLaw μ (noisyEstimator A M h0 h1) q) ∧
      (∫ z, populationOutput (noisyEstimator A M h0 h1) z
          ∂experimentLaw μ (noisyEstimator A M h0 h1) q) =
        ∫ z, populationOutput A z ∂experimentLaw μ A q := by
  have hP : Integrable A.output ((experimentLaw μ A q).map plainView) :=
    (integrable_map_measure A.output_measurable.aestronglyMeasurable
      measurable_plainView.aemeasurable).2 hA
  have hN := noisy_integrable ε M hP
  have hNm : Integrable (noisyOutput A) ((experimentLaw μ (noisyEstimator A M h0 h1) q).map noisyView) := by
    rw [noisy_law μ A M h0 h1 q]
    exact hN
  refine ⟨(integrable_map_measure (measurable_noisyOutput A).aestronglyMeasurable
    measurable_noisyView.aemeasurable).1 hNm, ?_⟩
  show ∫ z, noisyOutput A (noisyView z) ∂experimentLaw μ (noisyEstimator A M h0 h1) q =
    ∫ z, A.output (plainView z) ∂experimentLaw μ A q
  rw [← integral_map measurable_noisyView.aemeasurable
      (measurable_noisyOutput A).aestronglyMeasurable,
    ← integral_map measurable_plainView.aemeasurable A.output_measurable.aestronglyMeasurable,
    noisy_law μ A M h0 h1 q]
  exact noisy_integral M h0 h1 hP

/-- Square integrability transfers. -/
theorem noisy_memLp_two (hA : MemLp (populationOutput A) 2 (experimentLaw μ A q)) :
    MemLp (populationOutput (noisyEstimator A M h0 h1)) 2
      (experimentLaw μ (noisyEstimator A M h0 h1) q) := by
  have hP : MemLp A.output 2 ((experimentLaw μ A q).map plainView) :=
    (memLp_map_measure_iff A.output_measurable.aestronglyMeasurable
      measurable_plainView.aemeasurable).2 hA
  have hN := noisy_memLp ε M hP
  have hNm : MemLp (noisyOutput A) 2
      ((experimentLaw μ (noisyEstimator A M h0 h1) q).map noisyView) := by
    rw [noisy_law μ A M h0 h1 q]
    exact hN
  exact (memLp_map_measure_iff (measurable_noisyOutput A).aestronglyMeasurable
    measurable_noisyView.aemeasurable).1 hNm

/-- The variance identity from square integrability alone. -/
theorem noisy_variance_eq (hA : MemLp (populationOutput A) 2 (experimentLaw μ A q)) :
    ProbabilityTheory.variance (populationOutput (noisyEstimator A M h0 h1))
        (experimentLaw μ (noisyEstimator A M h0 h1) q) =
      ProbabilityTheory.variance (populationOutput A) (experimentLaw μ A q) + ε * M ^ 2 := by
  have hP : MemLp A.output 2 ((experimentLaw μ A q).map plainView) :=
    (memLp_map_measure_iff A.output_measurable.aestronglyMeasurable
      measurable_plainView.aemeasurable).2 hA
  rw [populationOutput_noisy, populationOutput_plain,
    ← ProbabilityTheory.variance_map (measurable_noisyOutput A).aemeasurable
      measurable_noisyView.aemeasurable,
    ← ProbabilityTheory.variance_map A.output_measurable.aemeasurable
      measurable_plainView.aemeasurable,
    noisy_law μ A M h0 h1 q]
  exact noisy_variance M h0 h1 hP

end Law

end ThresholdHC.ClippingBoundary
