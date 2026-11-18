import ThresholdHC.BlindUpper.BudgetChoice

/-! Mixtures of two adaptive estimators.

`mixEstimator p A₀ A₁` first tosses a coin showing `true` with probability
`clip p`, then runs `A₁` on heads and `A₀` on tails. When both estimators use
the same random-seed law, the original experiment's expected work and squared
risk of the mixture are the same mixtures of those of `A₀` and `A₁`: the
simulation identities of `ObservableSimulation.OriginalExperiment` write both
as integrals over the seed and the tapes, and the coin enters only through the
seed. -/
noncomputable section
namespace ThresholdHC.UpperMixture
open MeasureTheory ThresholdHC.CriticalEntropy ThresholdHC.Tier3
open ThresholdHC.Tier6 ThresholdHC.ObservableSimulation ThresholdHC.BlindUpper
open scoped ENNReal

/-- The weight `p`, clipped to `[0, 1]`. -/
def clip (p : ℝ) : ℝ := max 0 (min p 1)

theorem clip_nonneg (p : ℝ) : 0 ≤ clip p := le_max_left _ _

theorem clip_le_one (p : ℝ) : clip p ≤ 1 := max_le (by norm_num) (min_le_right _ _)

theorem clip_eq {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : clip p = p := by
  unfold clip
  rw [min_eq_left h1, max_eq_right h0]

/-- A coin showing `true` with probability `clip p`. -/
def coinLaw (p : ℝ) : Measure Bool :=
  ENNReal.ofReal (clip p) • Measure.dirac true + ENNReal.ofReal (1 - clip p) • Measure.dirac false

instance coinLaw_probability (p : ℝ) : IsProbabilityMeasure (coinLaw p) := by
  constructor
  have h0 := clip_nonneg p
  have h1 := clip_le_one p
  simp only [coinLaw, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add h0 (by linarith)]
  simp

/-- Toss the coin, then run `A₁` on heads and `A₀` on tails. -/
def mixEstimator {R : Type} [MeasurableSpace R] (p : ℝ) (A₀ A₁ : AdaptiveEstimator R) :
    AdaptiveEstimator (Bool × R) where
  randomLaw := (coinLaw p).prod A₀.randomLaw
  probability := by
    have := A₀.probability
    infer_instance
  policy := fun u => if u.1 then A₁.policy u.2 else A₀.policy u.2
  policy_measurable := by
    intro xs a
    have h1 := A₁.policy_measurable xs a
    have h0 := A₀.policy_measurable xs a
    have he : {u : Bool × R | (if u.1 then A₁.policy u.2 else A₀.policy u.2) xs = a} =
        (Prod.fst ⁻¹' {true} ∩ Prod.snd ⁻¹' {r | A₁.policy r xs = a}) ∪
        (Prod.fst ⁻¹' {false} ∩ Prod.snd ⁻¹' {r | A₀.policy r xs = a}) := by
      ext ⟨b, r⟩
      cases b <;> simp
    rw [he]
    exact ((measurable_fst (measurableSet_singleton true)).inter (measurable_snd h1)).union
      ((measurable_fst (measurableSet_singleton false)).inter (measurable_snd h0))
  output := fun z => if z.1.1 then A₁.output (z.1.2, z.2) else A₀.output (z.1.2, z.2)
  output_measurable := by
    apply Measurable.ite
    · exact measurableSet_eq_fun (measurable_fst.comp measurable_fst) measurable_const
    · exact A₁.output_measurable.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
    · exact A₀.output_measurable.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)

/-- An integral against the coin, a seed law and a tape law splits over the coin. -/
theorem lintegral_coin_prod {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    (p : ℝ) (ρ : Measure X) [SFinite ρ] (ν : Measure Y) [SFinite ν]
    (F : (Bool × X) × Y → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ z, F z ∂((coinLaw p).prod ρ).prod ν =
      ENNReal.ofReal (clip p) * ∫⁻ z, F ((true, z.1), z.2) ∂ρ.prod ν +
        ENNReal.ofReal (1 - clip p) * ∫⁻ z, F ((false, z.1), z.2) ∂ρ.prod ν := by
  have hG : Measurable (fun x : Bool × X => ∫⁻ y, F (x, y) ∂ν) := hF.lintegral_prod_right'
  have hT : ∀ b : Bool, ∫⁻ z, F ((b, z.1), z.2) ∂ρ.prod ν =
      ∫⁻ r, ∫⁻ y, F ((b, r), y) ∂ν ∂ρ := fun b =>
    lintegral_prod _ (hF.comp ((measurable_const.prodMk (measurable_fst)).prodMk
      measurable_snd)).aemeasurable
  rw [lintegral_prod _ hF.aemeasurable, lintegral_prod _ hG.aemeasurable, hT true, hT false]
  simp only [coinLaw, lintegral_add_measure, lintegral_smul_measure, lintegral_dirac]
  rfl

section Mixture
variable {R : Type} [MeasurableSpace R]

theorem mix_expectedWork (p : ℝ) (A₀ A₁ : AdaptiveEstimator R)
    (h : A₁.randomLaw = A₀.randomLaw) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    expectedWork μ (mixEstimator p A₀ A₁) q =
      ENNReal.ofReal (clip p) * expectedWork μ A₁ q +
        ENNReal.ofReal (1 - clip p) * expectedWork μ A₀ q := by
  have := A₀.probability
  rw [original_expectedWork_simulation, original_expectedWork_simulation μ A₁,
    original_expectedWork_simulation μ A₀]
  unfold originalSimulationLaw
  rw [h]
  have hm : Measurable (fun z : (Bool × R) × (ℕ → ℕ → Bool) =>
      populationPath ((mixEstimator p A₀ A₁).policy z.1) z.2) :=
    measurable_seeded_populationPath (mixEstimator p A₀ A₁).policy
      (fun xs => measurable_to_countable' ((mixEstimator p A₀ A₁).policy_measurable xs))
  have hF := measurable_totalProcessWork
    (fun z : (Bool × R) × (ℕ → ℕ → Bool) => populationPath ((mixEstimator p A₀ A₁).policy z.1) z.2)
    (fun n b => measurableSet_eq_fun ((measurable_pi_apply n).comp hm) measurable_const)
  rw [show (mixEstimator p A₀ A₁).randomLaw = (coinLaw p).prod A₀.randomLaw from rfl]
  rw [lintegral_coin_prod p A₀.randomLaw _ _ hF]
  rfl

theorem mix_squaredRisk (p : ℝ) (A₀ A₁ : AdaptiveEstimator R)
    (h : A₁.randomLaw = A₀.randomLaw) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (a : ℝ) :
    squaredRisk (experimentLaw μ (mixEstimator p A₀ A₁) q)
        (populationOutput (mixEstimator p A₀ A₁)) a =
      ENNReal.ofReal (clip p) * squaredRisk (experimentLaw μ A₁ q) (populationOutput A₁) a +
        ENNReal.ofReal (1 - clip p) * squaredRisk (experimentLaw μ A₀ q) (populationOutput A₀) a := by
  have := A₀.probability
  rw [original_squaredRisk_simulation, original_squaredRisk_simulation μ A₁,
    original_squaredRisk_simulation μ A₀]
  unfold originalSimulationLaw
  rw [h]
  have hm : Measurable (fun z : (Bool × R) × (ℕ → ℕ → Bool) =>
      (z.1, populationPath ((mixEstimator p A₀ A₁).policy z.1) z.2)) :=
    measurable_fst.prodMk (measurable_seeded_populationPath (mixEstimator p A₀ A₁).policy
      (fun xs => measurable_to_countable' ((mixEstimator p A₀ A₁).policy_measurable xs)))
  have hO : Measurable (fun z : (Bool × R) × ProcessTape =>
      ENNReal.ofReal (((mixEstimator p A₀ A₁).output z - a) ^ 2)) :=
    (((mixEstimator p A₀ A₁).output_measurable.sub measurable_const).pow_const 2).ennreal_ofReal
  have hF : Measurable (fun z : (Bool × R) × (ℕ → ℕ → Bool) =>
      ENNReal.ofReal (((mixEstimator p A₀ A₁).output
        (z.1, populationPath ((mixEstimator p A₀ A₁).policy z.1) z.2) - a) ^ 2)) := hO.comp hm
  rw [show (mixEstimator p A₀ A₁).randomLaw = (coinLaw p).prod A₀.randomLaw from rfl,
    lintegral_coin_prod p A₀.randomLaw _ _ hF]
  rfl

end Mixture

end ThresholdHC.UpperMixture
