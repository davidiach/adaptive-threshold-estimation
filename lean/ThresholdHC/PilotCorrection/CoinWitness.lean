import ThresholdHC.PilotCorrection.Mixture

/-! The nonvacuity witness: one gap `d = 1/2` and an internal fair coin.

The observation space is `Bool × Bool`: the first coordinate is the single
flip, which equals the sign when `d = 1/2`, and the second is an internal fair
coin. With `Y` the indicator of the flip and `Z` the `±1` value of the
internal coin, `Var_q(Y - βZ) = q - q ^ 2 + β ^ 2`. -/

noncomputable section
namespace ThresholdHC.PilotCorrection
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem fairCoin_isProbability : IsProbabilityMeasure fairCoin := by
  constructor
  simp only [fairCoin, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul,
    mul_one]
  exact ENNReal.inv_two_add_inv_two

theorem integral_fairCoin (g : Bool → ℝ) :
    (∫ c, g c ∂fairCoin) = (g true + g false) / 2 := by
  unfold fairCoin
  have h2 : (2⁻¹ : ℝ≥0∞) ≠ ∞ := ENNReal.inv_ne_top.mpr two_ne_zero
  have hi : ∀ b : Bool, Integrable g ((2⁻¹ : ℝ≥0∞) • Measure.dirac b) := fun b =>
    (Integrable.of_finite (μ := Measure.dirac b)).smul_measure h2
  rw [integral_add_measure (hi true) (hi false),
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul]
  ring

theorem integral_dirac_prod_fairCoin (b : Bool) (g : Bool × Bool → ℝ) :
    (∫ ω, g ω ∂(Measure.dirac b).prod fairCoin) = (g (b, true) + g (b, false)) / 2 := by
  rw [Measure.dirac_prod, integral_map measurable_prodMk_left.aemeasurable
    (measurable_of_finite g).aestronglyMeasurable]
  exact integral_fairCoin (fun c => g (b, c))

theorem coinWitness_prob (b : Bool) : IsProbabilityMeasure ((Measure.dirac b).prod fairCoin) := by
  have := fairCoin_isProbability
  infer_instance

/-- The witness features satisfy `FixedFeatures` with `v = 1`. -/
theorem coinWitness_features {ρ : ℝ} (hρ : 0 ≤ ρ) :
    FixedFeatures (fun _ : Fin 1 => (1 : ℝ)) ρ
      (fun _ => (Measure.dirac true).prod fairCoin)
      (fun _ => (Measure.dirac false).prod fairCoin)
      (fun ω : Bool × Bool => if ω.1 then (1 : ℝ) else 0)
      (fun ω : Bool × Bool => if ω.2 then (1 : ℝ) else -1) 1 := by
  have := fairCoin_isProbability
  have hπ : ∀ i : Fin 1, (0 : ℝ) ≤ (fun _ : Fin 1 => (1 : ℝ)) i := fun _ => zero_le_one
  refine ⟨hπ, by simp, hρ, measurable_of_finite _, measurable_of_finite _,
    fun _ => ⟨MemLp.of_discrete, MemLp.of_discrete, MemLp.of_discrete, MemLp.of_discrete⟩,
    one_pos, ?_⟩
  intro q hq
  have hint : ∀ g : Bool × Bool → ℝ,
      (∫ ω, g ω ∂coinLaw (fun _ : Fin 1 => (1 : ℝ))
        (fun _ => (Measure.dirac true).prod fairCoin)
        (fun _ => (Measure.dirac false).prod fairCoin) q) =
        ∑ i : Fin 1, (1 * (((g (true, true) + g (true, false)) / 2) -
          (g (false, true) + g (false, false)) / 2) * q i +
          1 * ((g (false, true) + g (false, false)) / 2)) := by
    intro g
    rw [integral_coinLaw _ _ _ hπ (fun _ => ⟨Integrable.of_finite, Integrable.of_finite⟩) hq.1]
    simp only [integral_dirac_prod_fairCoin]
  refine ⟨?_, ?_, ?_⟩
  · rw [hint]
    simp [signMass]
  · rw [hint]
    norm_num
  · rw [hint]
    norm_num

/-- The witness variance `Var_q(Y - βZ) = q - q ^ 2 + β ^ 2` on `Q`. -/
theorem coinWitness_variance {ρ : ℝ} (hρ : 0 ≤ ρ) {q : Fin 1 → ℝ}
    (hq : q ∈ rarityPolytope (fun _ : Fin 1 => (1 : ℝ)) ρ) (β : ℝ) :
    variance (fun ω => (fun ω : Bool × Bool => if ω.1 then (1 : ℝ) else 0) ω -
        β * (fun ω : Bool × Bool => if ω.2 then (1 : ℝ) else -1) ω)
      (coinLaw (fun _ : Fin 1 => (1 : ℝ))
        (fun _ => (Measure.dirac true).prod fairCoin)
        (fun _ => (Measure.dirac false).prod fairCoin) q) =
      q 0 - q 0 ^ 2 + β ^ 2 := by
  have := fairCoin_isProbability
  have hP : ∀ b : Bool, IsProbabilityMeasure ((Measure.dirac b).prod fairCoin) :=
    coinWitness_prob
  rw [variance_coinLaw (coinWitness_features hρ) hq β]
  simp only [integral_dirac_prod_fairCoin, signMass, Fin.sum_univ_one]
  norm_num

theorem coinWitness_holds : CoinWitnessStatement := by
  intro ρ hρ hρ2
  dsimp only
  have hq : (fun _ : Fin 1 => ρ) ∈ rarityPolytope (fun _ : Fin 1 => (1 : ℝ)) ρ :=
    ⟨fun _ => ⟨hρ.le, by linarith⟩, by simp⟩
  refine ⟨fun _ => coinWitness_prob true, fun _ => coinWitness_prob false,
    coinWitness_features hρ.le, fun _ => ρ, hq, fun β => ?_⟩
  have hP : ∀ b : Bool, IsProbabilityMeasure ((Measure.dirac b).prod fairCoin) :=
    coinWitness_prob
  rw [coinWitness_variance hρ.le hq β]
  nlinarith [sq_nonneg β]

end ThresholdHC.PilotCorrection
