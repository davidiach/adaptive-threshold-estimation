import ThresholdHC.KnownLawPlanner.PlanTightQuantileRate
import ThresholdHC.ArbitraryLawAdaptation.ZeroQuantile

/-! The plan of a reference law with mass at zero.

Let `α = z₀ δ₀ + (1 - z₀) η`, with `η` a probability law of positive gaps.
The planner puts the mass at zero entirely in the unresolved part. Its split
is the quantile split of `η` at the conditional rarity
`r = (ρ - z₀)/(1 - z₀)`, scaled by `1 - z₀`: the core `σ`, the resolved tail
`τ` on gaps at least `h = B^{-1/2}` and the positive unresolved part `ζ` on
gaps at most `h`. The unresolved mass of the design is `z = z₀ + ζ(univ)`.
It enters the level prices through the term `2 z M`, and the terminal rule
and the fallback through the bound `z̄ ≥ z` of the enclosure.

The capped design value `min{ρ, z + h H + h √(ρ Γ_σ)}` is the zero-atom
quantile value `Q_α`, which is at most `4 K_α`, and `ρ/(1 + √B) ≤ K_α`. For a
tight enclosure and weights within a factor `θ` of the optimal ones,

  `min{ρ/2, √certificate} ≤ (1 + 4 max{4096, 8 · 28000 √θ}) K_α(B)`,

and the constant fallback obeys the same bound. With dyadic upper square
roots, `θ = 2`, the coefficient is `C₀ = 1 + 4 max{4096, 8 √2 C_sum}` with
`C_sum = 28000`, and the reported radius is at most `6 C₀ K_α(B)`.

These are statements about the numbers the planner computes. The experiment
of the upper theorem has positive gaps only: a coin of gap zero, and the
fair-coin likelihood the bank would use for it, are not part of it. -/

noncomputable section
open MeasureTheory Set Real
open scoped NNReal ENNReal BigOperators

namespace ThresholdHC.KnownLawPlanner
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTailQuantile ThresholdHC.EntropyTailUpper
open ThresholdHC.EntropyTailAssembly ThresholdHC.EntropyTailExecution
open ThresholdHC.ArbitraryLawAdaptation

/-- The tail modulus scales with the measure. -/
theorem tailModulus_smul (ν : Measure Gap) {c : ℝ} (hc : 0 ≤ c) (h : ℝ) :
    tailModulus (ENNReal.ofReal c • ν) h = c * tailModulus ν h := by
  unfold tailModulus
  rw [integral_smul_measure, ENNReal.toReal_ofReal hc, smul_eq_mul]

/-- The cost entropy scales with the measure. -/
theorem scaled_measureCostEntropy (σ : Measure Gap) {c : ℝ} (hc : 0 ≤ c) :
    measureCostEntropy (ENNReal.ofReal c • σ) = ENNReal.ofReal c * measureCostEntropy σ := by
  have hb : ∀ j : ℕ, bandCost (ENNReal.ofReal c • σ) j = c * bandCost σ j := fun j => by
    simp only [bandCost, Measure.restrict_smul, integral_smul_measure,
      ENNReal.toReal_ofReal hc, smul_eq_mul]
  unfold measureCostEntropy
  rw [ENNReal.mul_iSup]
  apply iSup_congr
  intro n
  simp only [hb, costEntropy_smul, ENNReal.ofReal_mul hc]

/-- The elementary floor of the selection functional of a law with mass at
zero: `ρ/(1 + √B) ≤ K_α(B)`. -/
theorem zero_selection_floor (η : Measure Gap) [IsProbabilityMeasure η] {z ρ B : ℝ}
    (hρ : 0 < ρ) (hρ2 : ρ ≤ 1/2) (hB : 0 < B) :
    ENNReal.ofReal (ρ/(1+sqrt B)) ≤ zeroSelection (zeroAtomLaw z η) ρ B := by
  have hpos : (0:ℝ) < 1 + sqrt B := by positivity
  have hself : ρ/(1+sqrt B) ≤ ρ := div_le_self hρ.le (by linarith [sqrt_nonneg B])
  rcases le_total ρ (1 - z) with hcase | hcase
  · have hc : 0 < 1 - z := lt_of_lt_of_le hρ hcase
    have hr : 0 < ρ/(1-z) := div_pos hρ hc
    have hr1 : ρ/(1-z) ≤ 1 := (div_le_one hc).mpr hcase
    have hfl := selection_floor η hr hr1 hB
    have hcr : (1 - z) * (ρ/(1-z)) ≤ ρ := le_of_eq (by field_simp)
    have h := positive_selection_le_zeroSelection η (B := B) (by linarith : z < 1) hr.le hcr
    refine le_trans ?_ h
    have he : ρ/(1+sqrt B) = (1 - z) * (ρ/(1-z)/(1+sqrt B)) := by
      field_simp
    rw [he, ENNReal.ofReal_mul hc.le]
    gcongr
  · have h := min_zeroMass_le_zeroSelection (zeroAtomLaw z η) hρ hB
    rw [zeroAtomLaw_zero_atom] at h
    exact le_trans (le_min (ENNReal.ofReal_le_ofReal hself)
      (ENNReal.ofReal_le_ofReal (by linarith))) h

/-- The zero-atom quantile value in the design integrals of the scaled
split: `Q_α = min{ρ, z₀ + ζ(univ) + h H + h √(ρ Γ_σ)}`. -/
theorem zero_split_value (η : Measure Gap) [IsProbabilityMeasure η] (σ τ ζ : Measure Gap)
    [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] {z₀ ρ B : ℝ} (hz0 : 0 ≤ z₀)
    (hzρ : z₀ < ρ) (hρ1 : ρ ≤ 1) (hB : 0 < B)
    (hcore : σ = ENNReal.ofReal (1 - z₀) • quantileCore η (conditionalRarity ρ z₀))
    (htail : τ+ζ = ENNReal.ofReal (1 - z₀) • quantileTail η (conditionalRarity ρ z₀))
    (hτs : ∀ᵐ d : Gap ∂τ, budgetScale B ≤ (d:ℝ)) (hζs : ∀ᵐ d : Gap ∂ζ, (d:ℝ) ≤ budgetScale B) :
    zeroQuantileValue z₀ η ρ B =
      ENNReal.ofReal (min ρ (z₀ + ζ.real univ + budgetScale B * (∫ d : Gap, (d:ℝ)⁻¹ ∂τ) +
        budgetScale B * sqrt (ρ * (measureCostEntropy σ).toReal))) := by
  have hc : 0 < 1 - z₀ := by linarith
  have hρ0 : 0 < ρ := lt_of_le_of_lt hz0 hzρ
  have hh := budgetScale_pos hB
  have hr : 0 < conditionalRarity ρ z₀ := div_pos (by linarith) hc
  have hr1 : conditionalRarity ρ z₀ ≤ 1 := (div_le_one hc).mpr (by linarith)
  have ht := (quantileThreshold_properties η hr hr1).1
  have hs : ∀ᵐ d : Gap ∂σ, quantileThreshold η (conditionalRarity ρ z₀) ≤ (d:ℝ) := by
    rw [hcore]
    exact Measure.ae_smul_measure (quantileCore_support η (conditionalRarity ρ z₀)) _
  have hG : measureCostEntropy σ ≠ ⊤ := (measureCostEntropy_lt_top_of_support σ ht hs).ne
  have hσG : measureCostEntropy σ =
      ENNReal.ofReal (1 - z₀) * measureCostEntropy (quantileCore η (conditionalRarity ρ z₀)) := by
    rw [hcore, scaled_measureCostEntropy _ hc.le]
  have hH0 : 0 ≤ ∫ d : Gap, (d:ℝ)⁻¹ ∂τ := integral_nonneg fun d => inv_nonneg.mpr d.property.1.le
  have htm : (1 - z₀) * tailModulus (quantileTail η (conditionalRarity ρ z₀)) (budgetScale B) =
      budgetScale B * (∫ d : Gap, (d:ℝ)⁻¹ ∂τ) + ζ.real univ := by
    rw [← tailModulus_smul _ hc.le, ← htail, tailModulus_add τ ζ hh.le,
      tailModulus_eq_inverseCost τ hτs, tailModulus_eq_mass ζ hζs]
  have h1 : 0 ≤ budgetScale B * (∫ d : Gap, (d:ℝ)⁻¹ ∂τ) + ζ.real univ :=
    add_nonneg (mul_nonneg hh.le hH0) measureReal_nonneg
  have h2 : 0 ≤ budgetScale B * sqrt (ρ * (measureCostEntropy σ).toReal) :=
    mul_nonneg hh.le (sqrt_nonneg _)
  unfold zeroQuantileValue
  rw [ite_eq_right (not_le.mpr hzρ), ← hσG, entropy_root_eq_ofReal hG hρ0.le hh.le,
    ← ENNReal.ofReal_mul hc.le, htm, ← ENNReal.ofReal_add h1 h2,
    ← ENNReal.ofReal_add hz0 (add_nonneg h1 h2)]
  have he : z₀ + (budgetScale B * (∫ d : Gap, (d:ℝ)⁻¹ ∂τ) + ζ.real univ +
      budgetScale B * sqrt (ρ * (measureCostEntropy σ).toReal)) =
      z₀ + ζ.real univ + budgetScale B * (∫ d : Gap, (d:ℝ)⁻¹ ∂τ) +
        budgetScale B * sqrt (ρ * (measureCostEntropy σ).toReal) := by ring
  rw [he]
  exact (ENNReal.ofReal_mono.map_min).symm

/-- The oracle side of the zero-atom design in real numbers. The selection
functional of `α` is `ofReal K` for a real `K` with `ρ/(1 + √B) ≤ K`, and the
capped design value is at most `4 K`. -/
theorem zero_split_comparison (η : Measure Gap) [IsProbabilityMeasure η] (σ τ ζ : Measure Gap)
    [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] {z₀ ρ B : ℝ} (hz0 : 0 ≤ z₀)
    (hzρ : z₀ < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B)
    (hcore : σ = ENNReal.ofReal (1 - z₀) • quantileCore η (conditionalRarity ρ z₀))
    (htail : τ+ζ = ENNReal.ofReal (1 - z₀) • quantileTail η (conditionalRarity ρ z₀))
    (hτs : ∀ᵐ d : Gap ∂τ, budgetScale B ≤ (d:ℝ)) (hζs : ∀ᵐ d : Gap ∂ζ, (d:ℝ) ≤ budgetScale B) :
    ∃ K : ℝ, 0 ≤ K ∧ zeroSelection (zeroAtomLaw z₀ η) ρ B = ENNReal.ofReal K ∧
      ρ/(1+sqrt B) ≤ K ∧
      min ρ (z₀ + ζ.real univ + budgetScale B * (∫ d : Gap, (d:ℝ)⁻¹ ∂τ) +
        budgetScale B * sqrt (ρ * (measureCostEntropy σ).toReal)) ≤ 4 * K := by
  have hρ0 : 0 < ρ := lt_of_le_of_lt hz0 hzρ
  have hKtop : zeroSelection (zeroAtomLaw z₀ η) ρ B ≠ ⊤ :=
    ((min_le_left _ _).trans_lt ENNReal.ofReal_lt_top).ne
  have hK : zeroSelection (zeroAtomLaw z₀ η) ρ B =
      ENNReal.ofReal (zeroSelection (zeroAtomLaw z₀ η) ρ B).toReal :=
    (ENNReal.ofReal_toReal hKtop).symm
  have hK0 : 0 ≤ (zeroSelection (zeroAtomLaw z₀ η) ρ B).toReal := ENNReal.toReal_nonneg
  refine ⟨(zeroSelection (zeroAtomLaw z₀ η) ρ B).toReal, hK0, hK, ?_, ?_⟩
  · have hf := zero_selection_floor η (z := z₀) hρ0 (by linarith) hB
    rw [hK] at hf
    exact (ENNReal.ofReal_le_ofReal_iff hK0).mp hf
  · have h4 := zeroQuantileValue_le_four η hz0 hρ0 hρ4 hB
    have he : (4:ℝ≥0∞) = ENNReal.ofReal 4 := by norm_num
    rw [zero_split_value η σ τ ζ hz0 hzρ (by linarith) hB hcore htail hτs hζs, hK, he,
      ← ENNReal.ofReal_mul (by norm_num)] at h4
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h4

/-- The rate of the plan of a reference law with mass at zero. Outside the
constant fallback, the smaller of `ρ/2` and the certified risk of the plan is
at most `(1 + 4 max{4096, 8 · 28000 √θ}) K_α(B)`. -/
theorem zero_atom_plan_rate (η : Measure Gap) [IsProbabilityMeasure η] (σ τ ζ : Measure Gap)
    [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ]
    {z₀ ρ B θ : ℝ} {N : ℕ} (hz0 : 0 ≤ z₀) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B)
    (hθ : 0 ≤ θ)
    (hcore : σ = ENNReal.ofReal (1 - z₀) • quantileCore η (conditionalRarity ρ z₀))
    (htail : τ+ζ = ENNReal.ofReal (1 - z₀) • quantileTail η (conditionalRarity ρ z₀))
    (hτs : ∀ᵐ d : Gap ∂τ, budgetScale B ≤ (d:ℝ)) (hζs : ∀ᵐ d : Gap ∂ζ, (d:ℝ) ≤ budgetScale B)
    (hN : bandEdge N < quantileThreshold η (conditionalRarity ρ z₀))
    (E : SplitEnclosure σ τ ζ N) (hE : E.Tight (z₀ + ζ.real univ))
    (hz : 2048 * E.unresolved ≤ ρ)
    (w : Fin (planTerminal hρ B E.unresolved + 1) → ℝ)
    (hlow : ∀ i, sqrt (17*levelAccuracy ρ i.val /
      planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ)
        (planTerminal hρ B E.unresolved) i) ≤ w i)
    (hup : ∀ i, w i ≤ θ * sqrt (17*levelAccuracy ρ i.val /
      planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ)
        (planTerminal hρ B E.unresolved) i)) :
    ENNReal.ofReal (min (ρ/2) (sqrt (planCertificate ρ (planRates B
        (planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ)
          (planTerminal hρ B E.unresolved)) w)))) ≤
      ENNReal.ofReal (1 + 4 * max 4096 (224000 * sqrt θ)) *
        zeroSelection (zeroAtomLaw z₀ η) ρ B := by
  have hζ0 : 0 ≤ ζ.real univ := measureReal_nonneg
  have hzE : z₀ + ζ.real univ ≤ E.unresolved := hE.2.2.1
  have hzρ : z₀ < ρ := by linarith
  have hc : 0 < 1 - z₀ := by linarith
  have hr : 0 < conditionalRarity ρ z₀ := div_pos (by linarith) hc
  have hr1 : conditionalRarity ρ z₀ ≤ 1 := (div_le_one hc).mpr (by linarith)
  have ht := (quantileThreshold_properties η hr hr1).1
  have hs : ∀ᵐ d : Gap ∂σ, quantileThreshold η (conditionalRarity ρ z₀) ≤ (d:ℝ) := by
    rw [hcore]
    exact Measure.ae_smul_measure (quantileCore_support η (conditionalRarity ρ z₀)) _
  have hlaw : σ+τ+ζ = ENNReal.ofReal (1 - z₀) • η := by
    rw [add_assoc, htail, hcore, ← smul_add, add_comm, quantileTail_add_core η hr hr1]
  have hmass : (σ+τ).real univ + ζ.real univ = 1 - z₀ := by
    rw [← measureReal_add_apply, hlaw, measureReal_def, Measure.smul_apply, measure_univ,
      smul_eq_mul, mul_one, ENNReal.toReal_ofReal hc.le]
  have hm : ρ/128 < (σ+τ).real univ := by linarith
  obtain ⟨K, hK0, hK, hfloor, hQK⟩ :=
    zero_split_comparison η σ τ ζ hz0 hzρ hρ4 hB hcore htail hτs hζs
  rw [hK, ← ENNReal.ofReal_mul (by positivity)]
  rw [add_assoc] at hQK
  exact ENNReal.ofReal_le_ofReal (tight_plan_rate_real σ τ ζ ht hs hN hτs hρ hB hθ hm E hE hz
    hK0 hfloor (by norm_num) hQK w hlow hup)

/-- The fallback for a large unresolved mass. When `2048 z̄ > ρ` the planner
returns the constant `ρ/2`, which obeys the bound of the plan. The mass at
zero may be any `z₀ ≥ 0`; the split is used only when `2 z₀ < ρ`. -/
theorem zero_atom_fallback_rate (η : Measure Gap) [IsProbabilityMeasure η] (σ τ ζ : Measure Gap)
    [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ]
    {z₀ ρ B : ℝ} {N : ℕ} (θ : ℝ) (hz0 : 0 ≤ z₀) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B)
    (hcore : σ = ENNReal.ofReal (1 - z₀) • quantileCore η (conditionalRarity ρ z₀))
    (htail : τ+ζ = ENNReal.ofReal (1 - z₀) • quantileTail η (conditionalRarity ρ z₀))
    (hτs : ∀ᵐ d : Gap ∂τ, budgetScale B ≤ (d:ℝ)) (hζs : ∀ᵐ d : Gap ∂ζ, (d:ℝ) ≤ budgetScale B)
    (E : SplitEnclosure σ τ ζ N) (hE : E.Tight (z₀ + ζ.real univ))
    (hz : ρ < 2048 * E.unresolved) :
    ENNReal.ofReal (ρ/2) ≤
      ENNReal.ofReal (1 + 4 * max 4096 (224000 * sqrt θ)) *
        zeroSelection (zeroAtomLaw z₀ η) ρ B := by
  have hh := budgetScale_pos hB
  have hζ0 : 0 ≤ ζ.real univ := measureReal_nonneg
  have hH0 : 0 ≤ ∫ d : Gap, (d:ℝ)⁻¹ ∂τ := integral_nonneg fun d => inv_nonneg.mpr d.property.1.le
  have hC : (1:ℝ) ≤ 1 + 4 * max 4096 (224000 * sqrt θ) := by
    have := le_max_left (4096:ℝ) (224000 * sqrt θ)
    linarith
  rcases le_total ρ (2*z₀) with hbig | hsmall
  · -- `z₀ ≥ ρ/2`: `ρ/2 ≤ min{ρ, z₀} ≤ K_α`.
    have hfl := min_zeroMass_le_zeroSelection (zeroAtomLaw z₀ η) hρ hB
    rw [zeroAtomLaw_zero_atom] at hfl
    have h1 : ENNReal.ofReal (ρ/2) ≤ zeroSelection (zeroAtomLaw z₀ η) ρ B :=
      le_trans (le_min (ENNReal.ofReal_le_ofReal (by linarith))
        (ENNReal.ofReal_le_ofReal (by linarith))) hfl
    calc ENNReal.ofReal (ρ/2) ≤ 1 * zeroSelection (zeroAtomLaw z₀ η) ρ B := by rwa [one_mul]
      _ ≤ ENNReal.ofReal (1 + 4 * max 4096 (224000 * sqrt θ)) *
          zeroSelection (zeroAtomLaw z₀ η) ρ B := by
        gcongr
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal hC
  · have hzρ : z₀ < ρ := by linarith
    obtain ⟨K, hK0, hK, -, hQK⟩ :=
      zero_split_comparison η σ τ ζ hz0 hzρ hρ4 hB hcore htail hτs hζs
    rw [hK, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hzU : z₀ + ζ.real univ ≤ z₀ + ζ.real univ +
        budgetScale B * (∫ d : Gap, (d:ℝ)⁻¹ ∂τ) +
        budgetScale B * sqrt (ρ * (measureCostEntropy σ).toReal) := by
      have h1 : 0 ≤ budgetScale B * (∫ d : Gap, (d:ℝ)⁻¹ ∂τ) := mul_nonneg hh.le hH0
      have h2 : 0 ≤ budgetScale B * sqrt (ρ * (measureCostEntropy σ).toReal) :=
        mul_nonneg hh.le (sqrt_nonneg _)
      linarith
    exact fallback_arithmetic (224000 * sqrt θ) hρ.le hK0 (by norm_num) (by norm_num) hzU hQK
      (by linarith [hE.2.2.2.1])

/-- The planned coefficient `C₀ = 1 + 4 max{4096, 8 √2 C_sum}`, as a function
of the multilevel coefficient `C_sum`. -/
def plannedCoefficient (Csum : ℝ) : ℝ := 1 + 4 * max 4096 (8 * sqrt 2 * Csum)

/-- The planned coefficient does not decrease with the multilevel
coefficient. -/
theorem plannedCoefficient_mono {C C' : ℝ} (h : C ≤ C') :
    plannedCoefficient C ≤ plannedCoefficient C' := by
  unfold plannedCoefficient
  have h8 : (0:ℝ) ≤ 8 * sqrt 2 := by positivity
  have := max_le_max (le_refl (4096:ℝ)) (mul_le_mul_of_nonneg_left h h8)
  linarith

/-- The planned coefficient for dyadic weights. With upper square roots
within a factor two, the plan of a reference law with mass at zero has
`min{ρ/2, √certificate} ≤ C₀ K_α(B)`, with `C₀` at the multilevel
coefficient `28000` of the upper theorem. -/
theorem zero_atom_plan_rate_dyadic (η : Measure Gap) [IsProbabilityMeasure η]
    (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ]
    {z₀ ρ B : ℝ} {N : ℕ} (hz0 : 0 ≤ z₀) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B)
    (hcore : σ = ENNReal.ofReal (1 - z₀) • quantileCore η (conditionalRarity ρ z₀))
    (htail : τ+ζ = ENNReal.ofReal (1 - z₀) • quantileTail η (conditionalRarity ρ z₀))
    (hτs : ∀ᵐ d : Gap ∂τ, budgetScale B ≤ (d:ℝ)) (hζs : ∀ᵐ d : Gap ∂ζ, (d:ℝ) ≤ budgetScale B)
    (hN : bandEdge N < quantileThreshold η (conditionalRarity ρ z₀))
    (E : SplitEnclosure σ τ ζ N) (hE : E.Tight (z₀ + ζ.real univ))
    (hz : 2048 * E.unresolved ≤ ρ)
    (w : Fin (planTerminal hρ B E.unresolved + 1) → ℝ)
    (hlow : ∀ i, sqrt (17*levelAccuracy ρ i.val /
      planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ)
        (planTerminal hρ B E.unresolved) i) ≤ w i)
    (hup : ∀ i, w i ≤ 2 * sqrt (17*levelAccuracy ρ i.val /
      planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ)
        (planTerminal hρ B E.unresolved) i)) :
    ENNReal.ofReal (min (ρ/2) (sqrt (planCertificate ρ (planRates B
        (planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ)
          (planTerminal hρ B E.unresolved)) w)))) ≤
      ENNReal.ofReal (plannedCoefficient 28000) * zeroSelection (zeroAtomLaw z₀ η) ρ B := by
  have h := zero_atom_plan_rate η σ τ ζ hz0 hρ hρ4 hB (by norm_num : (0:ℝ) ≤ 2) hcore htail
    hτs hζs hN E hE hz w hlow hup
  have he : 1 + 4 * max 4096 (224000 * sqrt 2) = plannedCoefficient 28000 := by
    unfold plannedCoefficient
    rw [show (224000:ℝ) * sqrt 2 = 8 * sqrt 2 * 28000 by ring]
  rwa [he] at h

/-- The reported radius for dyadic weights. For every relative upper square
root with `κ √8 ≤ 6`, the radius of the plan of a reference law with mass at
zero is at most `C_* K_α(B)`, with `C_* = 6 C₀`. -/
theorem zero_atom_plan_radius_dyadic (η : Measure Gap) [IsProbabilityMeasure η]
    (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ]
    {z₀ ρ B κ r : ℝ} {N : ℕ} (hz0 : 0 ≤ z₀) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B)
    (hcore : σ = ENNReal.ofReal (1 - z₀) • quantileCore η (conditionalRarity ρ z₀))
    (htail : τ+ζ = ENNReal.ofReal (1 - z₀) • quantileTail η (conditionalRarity ρ z₀))
    (hτs : ∀ᵐ d : Gap ∂τ, budgetScale B ≤ (d:ℝ)) (hζs : ∀ᵐ d : Gap ∂ζ, (d:ℝ) ≤ budgetScale B)
    (hN : bandEdge N < quantileThreshold η (conditionalRarity ρ z₀))
    (E : SplitEnclosure σ τ ζ N) (hE : E.Tight (z₀ + ζ.real univ))
    (hz : 2048 * E.unresolved ≤ ρ)
    (w : Fin (planTerminal hρ B E.unresolved + 1) → ℝ)
    (hlow : ∀ i, sqrt (17*levelAccuracy ρ i.val /
      planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ)
        (planTerminal hρ B E.unresolved) i) ≤ w i)
    (hup : ∀ i, w i ≤ 2 * sqrt (17*levelAccuracy ρ i.val /
      planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ)
        (planTerminal hρ B E.unresolved) i))
    (hκ : κ * sqrt 8 ≤ 6)
    (hr : r ≤ κ * sqrt (8 * min (ρ^2/4) (planCertificate ρ (planRates B
      (planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ)
        (planTerminal hρ B E.unresolved)) w)))) :
    ENNReal.ofReal r ≤
      ENNReal.ofReal (6 * plannedCoefficient 28000) * zeroSelection (zeroAtomLaw z₀ η) ρ B :=
  plan_radius_le hρ.le hκ hr
    (zero_atom_plan_rate_dyadic η σ τ ζ hz0 hρ hρ4 hB hcore htail hτs hζs hN E hE hz w hlow hup)

end ThresholdHC.KnownLawPlanner
