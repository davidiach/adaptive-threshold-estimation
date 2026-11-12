import ThresholdHC.KnownLawPlanner.PlanZeroAtomRate

/-! The planner end to end.

The rate theorems are stated for a split `σ + τ + ζ` with hypotheses that
identify it as the quantile split cut at the budget scale. Here the split is
constructed, so those hypotheses are met by every law, and the validity of
the planner's output is combined with its rate:

* for every tight enclosure of the quantile split and all weights within a
  factor `θ` of the optimal ones, the planner's output, the plan or the
  constant fallback, has budget `B` and risk at most
  `(1 + (8/5) max{4096, 8 · 28000 √θ}) K_{μ,ρ}(B)`;
* with the exact integrals and the optimal weights, for every probability law
  `μ` of positive gaps, `0 < ρ ≤ 1/4` and `B > 0`, the minimax risk is at
  most `44801 K_{μ,ρ}(B)`.

For a reference law with mass at zero, the scaled quantile split exists and
its exact integrals, with the mass at zero added to the unresolved mass, are
a tight enclosure. -/

noncomputable section
open MeasureTheory Set Real
open scoped NNReal ENNReal BigOperators

namespace ThresholdHC.KnownLawPlanner
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTailQuantile ThresholdHC.EntropyTailUpper
open ThresholdHC.EntropyTailAssembly ThresholdHC.EntropyTailExecution
open ThresholdHC.RareAboveTwo ThresholdHC.ArbitraryLawAdaptation

/-- A finite measure is cut at a gap `h` into the part on gaps at least `h`
and the part on gaps below `h`. -/
theorem exists_cut (ν : Measure Gap) [IsFiniteMeasure ν] (h : ℝ) :
    ∃ τ ζ : Measure Gap, IsFiniteMeasure τ ∧ IsFiniteMeasure ζ ∧ τ+ζ = ν ∧
      (∀ᵐ d : Gap ∂τ, h ≤ (d:ℝ)) ∧ (∀ᵐ d : Gap ∂ζ, (d:ℝ) ≤ h) := by
  have hS : MeasurableSet {d : Gap | h ≤ (d:ℝ)} :=
    measurableSet_le measurable_const measurable_subtype_coe
  refine ⟨ν.restrict {d : Gap | h ≤ (d:ℝ)}, ν.restrict {d : Gap | h ≤ (d:ℝ)}ᶜ, inferInstance,
    inferInstance, Measure.restrict_add_restrict_compl hS, ae_restrict_mem hS, ?_⟩
  filter_upwards [ae_restrict_mem hS.compl] with d hd
  exact (not_le.mp hd).le

/-- The quantile split of a law of positive gaps, cut at the budget scale,
exists: the hypotheses of the rate theorems are met by every law. -/
theorem exists_quantile_split (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (B : ℝ) :
    ∃ σ τ ζ : Measure Gap, IsFiniteMeasure σ ∧ IsFiniteMeasure τ ∧ IsFiniteMeasure ζ ∧
      σ+τ+ζ = μ ∧ σ = quantileCore μ ρ ∧ τ+ζ = quantileTail μ ρ ∧
      (∀ᵐ d : Gap ∂τ, budgetScale B ≤ (d:ℝ)) ∧ (∀ᵐ d : Gap ∂ζ, (d:ℝ) ≤ budgetScale B) := by
  have hνf : IsFiniteMeasure (quantileTail μ ρ) :=
    isFiniteMeasure_of_le μ (quantileTail_le μ hρ hρ1)
  have hσf : IsFiniteMeasure (quantileCore μ ρ) := isFiniteMeasure_of_le μ Measure.sub_le
  obtain ⟨τ, ζ, hτf, hζf, hsum, hτs, hζs⟩ := exists_cut (quantileTail μ ρ) (budgetScale B)
  refine ⟨quantileCore μ ρ, τ, ζ, hσf, hτf, hζf, ?_, rfl, hsum, hτs, hζs⟩
  rw [add_assoc, hsum, add_comm, quantileTail_add_core μ hρ hρ1]

/-- The planner's output is admissible, in minimax form. For an enclosure
whose envelope meets the termination requirement, a terminal level that
covers its unresolved mass and positive weights, the minimax risk at budget
`B` is at most the smaller of `ρ/2` and the certified risk of the plan. -/
theorem searched_plan_minimax (σ τ ζ : Measure Gap)
    [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)]
    {t ρ B : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : bandEdge N < t)
    (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4) (hB : 0 < B)
    (E : SplitEnclosure σ τ ζ N) (hvan : EnvelopeVanishes E.resolvedError) {J : ℕ}
    (hzJ : E.unresolved ≤ levelAccuracy ρ J/8) (w : Fin (J+1) → ℝ) (hw : ∀ i, 0 < w i) :
    rareMinimaxRisk (σ+τ+ζ) ρ B ≤
      ENNReal.ofReal (min (ρ/2) (sqrt (planCertificate ρ
        (planRates B (planCost E ρ (searchCaps E.resolvedError hvan hρ) J) w)))) := by
  obtain ⟨hb, hrisk⟩ := searched_plan_valid σ τ ζ ht hs hN hτ hρ hρ1 hB E hvan hzJ w hw
  have h1 : rareMinimaxRisk (σ+τ+ζ) ρ B ≤ ENNReal.ofReal (sqrt (planCertificate ρ
      (planRates B (planCost E ρ (searchCaps E.resolvedError hvan hρ) J) w))) :=
    (show rareMinimaxRisk (σ+τ+ζ) ρ B ≤
        rareRisk (σ+τ+ζ) (planEstimator σ τ ζ ht hs hN hρ hρ1
          (searchCaps E.resolvedError hvan hρ)
          (planRates B (planCost E ρ (searchCaps E.resolvedError hvan hρ) J) w)) ρ from
      sInf_le ⟨Fin (J+1) → ℕ, inferInstance, planEstimator σ τ ζ ht hs hN hρ hρ1
        (searchCaps E.resolvedError hvan hρ)
        (planRates B (planCost E ρ (searchCaps E.resolvedError hvan hρ) J) w), hb,
        rfl⟩).trans hrisk
  have h2 := minimax_half_rarity (σ+τ+ζ) (B := B) hρ.le
  rcases le_total (ρ/2) (sqrt (planCertificate ρ
      (planRates B (planCost E ρ (searchCaps E.resolvedError hvan hρ) J) w))) with h | h
  · rwa [min_eq_left h]
  · rwa [min_eq_right h]

/-- The planner attains the oracle rate from upper bounds. For the quantile
split of a law of positive gaps, every tight enclosure and all weights within
a factor `θ` of the optimal ones, the planner's output, the plan when
`2048 z̄ ≤ ρ` and the constant otherwise, gives minimax risk at most
`(1 + (8/5) max{4096, 8 · 28000 √θ}) K_{μ,ρ}(B)`. -/
theorem tight_planner_minimax_rate (σ τ ζ : Measure Gap)
    [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)]
    {ρ B θ : ℝ} {N : ℕ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) (hθ : 0 ≤ θ)
    (hcore : σ = quantileCore (σ+τ+ζ) ρ) (htail : τ+ζ = quantileTail (σ+τ+ζ) ρ)
    (hτs : ∀ᵐ d : Gap ∂τ, budgetScale B ≤ (d:ℝ)) (hζs : ∀ᵐ d : Gap ∂ζ, (d:ℝ) ≤ budgetScale B)
    (hN : bandEdge N < quantileThreshold (σ+τ+ζ) ρ)
    (E : SplitEnclosure σ τ ζ N) (hE : E.Tight (ζ.real univ))
    (w : Fin (planTerminal hρ B E.unresolved + 1) → ℝ)
    (hlow : ∀ i, sqrt (17*levelAccuracy ρ i.val /
      planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ)
        (planTerminal hρ B E.unresolved) i) ≤ w i)
    (hup : ∀ i, w i ≤ θ * sqrt (17*levelAccuracy ρ i.val /
      planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ)
        (planTerminal hρ B E.unresolved) i)) :
    rareMinimaxRisk (σ+τ+ζ) ρ B ≤
      ENNReal.ofReal (1 + 8/5 * max 4096 (224000 * sqrt θ)) *
        EntropyTail.selection (σ+τ+ζ) ρ B := by
  have hρ1 : ρ ≤ 1 := by linarith
  have hh := budgetScale_pos hB
  have ht := (quantileThreshold_properties (σ+τ+ζ) hρ hρ1).1
  have hs : ∀ᵐ d : Gap ∂σ, quantileThreshold (σ+τ+ζ) ρ ≤ (d:ℝ) := by
    have h := quantileCore_support (σ+τ+ζ) ρ
    rw [← hcore] at h
    exact h
  have hτ := inverse_integrable_of_support τ hh hτs
  rcases lt_or_ge ρ (2048 * E.unresolved) with hz | hz
  · exact (minimax_half_rarity (σ+τ+ζ) (B := B) hρ.le).trans
      (tight_quantile_fallback_rate σ τ ζ θ hρ hρ4 hB hcore htail hτs hζs E hE hz)
  · have hzJ : E.unresolved ≤ levelAccuracy ρ (planTerminal hρ B E.unresolved)/8 := by
      have h := planTerminal_unresolved hρ B hz
      linarith [levelAccuracy_pos hρ (planTerminal hρ B E.unresolved)]
    have hzρ : ζ.real univ ≤ ρ := by
      have h0 : 0 ≤ ζ.real univ := measureReal_nonneg
      linarith [E.unresolved_le]
    have hk := planCost_pos σ τ ζ ht hs hN hτ hρ hρ4 hzρ E
      (searchCaps E.resolvedError hE.vanishes hρ) (planTerminal hρ B E.unresolved)
    have hw : ∀ i, 0 < w i := fun i =>
      lt_of_lt_of_le (sqrt_pos.mpr (div_pos
        (mul_pos (by norm_num) (levelAccuracy_pos hρ i.val)) (hk i))) (hlow i)
    exact (searched_plan_minimax σ τ ζ ht hs hN hτ hρ hρ4 hB E hE.vanishes hzJ w hw).trans
      (tight_quantile_plan_rate σ τ ζ hρ hρ4 hB hθ hcore htail hτs hζs hN E hE hz w hlow hup)

/-- The exact planner on a quantile split: with the exact integrals and the
optimal weights its output gives minimax risk at most `44801 K`. -/
theorem split_planner_minimax_rate (σ τ ζ : Measure Gap)
    [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)]
    {ρ B : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B)
    (hcore : σ = quantileCore (σ+τ+ζ) ρ) (htail : τ+ζ = quantileTail (σ+τ+ζ) ρ)
    (hτs : ∀ᵐ d : Gap ∂τ, budgetScale B ≤ (d:ℝ)) (hζs : ∀ᵐ d : Gap ∂ζ, (d:ℝ) ≤ budgetScale B) :
    rareMinimaxRisk (σ+τ+ζ) ρ B ≤
      ENNReal.ofReal 44801 * EntropyTail.selection (σ+τ+ζ) ρ B := by
  have hρ1 : ρ ≤ 1 := by linarith
  have hh := budgetScale_pos hB
  have ht := (quantileThreshold_properties (σ+τ+ζ) hρ hρ1).1
  have hs : ∀ᵐ d : Gap ∂σ, quantileThreshold (σ+τ+ζ) ρ ≤ (d:ℝ) := by
    have h := quantileCore_support (σ+τ+ζ) ρ
    rw [← hcore] at h
    exact h
  have hτ := inverse_integrable_of_support τ hh hτs
  obtain ⟨N, hN⟩ : ∃ N : ℕ, bandEdge N < quantileThreshold (σ+τ+ζ) ρ := by
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one ht (by norm_num : (2:ℝ)⁻¹ < 1)
    exact ⟨N, (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ N)).trans_lt hN⟩
  have hC : (1:ℝ) + 8/5 * max 2048 (28000 * sqrt 1) = 44801 := by
    rw [sqrt_one, mul_one, max_eq_right (by norm_num)]
    norm_num
  rcases lt_or_ge ρ (2048 * ζ.real univ) with hz | hz
  · have hf := quantile_fallback_rate σ τ ζ 1 hρ hρ4 hB hcore htail hτs hζs hz
    rw [hC] at hf
    exact (minimax_half_rarity (σ+τ+ζ) (B := B) hρ.le).trans hf
  · have hzJ : ζ.real univ ≤ levelAccuracy ρ (planTerminal hρ B (ζ.real univ))/8 := by
      have h := planTerminal_unresolved hρ B hz
      linarith [levelAccuracy_pos hρ (planTerminal hρ B (ζ.real univ))]
    have hzρ : ζ.real univ ≤ ρ := by
      have h0 : 0 ≤ ζ.real univ := measureReal_nonneg
      linarith
    have hk := planCost_pos σ τ ζ ht hs hN hτ hρ hρ4 hzρ (SplitEnclosure.exact σ τ ζ N)
      (searchCaps (eta (σ+τ)) (eta_vanishes (σ+τ)) hρ) (planTerminal hρ B (ζ.real univ))
    have hw : ∀ i : Fin (planTerminal hρ B (ζ.real univ) + 1),
        0 < sqrt (17*levelAccuracy ρ i.val /
          planCost (SplitEnclosure.exact σ τ ζ N) ρ
            (searchCaps (eta (σ+τ)) (eta_vanishes (σ+τ)) hρ)
            (planTerminal hρ B (ζ.real univ)) i) := fun i =>
      sqrt_pos.mpr (div_pos (mul_pos (by norm_num) (levelAccuracy_pos hρ i.val)) (hk i))
    have hmm := searched_plan_minimax σ τ ζ ht hs hN hτ hρ hρ4 hB
      (SplitEnclosure.exact σ τ ζ N) (eta_vanishes (σ+τ)) hzJ _ hw
    have hrate := quantile_plan_rate σ τ ζ hρ hρ4 hB (by norm_num : (0:ℝ) ≤ 1) hcore htail
      hτs hζs hN hz _ (fun i => le_rfl) (fun i => by rw [one_mul])
    rw [hC] at hrate
    exact hmm.trans hrate

/-- The exact planner attains the oracle rate, for every law. For every
probability law `μ` of positive gaps, every `0 < ρ ≤ 1/4` and every `B > 0`,
the output of the planner run on the quantile split of `μ` with the exact
integrals and the optimal weights gives minimax risk at most
`44801 K_{μ,ρ}(B)`. -/
theorem planner_minimax_rate (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B : ℝ} (hρ : 0 < ρ)
    (hρ4 : ρ ≤ 1/4) (hB : 0 < B) :
    rareMinimaxRisk μ ρ B ≤ ENNReal.ofReal 44801 * EntropyTail.selection μ ρ B := by
  obtain ⟨σ, τ, ζ, hσf, hτf, hζf, hsum, hcore, htail, hτs, hζs⟩ :=
    exists_quantile_split μ hρ (by linarith) B
  subst hsum
  exact split_planner_minimax_rate σ τ ζ hρ hρ4 hB hcore htail hτs hζs

/-- The exact design integrals of a split whose reference law has mass `z₀`
at zero: the mass at zero is added to the unresolved mass. -/
def SplitEnclosure.exactZero (σ τ ζ : Measure Gap) (N : ℕ) {z₀ : ℝ} (hz₀ : 0 ≤ z₀) :
    SplitEnclosure σ τ ζ N where
  entropy := costEntropy (fun j : Fin N => bandCost σ j.val)
  tailInverse := ∫ d : Gap, (d:ℝ)⁻¹ ∂τ
  unresolved := z₀ + ζ.real univ
  resolvedError := eta (σ+τ)
  tailWork := ordinaryCost τ
  entropy_le := le_rfl
  tailInverse_le := le_rfl
  unresolved_le := le_add_of_nonneg_left hz₀
  resolvedError_le := fun _ => le_rfl
  tailWork_le := fun _ => le_rfl

/-- The exact design integrals with mass at zero are a tight enclosure. -/
theorem SplitEnclosure.exactZero_tight (σ τ ζ : Measure Gap) (N : ℕ) {z₀ : ℝ} (hz₀ : 0 ≤ z₀) :
    (SplitEnclosure.exactZero σ τ ζ N hz₀).Tight (z₀ + ζ.real univ) := by
  have hΓ := costEntropy_nonneg (fun j : Fin N => bandCost_nonneg σ j.val)
  have hH : 0 ≤ ∫ d : Gap, (d:ℝ)⁻¹ ∂τ := integral_nonneg fun d => inv_nonneg.mpr d.property.1.le
  have hz : 0 ≤ ζ.real univ := measureReal_nonneg
  refine ⟨?_, ?_, le_rfl, ?_, fun k => ?_, fun k => ?_⟩
  · change costEntropy (fun j : Fin N => bandCost σ j.val) ≤ _
    linarith
  · change (∫ d : Gap, (d:ℝ)⁻¹ ∂τ) ≤ _
    linarith
  · change z₀ + ζ.real univ ≤ _
    linarith
  · change eta (σ+τ) (4 ^ k) ≤ _
    linarith [eta_nonneg (σ+τ) (4 ^ k)]
  · change ordinaryCost τ (4 ^ k) ≤ _
    linarith [ordinaryCost_nonneg τ (by positivity : (0:ℝ) ≤ 4 ^ k)]

/-- The design of a reference law with mass at zero exists: the quantile
split of the positive part at the conditional rarity, scaled by `1 - z₀` and
cut at the budget scale. -/
theorem exists_zero_atom_split (η : Measure Gap) [IsProbabilityMeasure η] {z₀ ρ : ℝ}
    (hzρ : z₀ < ρ) (hρ1 : ρ ≤ 1) (B : ℝ) :
    ∃ σ τ ζ : Measure Gap, IsFiniteMeasure σ ∧ IsFiniteMeasure τ ∧ IsFiniteMeasure ζ ∧
      σ = ENNReal.ofReal (1 - z₀) • quantileCore η (conditionalRarity ρ z₀) ∧
      τ+ζ = ENNReal.ofReal (1 - z₀) • quantileTail η (conditionalRarity ρ z₀) ∧
      (∀ᵐ d : Gap ∂τ, budgetScale B ≤ (d:ℝ)) ∧ (∀ᵐ d : Gap ∂ζ, (d:ℝ) ≤ budgetScale B) := by
  have hc : 0 < 1 - z₀ := by linarith
  have hr : 0 < conditionalRarity ρ z₀ := div_pos (by linarith) hc
  have hr1 : conditionalRarity ρ z₀ ≤ 1 := (div_le_one hc).mpr (by linarith)
  have hνf : IsFiniteMeasure (quantileTail η (conditionalRarity ρ z₀)) :=
    isFiniteMeasure_of_le η (quantileTail_le η hr hr1)
  have hσf : IsFiniteMeasure (quantileCore η (conditionalRarity ρ z₀)) :=
    isFiniteMeasure_of_le η Measure.sub_le
  have hν' : IsFiniteMeasure (ENNReal.ofReal (1 - z₀) • quantileTail η (conditionalRarity ρ z₀)) :=
    (quantileTail η (conditionalRarity ρ z₀)).smul_finite ENNReal.ofReal_ne_top
  have hσ' : IsFiniteMeasure (ENNReal.ofReal (1 - z₀) • quantileCore η (conditionalRarity ρ z₀)) :=
    (quantileCore η (conditionalRarity ρ z₀)).smul_finite ENNReal.ofReal_ne_top
  obtain ⟨τ, ζ, hτf, hζf, hsum, hτs, hζs⟩ := exists_cut
    (ENNReal.ofReal (1 - z₀) • quantileTail η (conditionalRarity ρ z₀)) (budgetScale B)
  exact ⟨_, τ, ζ, hσ', hτf, hζf, rfl, hsum, hτs, hζs⟩

end ThresholdHC.KnownLawPlanner
