
import ThresholdHC.AnytimeLower.InfiniteMoment
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory InformationTheory Real Set Filter
open scoped ENNReal Topology
open ThresholdHC.AnytimeLower ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.RareAboveTwo

example : ∀ (τ : ℝ) {h : ℝ} (hh : 0 ≤ h) (d : Gap),
    0 ≤ tailProfile τ h d ∧ tailProfile τ h d ≤ 1 := @tailProfile_bounds

example : ∀ (τ : ℝ) {h : ℝ} (hh : 0 ≤ h) (d : Gap),
    (d:ℝ)*tailProfile τ h d ≤ h := @tailProfile_weighted

example : ∀ (μ : Measure Gap) [IsFiniteMeasure μ] {τ h : ℝ}
    (hh : 0 < h) (hμ : 0 < μ {d : Gap | (d:ℝ) ≤ τ}),
    0 < profileMass μ τ h := @profileMass_pos

example : ∀ (μ : Measure Gap) [IsFiniteMeasure μ] (τ : ℝ)
    (h : ℕ → ℝ) (hh : ∀ k, 0 ≤ h k) (hlim : Tendsto h atTop (𝓝 0)),
    Tendsto (fun k => profileMass μ τ (h k)) atTop (𝓝 0) := @profileMass_tendsto_zero

example : ∀ (W : ℕ → ℝ) (hp : ∀ j, 0 < W j) (hl : Tendsto W atTop (𝓝 0))
    {i j : ℕ} (hij : i ≤ j) (hj : j < nextDrop W hp hl i),
    W i/4 < W j := @before_nextDrop

example : ∀ (W : ℕ → ℝ) (hp : ∀ j, 0 < W j) (hl : Tendsto W atTop (𝓝 0))
    (hq : ∀ j, W j/4 ≤ W (j+1)) (i : ℕ),
    W i/16 < W (nextDrop W hp hl i) := @nextDrop_overshoot

example : ∀ {m : ℕ} (n : ℕ) (pol : List Bool → Option (Fin m))
    (d q r : Fin m → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1/2)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 1)
    (hc : ∀ i, TailContrast (d i) (q i) (r i))
    (hcontrast : ∀ i, d i*|q i-r i| ≤ ε/32),
    ThresholdHC.klFT (ThresholdHC.transcriptLaw (n:=n) pol d q)
      (ThresholdHC.transcriptLaw pol d r) ≤ n*ε^2 := @tail_transcript_kl

example : ∀ {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (q r : SignLaw) {ε : ℝ} (hε : 0 ≤ ε)
    (hc : ∀ d : Gap, TailContrast d (q.val d) (r.val d))
    (hcontrast : ∀ d : Gap, (d:ℝ)*|q.val d-r.val d| ≤ ε/32) (n : ℕ),
    klDiv (observablePrefixLaw μ A q n) (observablePrefixLaw μ A r n) ≤
      ENNReal.ofReal (n*ε^2) := @tail_observable_prefix_kl

example : ∀ (μ : Measure Gap) [IsFiniteMeasure μ] {τ : ℝ} (hτ : 0 < τ)
    (hμ : 0 < μ {d : Gap | (d:ℝ) ≤ τ}) (i k : ℕ) (hik : i < k),
    3*selectedSeparation μ hτ hμ k ≤ selectedSeparation μ hτ hμ i :=
      @selectedSeparation_separated

example : ∀ {δ : ℝ} (hd : δ < 1) (s : ℕ → ℝ) (hs : ∀ k, 0 < s k),
    ¬Summable (fun k => exp (-((testingBudget δ s k:ℝ)*(s k)^2)/(1-δ))) :=
      @testingBudget_not_summable

example : ∀ {δ : ℝ} (hd : δ < 1) (s : ℕ → ℝ) (hs : ∀ k, 0 < s k) (hm : Antitone s),
    Tendsto (testingBudget δ s) atTop atTop := @testingBudget_tendsto

example : ∀ (μ : Measure Gap) [IsFiniteMeasure μ]
    (hI : ¬Integrable (fun d : Gap => (d:ℝ)⁻¹) μ) {ρ : ℝ} (hρ : 0 < ρ),
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1/4 ∧ 0 < μ {d : Gap | (d:ℝ) ≤ τ} ∧
      μ.real {d : Gap | (d:ℝ) ≤ τ} ≤ ρ := @exists_smallGapRegion

example : ∀ {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (H : ∀ n, R × Prefix n → ℝ) (hH : ∀ n, Measurable (H n))
    {τ ρ δ : ℝ} (hτ : 0 < τ) (hτq : τ ≤ 1/4)
    (hμ : 0 < μ {d : Gap | (d:ℝ) ≤ τ})
    (hrare : μ.real {d : Gap | (d:ℝ) ≤ τ} ≤ ρ)
    (hd : 0 ≤ δ ∧ δ ≤ 1/2) (t : ℕ → ℝ) (hacc : OnlineAccuracy μ A H ρ δ t),
    ∃ᶠ k in atTop, profileMass μ τ (selectedScale μ hτ hμ k)/256 ≤
      t (testingBudget δ (selectedScale μ hτ hμ) k) := @tail_scheduled_frequently

example : ∀ {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (H : ∀ n, R × Prefix n → ℝ) (hH : ∀ n, Measurable (H n))
    {τ ρ δ : ℝ} (hτ : 0 < τ) (hτq : τ ≤ 1/4)
    (hμ : 0 < μ {d : Gap | (d:ℝ) ≤ τ})
    (hrare : μ.real {d : Gap | (d:ℝ) ≤ τ} ≤ ρ)
    (hd : 0 ≤ δ ∧ δ ≤ 1/2) (t : ℕ → ℝ) (hacc : OnlineAccuracy μ A H ρ δ t) (M : ℕ),
    ∃ k, M ≤ testingBudget δ (selectedScale μ hτ hμ) k ∧
      profileMass μ τ (selectedScale μ hτ hμ k)/256 ≤
        t (testingBudget δ (selectedScale μ hτ hμ) k) := @tail_scheduled_unbounded

example : ∀ {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (hI : ¬Integrable (fun d : Gap => (d:ℝ)⁻¹) μ)
    (A : AdaptiveEstimator R) (H : ∀ n, R × Prefix n → ℝ)
    (hH : ∀ n, Measurable (H n)) {ρ δ : ℝ} (hρ : 0 < ρ)
    (hd : 0 ≤ δ ∧ δ ≤ 1/2) (t : ℕ → ℝ) (hacc : OnlineAccuracy μ A H ρ δ t),
    ∃ (τ : ℝ) (hτ : 0 < τ) (hμ : 0 < μ {d : Gap | (d:ℝ) ≤ τ}),
      τ ≤ 1/4 ∧ μ.real {d : Gap | (d:ℝ) ≤ τ} ≤ ρ/2 ∧
      ∀ M : ℕ, ∃ k, M ≤ testingBudget δ (selectedScale μ hτ hμ) k ∧
        profileMass μ τ (selectedScale μ hτ hμ k)/256 ≤
          t (testingBudget δ (selectedScale μ hτ hμ) k) := @infiniteMoment_unbounded
#print axioms ThresholdHC.AnytimeLower.before_nextDrop
#print axioms ThresholdHC.AnytimeLower.exists_smallGapRegion
#print axioms ThresholdHC.AnytimeLower.infiniteMoment_unbounded
#print axioms ThresholdHC.AnytimeLower.nextDrop_overshoot
#print axioms ThresholdHC.AnytimeLower.profileMass_pos
#print axioms ThresholdHC.AnytimeLower.profileMass_tendsto_zero
#print axioms ThresholdHC.AnytimeLower.selectedSeparation_separated
#print axioms ThresholdHC.AnytimeLower.tailProfile_bounds
#print axioms ThresholdHC.AnytimeLower.tailProfile_weighted
#print axioms ThresholdHC.AnytimeLower.tail_observable_prefix_kl
#print axioms ThresholdHC.AnytimeLower.tail_scheduled_frequently
#print axioms ThresholdHC.AnytimeLower.tail_scheduled_unbounded
#print axioms ThresholdHC.AnytimeLower.tail_transcript_kl
#print axioms ThresholdHC.AnytimeLower.testingBudget_not_summable
#print axioms ThresholdHC.AnytimeLower.testingBudget_tendsto
