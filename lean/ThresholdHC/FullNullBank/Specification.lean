import ThresholdHC.RobustContinuation.RaceOrder
import ThresholdHC.EntropyTailAssembly.LevelCertificates

/-! Target statements for the bank that evaluates the exact null mixture of a
reference law with a zero atom, the fair-coin likelihood included.

Source: `docs/ARBITRARY_LAW_ADAPTATION.md`, section `4. Robust use of the
known-law estimator`, the paragraph that begins `Assign a reference zero atom
entirely to the unresolved part`: the null prefix probability of the bank of
`alpha = z0 delta_0 + (1 - z0) eta` includes the zero atom's fair-coin
likelihood exactly, and the error and work bounds of the level certificates
hold for it. The same paragraph, and `docs/ARBITRARY_LAW_FORMALIZATION.md`,
sections `Rate of a plan computed from upper bounds` (the paragraph `These are
statements about the numbers the planner computes`) and `Robust continuation:
level certificates under a coupled law` (the paragraph `A reference law
z_0 delta_0 + (1 - z_0) eta is the case c = 1 - z_0`), record that this bank,
which evaluates the null mixture of the whole reference law, was not the one
checked. The bank is the one the toolkit runs:
`toolkit/threshold_toolkit/gap_envelope.py` (`GapEnvelope.null_prefix`:
`zero_mass * (1/2)^(h+t) + sum w (1/2-d)^h (1/2+d)^t`) and
`toolkit/threshold_toolkit/known_rare_estimator.py` (`_classify`: positive
exit when the null prefix probability is at most `u` times the positive-bank
probability, with `u = level.error/4 = rho * levelEpsilon l`, and negative
allowance `u/rho = levelEpsilon l`).

Formalization choices.
* `fullNullLaw z0 eta` is the exact null mixture of the reference law on the
  bank's tapes: a fair coin (`tapeMeasure` at `1/2`) with weight `z0` and the
  all-negative population of `eta` (`EntropyTailUpper.allNegativeLaw`) with
  weight `1 - z0`. `fullNullBankTest z0 eta weights u` fires on a prefix when
  its probability under `fullNullLaw` is at most `u` times its probability
  under the positive references (`EntropyTailUpper.positiveBankLaw`). The
  negative test is the existing `EntropyTailUpper.negativeBankTest`.
* `FullNullBankStatement` is the bank and the coin: the test is upward in the
  flips; Ville's bound under the full null; the integrated false positives of
  the positive part, `(1 - z0) * int P_d(false positive) d eta <= u`; and, for a
  design `sigma + tau + zeta = (1 - z0) eta`, the work of the race on a positive
  or a negative coin of gap `d >= d0` with `d0` in band `j`. The fair-coin term
  does not decay with the prefix length; it is charged in the positive
  allowance through the envelope `z0 + threePieceEnvelope sigma tau zeta d0`.
* `FullNullLevelStatement` is the level certificate under a true law coupled
  above the reference: the coupling `pi` has first marginal `(1 - z0) eta` and
  `z.1 <= z.2` almost everywhere, and the true law is its second marginal plus
  a part `mu0` coupled to no positive reference gap (the mass that the true law
  puts against the zero atom). The bank's positive allowance is
  `rho * levelEpsilon l` under the full null. The error bound is that of the
  robust bank with null law `eta` (`RobustContinuation.robust_level_error`),
  and the work bound is its level price with the premise `z0 + zeta(all) <= rho`
  in place of `zeta(all) <= rho`.
* Gaps are positive (`Tier6.Gap = (0, 1/2]`), so no physical coin of gap zero
  is modelled: the fair coin enters only as the likelihood the bank uses for
  the atom. The coupling is a hypothesis. The bank's null probability is the
  exact measure, which matches the exact interval of `GapEnvelope`; the
  toolkit's general interval-oracle contract is not modelled.
Not stated: the plan, the planner rate and the estimator that runs the plan
with this bank, and the rational arithmetic that produces a tight enclosure
for a finite law. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal

namespace ThresholdHC.FullNullBank
open ThresholdHC ThresholdHC.Tier2 ThresholdHC.Tier6 ThresholdHC.ObservableSimulation
open ThresholdHC.EntropyTailUpper ThresholdHC.EntropyTailAssembly
open ThresholdHC.RobustContinuation ThresholdHC.RareAboveTwo

/-- The fair coin, success probability `1/2`. -/
def fairParameter : unitInterval := ⟨1/2, by constructor <;> norm_num⟩

/-- The exact null mixture of `alpha = z0 delta_0 + (1 - z0) eta` on the bank's
tapes: a fair coin with weight `z0` and the all-negative population of `eta`
with weight `1 - z0`. -/
def fullNullLaw (z₀ : ℝ) (η : Measure Gap) : Measure (ℕ → Bool) :=
  ENNReal.ofReal z₀ • tapeMeasure fairParameter + ENNReal.ofReal (1 - z₀) • allNegativeLaw η

/-- The toolkit's positive bank: the full null probability of the prefix is at
most `u` times its probability under the positive references. -/
def fullNullBankTest (z₀ : ℝ) (η : Measure Gap) (weights : ℕ → ℝ≥0) (u : ℝ) : PrefixTest :=
  fun n w => fullNullLaw z₀ η (tapePrefix n ⁻¹' {w}) ≤
    ENNReal.ofReal u * positiveBankLaw weights (tapePrefix n ⁻¹' {w})

/-- The bank with the full null mixture and its work on one coin. -/
def FullNullBankStatement : Prop :=
  ∀ (z₀ : ℝ) (η : Measure Gap) [IsProbabilityMeasure η] (weights : ℕ → ℝ≥0),
    HasSum weights 1 → 0 ≤ z₀ → z₀ < 1 →
    (∀ u, UpwardTest (fullNullBankTest z₀ η weights u)) ∧
    (∀ u, fullNullLaw z₀ η (everPrefixHit (fullNullBankTest z₀ η weights u)) ≤
      ENNReal.ofReal u) ∧
    (∀ u, 0 ≤ u → (1 - z₀) * (∫ d, tapeEventProbability false
      (everPrefixHit (fullNullBankTest z₀ η weights u)) d ∂η) ≤ u) ∧
    ∀ (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ],
      σ+τ+ζ = ENNReal.ofReal (1 - z₀) • η →
      Integrable (fun x : Gap => (x:ℝ)⁻¹^2) σ → Integrable (fun x : Gap => (x:ℝ)⁻¹) τ →
      ∀ {ε ρ : ℝ}, 0 < ε → ε ≤ 1 → 0 < ρ →
      ∀ (j L : ℕ), 0 < (weights j:ℝ) → (weights j:ℝ) ≤ 1 →
      ∀ {d₀ d : Gap}, d₀ ∈ EntropyTailQuantile.band j → (d₀:ℝ) ≤ d →
        conditionalRaceWork (negativeBankTest weights ε) (fullNullBankTest z₀ η weights (ρ*ε))
            L true d ≤
          12*positiveAllowance ε (weights j:ℝ) ρ (z₀ + threePieceEnvelope σ τ ζ d₀)/(d₀:ℝ)^2 ∧
        conditionalRaceWork (negativeBankTest weights ε) (fullNullBankTest z₀ η weights (ρ*ε))
            L false d ≤
          (3/(2*(d₀:ℝ)^2))*(1+Real.log (ε*(weights j:ℝ))⁻¹)

/-- The level error and the level work of the race with the full-null bank,
under a true law coupled above the reference. -/
def FullNullLevelStatement : Prop :=
  ∀ (z₀ : ℝ) (η : Measure Gap) [IsProbabilityMeasure η], 0 ≤ z₀ → z₀ < 1 →
  ∀ (π : Measure (Gap × Gap)) [IsFiniteMeasure π], (∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2) →
    π.map Prod.fst = ENNReal.ofReal (1 - z₀) • η →
  ∀ (μ₀ : Measure Gap) [IsFiniteMeasure μ₀] {ρ : ℝ}, 0 < ρ →
  ∀ q : SignLaw, RarePrior (π.map Prod.snd + μ₀) ρ q →
    (∀ (ν ζ : Measure Gap) [IsFiniteMeasure ν] [IsFiniteMeasure ζ],
      ν+ζ = ENNReal.ofReal (1 - z₀) • η →
      ∀ weights : ℕ → ℝ≥0, HasSum weights 1 → ∀ l k : ℕ,
      eta ν (4^k) ≤ levelAccuracy ρ l/8 →
      ζ.real univ + μ₀.real univ ≤ levelAccuracy ρ l/8 →
      racePopulationError (π.map Prod.snd + μ₀) q (negativeBankTest weights (levelEpsilon l))
        (fullNullBankTest z₀ η weights (ρ*levelEpsilon l)) (2*k) ≤ levelAccuracy ρ l) ∧
    (∀ (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ],
      σ+τ+ζ = ENNReal.ofReal (1 - z₀) • η →
      ∀ {t : ℝ} {N : ℕ}, 0 < t → (∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) →
      EntropyTailQuantile.bandEdge N < t → Integrable (fun d : Gap => (d:ℝ)⁻¹) τ →
      z₀ + ζ.real univ ≤ ρ → ∀ l L : ℕ,
      (∫ d, mixtureRaceWork q (negativeBankTest (referenceWeights σ) (levelEpsilon l))
          (fullNullBankTest z₀ η (referenceWeights σ) (ρ*levelEpsilon l)) L d
          ∂(π.map Prod.snd + μ₀)) ≤
        128*(l+1)*EntropyTailQuantile.costEntropy
            (fun j : Fin N => EntropyTailQuantile.bandCost σ j.val) +
        6*(∫ d : Gap, (d:ℝ)⁻¹ ∂τ)^2/ρ + 2*ordinaryCost τ (Uniform713.cap L) +
        2*Uniform713.cap L*(ζ.real univ + μ₀.real univ))

end ThresholdHC.FullNullBank
