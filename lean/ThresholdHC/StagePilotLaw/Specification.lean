import ThresholdHC.ArbitraryLawAdaptation.TailPilotLaw
import ThresholdHC.ArbitraryLawAdaptation.PilotOnset
import ThresholdHC.ArbitraryLawAdaptation.ZeroModel

/-! Target statements: the pilot events (A8) and (A11) of the paid learning
stage, under the law of the original hidden-gap experiment of the whole stage.

Source: `docs/ARBITRARY_LAW_ADAPTATION.md`, section 2 (Learning the envelope
under one physical cap), display (A8), and section 3 (The learned law retains
the oracle rate), display (A11) with its sentence: there is a finite
`J_0(mu, rho)` such that on the same event (A8), for every `J >= J_0`,
`K_(mu_bar, rho)(N) <= 2^24 K_(mu, rho)(N)`. The same displays are (UA8) and
(UA11) of `paper/v6/arbitrary-law-adaptation.tex`, subsection
`sec:arbitrary-law-adaptation`, subsubsections Learning the envelope under one
physical cap and The learned law retains the oracle rate. The audited library
states both events on the coin array of the original simulation law
(`original_pilotStage_event` and `original_pilotStage_oracle`); the caveat is
recorded in `docs/ARBITRARY_LAW_FORMALIZATION.md` (sections Capped
multi-depth pilot and Learned law against the oracle: the comparison) and at
the end of section 3 of `docs/ARBITRARY_LAW_ADAPTATION.md`.

Here the events are stated under
`experimentLaw μ ((pilotStage S J m ρ).endpoint false) q`, the original
hidden-gap experiment of the whole learning stage run as an estimator. The
stage `S` is arbitrary (private randomness, continuation and interval rule);
only its pilot is the capped multi-depth pilot of (A6). The certificates are
read off the paid chronological prefix
`(processHistory z.2 cap).take pilotCost` of the stage's observed history,
which is the prefix the stage's own interval rule reads.

* `StagePilotEventStatement`: (A8), both halves at every depth `j = i + 1 ≤ J`,
  together with the domination of the gap law by the learned law (A9).
* `StagePilotOracleStatement`: on the same event (A8), with domination, the
  learned law also satisfies (A11), under the pilot's onset condition at the
  fixed depth `J`.
* `StagePilotOracleEventuallyStatement`: the same with the finite onset
  `J₀`, which depends on the gap law and the rarity only and is chosen before
  the seed type, the sign law, the stage, `m` and `ε`.

Deviations from the source. Index `i < J` stands for depth `j = i + 1`. The
paper's odd `m` is not needed: every `m > 0` with `m ≥ 8 log(2J/ε)` is
allowed. (A11) is stated with `zeroSelection`, the selection functional
extended to laws with mass at zero, at the budget `N = 4^J`, with
`16777216 = 2^24`. The pilot is charged its full cap; the paper's remark that
easy-law pilots stop early is not formalized. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.StagePilotLaw
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.ArbitraryLawAdaptation

/-- (A8) for the pilot installed in the learning stage, under the law of the
original hidden-gap experiment of the whole stage. With `m ≥ 8 log(2J/ε)`
probes at every depth, with probability at least `1 - ε` the certificates read
off the paid chronological prefix of the observed history satisfy
`F(2^{-j}) ≤ U_j ≤ 128 (u_j + W_j/b_j + 1/M)` at every depth `j = i + 1 ≤ J`,
and the learned law dominates the gap law in distribution. -/
def StagePilotEventStatement : Prop :=
  ∀ (R : Type) [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (S : LearnedStage R) (J m : ℕ) (ρ ε : ℝ),
    0 < ρ → 1 ≤ J → 0 < m → 0 < ε → 8 * Real.log (2 * (J : ℝ) / ε) ≤ m →
    1 - ε ≤ (experimentLaw μ ((pilotStage S J m ρ).endpoint false) q).real
      {z | (∀ i, i < J →
          μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ (i + 1)} ≤
            (pilotStage S J m ρ).upper ((processHistory z.2 (pilotStage S J m ρ).cap).take
              (pilotStage S J m ρ).pilotCost) i ∧
          (pilotStage S J m ρ).upper ((processHistory z.2 (pilotStage S J m ρ).cap).take
              (pilotStage S J m ρ).pilotCost) i ≤ pilotBound μ J ρ (i + 1)) ∧
        ∀ x : ℝ, (μ.map Subtype.val) (Set.Iic x) ≤
          (pilotStage S J m ρ).learnedLaw ((processHistory z.2 (pilotStage S J m ρ).cap).take
            (pilotStage S J m ρ).pilotCost) (Set.Iic x)}

/-- (A11) on the same event (A8), under the law of the original hidden-gap
experiment of the whole stage. Under the pilot's onset condition at depth `J`
and with `m ≥ 8 log(2J/ε)` probes at every depth, with probability at least
`1 - ε` the certificates read off the paid chronological prefix satisfy both
halves of (A8), the learned law dominates the gap law in distribution, and its
zero-extended selection functional at budget `4^J` is at most `2^24` times the
oracle's. -/
def StagePilotOracleStatement : Prop :=
  ∀ (R : Type) [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (S : LearnedStage R) (J m : ℕ) (ρ ε : ℝ),
    0 < ρ → ρ ≤ 1 / 4 → 1 ≤ J → PilotOnset μ ρ J → 0 < m → 0 < ε →
    8 * Real.log (2 * (J : ℝ) / ε) ≤ m →
    1 - ε ≤ (experimentLaw μ ((pilotStage S J m ρ).endpoint false) q).real
      {z | (∀ i, i < J →
          μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ (i + 1)} ≤
            (pilotStage S J m ρ).upper ((processHistory z.2 (pilotStage S J m ρ).cap).take
              (pilotStage S J m ρ).pilotCost) i ∧
          (pilotStage S J m ρ).upper ((processHistory z.2 (pilotStage S J m ρ).cap).take
              (pilotStage S J m ρ).pilotCost) i ≤ pilotBound μ J ρ (i + 1)) ∧
        (∀ x : ℝ, (μ.map Subtype.val) (Set.Iic x) ≤
          (pilotStage S J m ρ).learnedLaw ((processHistory z.2 (pilotStage S J m ρ).cap).take
            (pilotStage S J m ρ).pilotCost) (Set.Iic x)) ∧
        zeroSelection ((pilotStage S J m ρ).learnedLaw ((processHistory z.2
            (pilotStage S J m ρ).cap).take (pilotStage S J m ρ).pilotCost)) ρ (4 ^ J) ≤
          16777216 * EntropyTail.selection μ ρ (4 ^ J)}

/-- (A11) on the same event (A8) with its finite onset, under the law of the
original hidden-gap experiment of the whole stage. There is a depth `J₀ ≥ 1`,
depending on the gap law and the rarity only and chosen before the seed type,
the sign law, the stage, `m` and `ε`, such that the event of
`StagePilotOracleStatement` has probability at least `1 - ε` at every target
depth `J ≥ J₀`. -/
def StagePilotOracleEventuallyStatement : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ : ℝ), 0 < ρ → ρ ≤ 1 / 4 →
    ∃ J₀ : ℕ, 1 ≤ J₀ ∧ ∀ (R : Type) [MeasurableSpace R] (q : SignLaw) (S : LearnedStage R)
      (J m : ℕ) (ε : ℝ), J₀ ≤ J → 0 < m → 0 < ε → 8 * Real.log (2 * (J : ℝ) / ε) ≤ m →
      1 - ε ≤ (experimentLaw μ ((pilotStage S J m ρ).endpoint false) q).real
        {z | (∀ i, i < J →
            μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ (i + 1)} ≤
              (pilotStage S J m ρ).upper ((processHistory z.2 (pilotStage S J m ρ).cap).take
                (pilotStage S J m ρ).pilotCost) i ∧
            (pilotStage S J m ρ).upper ((processHistory z.2 (pilotStage S J m ρ).cap).take
                (pilotStage S J m ρ).pilotCost) i ≤ pilotBound μ J ρ (i + 1)) ∧
          (∀ x : ℝ, (μ.map Subtype.val) (Set.Iic x) ≤
            (pilotStage S J m ρ).learnedLaw ((processHistory z.2 (pilotStage S J m ρ).cap).take
              (pilotStage S J m ρ).pilotCost) (Set.Iic x)) ∧
          zeroSelection ((pilotStage S J m ρ).learnedLaw ((processHistory z.2
              (pilotStage S J m ρ).cap).take (pilotStage S J m ρ).pilotCost)) ρ (4 ^ J) ≤
            16777216 * EntropyTail.selection μ ρ (4 ^ J)}

end ThresholdHC.StagePilotLaw
