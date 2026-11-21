import ThresholdHC.ArbitraryLawAdaptation.TailPilotLaw

/-! Target statements for the early-stopping pilot: an observable multi-depth
pilot that stops buying flips when its probes stop.

Source: `paper/v6/arbitrary-law-adaptation.tex`, section
`sec:arbitrary-law-adaptation` (proof of `thm:arbitrary-law-adaptation`),
subsubsection `Learning the envelope under one physical cap`. (UA6) gives the
budgets `b_j` and the coin cap `M`, and a copy of the depth-`j` probe stops
on its first unresolved coin, on completing `M` coins, or on exhausting its
`b_j` flips; a partial coin is charged but not counted. (UA8) is the pilot's
event, the pathwise cap is `P_J = m sum_j b_j` (UA10), and the subsubsection
ends with the remark `The cap M makes easy-law pilots stop without spending
all their authorized flips.` The checked pilot of
`ArbitraryLawAdaptation.pilotEstimator` buys every block in full
(`docs/ARBITRARY_LAW_FORMALIZATION.md`, the observable tail and the pilot
sections), so the remark was not formalized.

* `IsEarlyPilot J m ρ A`: a family of observable estimators without private
  randomness in effect, index `i` reporting depth `i + 1`, all with one
  policy. On every admissible path each buys at most the full pilot's cap
  `m sum_j b_j` (`pilotCost J m`). On every table of coin tapes it buys
  exactly the tape-level charge of the stopping probes: probe `k` of depth
  `j + 1` reads the coins `Nat.pair j (Nat.pair k c)` and is charged
  `probeFlips = min(b, work up to its stop)`. Its certificate at depth `i + 1`
  is the tape-level median of those probes, the certificate of the full pilot.
* `EarlyPilotExistsStatement`: such a family exists for `0 < ρ` and `0 < m`.
  The four other statements quantify over every family that meets the
  predicate; this one makes them non-vacuous.
* `EarlyPilotEventStatement`: (UA8) for the early pilot, under the law of the
  original hidden-gap experiment, with the hypotheses of
  `ArbitraryLawAdaptation.observable_pilot_event`.
* `EarlyPilotWorkStatement`: the expected number of flips bought is at most
  `m sum_j min(b_j, M W_j)`, with `W_j = ∫ w_j dμ` the work envelope.
* `EasyLawWorkStatement`: when every gap is at least `a > 0`, the expected
  number of flips is at most `512 m M J (J + 3) / a^2`.
* `EasyLawVanishingStatement`: for fixed `a`, `ρ` and `ε`, past a depth that
  depends on them only, an easy-law pilot spends at most an `ε` fraction of
  its authorized flips `m sum_j b_j`, for every such gap law.

Deviations from the source: index `i < J` stands for depth `i + 1`; the
paper's odd `m` is not needed; the early pilot is a new standalone estimator
and is not installed in the learning stage, whose results still charge the
full pilot. The remark is qualitative in the paper: the work bounds of the
last three statements are derived here and are not paper statements. The
finer per-probe cap `min(b_j, M 4^j)` holds on table paths through the work
identity but is not stated on arbitrary admissible paths. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.EarlyPilot
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.HardBudget
open ThresholdHC.ObservableSimulation ThresholdHC.ArbitraryLawAdaptation

/-- An observable pilot, fixed before the law, that stops buying when its
probes stop. Index `i` reports depth `i + 1`, and every index shares one
policy. On every admissible path it buys at most the full pilot's cap
`m sum_j b_j`. On every table of coin tapes it buys exactly the tape-level
charge of the stopping probes: probe `k` of depth `j + 1` on the coins
`Nat.pair j (Nat.pair k c)`, stopped on its first unresolved coin, on `M`
coins or on `b_j` flips. Its certificate at depth `i + 1` is the tape-level
median of those probes. -/
def IsEarlyPilot (J m : ℕ) (ρ : ℝ) (A : ℕ → AdaptiveEstimator Unit) : Prop :=
  (∀ i, (A i).policy = (A 0).policy) ∧
  (∀ i, PathwiseCap (A i) (pilotCost J m)) ∧
  (∀ (s : Table) (i : ℕ), totalProcessWork (populationPath ((A i).policy ()) s) =
      ((∑ j ∈ Finset.range J, ∑ k ∈ Finset.range m,
        probeFlips (j + 1) (pilotBudget J (j + 1)) (pilotCoinCap J ρ) (pilotStreams s j k) : ℕ) :
          ℝ≥0∞)) ∧
  (∀ (s : Table) (i : ℕ), i < J →
      (A i).output ((), populationPath ((A i).policy ()) s) =
        medianUpper (i + 1) m (fun _ => pilotBudget J (i + 1)) (fun _ => pilotCoinCap J ρ)
          (pilotStreams s i))

/-- An early-stopping pilot exists for every target depth, every number of
probes `m ≥ 1` and every `ρ > 0`. -/
def EarlyPilotExistsStatement : Prop :=
  ∀ (J m : ℕ) (ρ : ℝ), 0 < ρ → 0 < m → ∃ A : ℕ → AdaptiveEstimator Unit, IsEarlyPilot J m ρ A

/-- (UA8) for the early-stopping pilot under the original hidden-gap
experiment: with `m ≥ 8 log(2J/ε)` probes at every depth, with probability at
least `1 - ε` the certificate of every depth `j = i + 1 ≤ J` satisfies
`F(2^{-j}) ≤ U_j ≤ 128 (u_j + W_j/b_j + 1/M)`. -/
def EarlyPilotEventStatement : Prop :=
  ∀ (J m : ℕ) (ρ : ℝ) (A : ℕ → AdaptiveEstimator Unit), IsEarlyPilot J m ρ A →
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (i₀ : ℕ) (ε : ℝ),
      0 < ρ → 1 ≤ J → 0 < m → 0 < ε → 8 * Real.log (2 * (J : ℝ) / ε) ≤ m →
      1 - ε ≤ (experimentLaw μ (A i₀) q).real
        {z | ∀ i, i < J →
          μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ (i + 1)} ≤ (A i).output (z.1.1, z.2) ∧
          (A i).output (z.1.1, z.2) ≤ pilotBound μ J ρ (i + 1)}

/-- Expected work: each probe of depth `j + 1` costs at most
`min(b_(j+1), M W_(j+1))` flips on average, so the pilot costs at most
`m sum_j min(b_j, M W_j)`. -/
def EarlyPilotWorkStatement : Prop :=
  ∀ (J m : ℕ) (ρ : ℝ) (A : ℕ → AdaptiveEstimator Unit), IsEarlyPilot J m ρ A →
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (i : ℕ),
      expectedWork μ (A i) q ≤ ENNReal.ofReal ((m : ℝ) * ∑ j ∈ Finset.range J,
        min (pilotBudget J (j + 1) : ℝ)
          ((pilotCoinCap J ρ : ℝ) * ∫ d : Gap, tailWorkEnvelope (j + 1) d ∂μ))

/-- Easy laws, with every gap at least `a > 0`: expected work at most
`512 m M J (J + 3) / a^2`, against the cap `m sum_j b_j ≥ m 4^J / 2` for `J ≥ 1`. -/
def EasyLawWorkStatement : Prop :=
  ∀ (J m : ℕ) (ρ : ℝ) (A : ℕ → AdaptiveEstimator Unit), IsEarlyPilot J m ρ A →
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (i : ℕ) (a : ℝ),
      0 < a → (∀ᵐ d : Gap ∂μ, a ≤ (d : ℝ)) →
      expectedWork μ (A i) q ≤
        ENNReal.ofReal (512 * m * pilotCoinCap J ρ * J * (J + 3) / a ^ 2)

/-- Easy-law pilots spend a vanishing fraction of their authorized flips: for
fixed `a`, `ρ` and `ε` there is a depth `J₀`, the same for every gap law with
gaps at least `a`, past which the expected work is at most `ε m sum_j b_j`. -/
def EasyLawVanishingStatement : Prop :=
  ∀ (a ρ ε : ℝ), 0 < a → 0 < ρ → 0 < ε → ∃ J₀ : ℕ,
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ], (∀ᵐ d : Gap ∂μ, a ≤ (d : ℝ)) →
    ∀ (J m : ℕ) (A : ℕ → AdaptiveEstimator Unit), J₀ ≤ J → IsEarlyPilot J m ρ A →
      ∀ (q : SignLaw) (i : ℕ), expectedWork μ (A i) q ≤ ENNReal.ofReal (ε * pilotCost J m)

end ThresholdHC.EarlyPilot
