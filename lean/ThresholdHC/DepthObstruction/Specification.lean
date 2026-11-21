import ThresholdHC.CapIdentification.DiameterAttainment
import ThresholdHC.CriticalEntropy.LocalSimulation

/-! Target statements for part 1 of the bounded-depth obstruction: the
population, cross-coin-feedback half of the theorem `thm:cap` (Feedback does not
repair bounded-depth nonidentifiability) of
`research/2026-10-27-nonlinear-population/upper/proof-body.tex` (lines 87-151),
also summarised in `research/2026-10-27-nonlinear-population/FINAL_REPORT.md`
(line 19) and in the row Bounded-depth obstruction of `docs/SECONDARY_CLAIMS.md`
(line 135).

The source says that every coin word of length at most `2K` has the same
probability under its two sign profiles, and that therefore every population
procedure using at most `2K` observations per coin, with arbitrary pilots,
interleaving and cross-coin feedback, has identical transcript laws under them,
so that its worst RMS error is at least half the target separation, whatever its
total work. Here the per-coin cap is a general `N`, the gap law `μ` is arbitrary,
and the two sign laws are any pair whose first `ceil(N/2)` odd gap moments agree
(`CapIdentification.OddMomentMatch`), which is exactly equality of every coin
word probability through depth `N` (`CapIdentification.odd_moments_iff_count_match`).

* `PerCoinCap A N`: on every simulated population path of the unchanged
  observable experiment, every coin label receives at most `N` flips.
* `CappedTranscriptStatement`: such a procedure has the same joint law of seed
  and full observed transcript under the two sign laws. No almost-sure
  termination hypothesis is needed: the output is a measurable function of the
  seed and the full transcript.
* `EqualLawFloorStatement`: equal seed-and-transcript laws force the larger of
  the two RMS errors to be at least half the target separation (the last display
  of the proof of `thm:cap`), retaining infinite risk.
* `PopulationCapFloorStatement`: a formal-only extension, not a claim of the
  source. Half the attained cap-`N` diameter `CapIdentification.capDiameter`
  floors the rare-prior RMS risk of every per-coin-capped population procedure,
  for every gap law. It extends `CapIdentification.fixed_cap_identification` from
  single stopped procedures to arbitrary population feedback.
* `HistoryCapBridgeStatement`: the history-count form of a per-coin cap used in
  `RestrictedRMS.three_flip_coefficient_iff`, with bound `N`, implies
  `PerCoinCap A N`.

The explicit odd-Legendre hard pair for the exact quadratic law, its separation
`ρ/((K+1)(2K+1))` and the depth-tail bound `thm:tail` are not stated here. -/

noncomputable section
namespace ThresholdHC.DepthObstruction
open MeasureTheory
open scoped ENNReal
open ThresholdHC.Tier6 (Gap SignLaw signMean AdaptiveEstimator experimentLaw rootMeanRisk
  populationOutput)
open ThresholdHC.RareAboveTwo (rareRisk)
open ThresholdHC.CapIdentification (OddMomentMatch capDiameter)

/-- Each coin supplies at most `N` flips: on every finite horizon of the population
simulation, for every seed and every family of coin tapes, every label is queried
at most `N` times. -/
def PerCoinCap {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (N : ℕ) : Prop :=
  ∀ (r : R) (n : ℕ) (s : ℕ → ℕ → Bool) (i : ℕ),
    (CriticalEntropy.populationSimulation (A.policy r) n s).1 i ≤ N

/-- proof-body.tex, `thm:cap`, transcript part (lines 98-100, 130-139): with
matching odd moments through depth `N`, every procedure with per-coin cap `N`,
including arbitrary cross-coin feedback, has the same seed-and-transcript law. -/
def CappedTranscriptStatement : Prop :=
  ∀ (R : Type) [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (qH qL : SignLaw) (N : ℕ) (A : AdaptiveEstimator R),
    OddMomentMatch μ qH qL N → PerCoinCap A N →
    (experimentLaw μ A qH).map (fun z => (z.1.1, z.2)) =
      (experimentLaw μ A qL).map (fun z => (z.1.1, z.2))

/-- proof-body.tex, `thm:cap`, final display of the proof (lines 144-150): equal
observable laws give worst RMS error at least half the target separation. -/
def EqualLawFloorStatement : Prop :=
  ∀ (R : Type) [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (qH qL : SignLaw),
    (experimentLaw μ A qH).map (fun z => (z.1.1, z.2)) =
      (experimentLaw μ A qL).map (fun z => (z.1.1, z.2)) →
    ENNReal.ofReal (|signMean μ qH.val - signMean μ qL.val| / 2) ≤
      max (rootMeanRisk (experimentLaw μ A qH) (populationOutput A) (signMean μ qH.val))
          (rootMeanRisk (experimentLaw μ A qL) (populationOutput A) (signMean μ qL.val))

/-- Formal-only extension, not a source claim: for every gap law, half the cap-`N`
diameter floors the rare-prior RMS risk of every per-coin-capped population
procedure, whatever its total work. -/
def PopulationCapFloorStatement : Prop :=
  ∀ (R : Type) [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ : ℝ) (N : ℕ) (A : AdaptiveEstimator R), 0 ≤ ρ → PerCoinCap A N →
    ENNReal.ofReal (capDiameter μ ρ N / 2) ≤ rareRisk μ A ρ

/-- Bridge: the history-count cap of `RestrictedRMS.three_flip_coefficient_iff`
(whenever label `j` is queried after history `xs`, fewer than `N` earlier queries
along `xs` went to `j`) implies `PerCoinCap A N`. -/
def HistoryCapBridgeStatement : Prop :=
  ∀ (R : Type) [MeasurableSpace R] (A : AdaptiveEstimator R) (N : ℕ),
    (∀ (s : R) (xs : List Bool) (j : ℕ), A.policy s xs = some j →
      (List.range xs.length).countP (fun i => decide (A.policy s (xs.take i) = some j)) < N) →
    PerCoinCap A N

end ThresholdHC.DepthObstruction
