import ThresholdHC.ArbitraryLawAdaptation.TailBlockReader
import ThresholdHC.ArbitraryLawAdaptation.TailOracleLaw
import ThresholdHC.HardBudget.Controller

/-! The tail certificate in the observable experiment.

The estimators here see only flips. Each one buys a fixed number of flips with
a reader and reports a function of the observed word. Any event about the
observed word has the same probability in the original hidden-gap experiment
as the same event about the reader's word on the coin array of the original
simulation law. The coin-array statements of the tail certificate therefore
hold for the estimator's output under the law of the original experiment:
statement (1), its version with a coin cap, the oracle comparison (3), and the
versions for a finite range of depths.

The reader buys every block in full, so the estimator is charged its cap on
every path; flips bought after a probe has stopped are ignored. Coverage holds
at every pause: the certificate computed from the first `t` observed flips
covers the small-gap mass for every `t` at once. -/

noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace ThresholdHC.ArbitraryLawAdaptation
open ThresholdHC.Tier2 ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.CriticalEntropy
open ThresholdHC.ObservableSimulation ThresholdHC.EntropyTailQuantile
open ThresholdHC.HardBudget ThresholdHC.BlindUpper

/-- The estimator that buys exactly `n` flips with the reader `p` and reports
`out` of the observed word. It has no private randomness. -/
def wordEstimator (n : ℕ) (p : Reader) (out : List Bool → ℝ) : AdaptiveEstimator Unit where
  randomLaw := Measure.dirac ()
  probability := inferInstance
  policy _ := stopAt n p
  policy_measurable := by
    intro xs a
    exact measurableSet_eq_fun measurable_const measurable_const
  output z := out (processHistory z.2 n)
  output_measurable :=
    (measurable_from_top (f := out)).comp ((measurable_processHistory_fixed n).comp measurable_snd)

/-- The estimator buys at most `n` flips on every path. -/
theorem wordEstimator_cap (n : ℕ) (p : Reader) (out : List Bool → ℝ) :
    PathwiseCap (wordEstimator n p out) n :=
  stopAt_pathwise_cap _ _ _ (fun _ => rfl)

/-- On every table of coin tapes, the history the estimator observes is the
word of its block. -/
theorem wordEstimator_history (n : ℕ) (p : Reader) (s : Table) :
    processHistory (populationPath (stopAt n p) s) n = (readBlock n p s).1 := by
  have h := processHistory_word (readBlock n p s).1
  rw [readBlock_length] at h
  rw [block_path]
  exact h

/-- On every table of coin tapes, the estimator reports `out` of the word of
its block. -/
theorem wordEstimator_output (n : ℕ) (p : Reader) (out : List Bool → ℝ) (s : Table) :
    (wordEstimator n p out).output
        ((), populationPath ((wordEstimator n p out).policy ()) s) =
      out (readBlock n p s).1 := by
  change out (processHistory (populationPath (stopAt n p) s) n) = _
  rw [wordEstimator_history]

/-- Transfer to the original experiment. Any event about the observed word has
the same probability under the law of the original hidden-gap experiment as
the same event about the block's word on the coin array of the original
simulation law. -/
theorem original_word_event (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (n : ℕ) (p : Reader) (out : List Bool → ℝ) (S : Set (List Bool)) :
    (experimentLaw μ (wordEstimator n p out) q).real {z | processHistory z.2 n ∈ S} =
      (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).real
        {ω | (readBlock n p ω).1 ∈ S} := by
  let A := wordEstimator n p out
  let E : Set (Unit × ProcessTape) := {y | processHistory y.2 n ∈ S}
  have hE : MeasurableSet E :=
    ((measurable_processHistory_fixed n).comp measurable_snd) MeasurableSpace.measurableSet_top
  have hg : Measurable (fun z : PopulationSeed Unit × ProcessTape => (z.1.1, z.2)) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hp : Measurable (fun z : Unit × Table => (z.1, populationPath (A.policy z.1) z.2)) :=
    measurable_fst.prodMk (measurable_seeded_populationPath A.policy
      (fun xs => measurable_to_countable' (A.policy_measurable xs)))
  have h1 : (experimentLaw μ A q).real {z | processHistory z.2 n ∈ S} =
      ((experimentLaw μ A q).map (fun z => (z.1.1, z.2))).real E :=
    (map_measureReal_apply hg hE).symm
  have hdirac : originalSimulationLaw μ A q =
      (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).map (Prod.mk ()) := by
    unfold originalSimulationLaw
    exact Measure.dirac_prod ()
  change (experimentLaw μ A q).real {z | processHistory z.2 n ∈ S} = _
  rw [h1, original_observable_simulation_law, map_measureReal_apply hp hE, hdirac,
    map_measureReal_apply measurable_prodMk_left (hp hE)]
  congr 1
  ext ω
  change processHistory (populationPath (stopAt n p) ω) n ∈ S ↔ (readBlock n p ω).1 ∈ S
  rw [wordEstimator_history]

/-- A lower bound on the coin array for an event that implies an event about
the block's word gives the same lower bound in the original experiment. -/
theorem observable_of_array (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (n : ℕ) (p : Reader) (out : List Bool → ℝ) (S : Set (List Bool)) {c : ℝ}
    {G : Set (ℕ → ℕ → Bool)} (hG : G ⊆ {ω | (readBlock n p ω).1 ∈ S})
    (h : c ≤ (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).real G) :
    c ≤ (experimentLaw μ (wordEstimator n p out) q).real {z | processHistory z.2 n ∈ S} := by
  rw [original_word_event]
  exact h.trans (measureReal_mono hG)

/-- The median certificate with a coin cap, on one coin array. Probe `j` reads
the coins `Nat.pair j i`. -/
theorem original_median_certificate_array (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (J m b M : ℕ) (hm : 0 < m) (hb : 0 < b) (hM : 0 < M) {δ : ℝ} (hδ : 0 < δ)
    (hmδ : 8 * log (2 / δ) ≤ m) :
    1 - δ ≤
      (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).real
        {ω | (∀ b' M' : ℕ → ℕ, μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤
            medianUpper J m b' M' (fun j i => ω (Nat.pair j i))) ∧
          medianUpper J m (fun _ => b) (fun _ => M) (fun j i => ω (Nat.pair j i)) ≤
            min 1 (128 * max (max (tailUnresolvedMass μ J)
              ((∫ d : Gap, tailWorkEnvelope J d ∂μ) / b)) (1 / M))} := by
  have hsplit : Measurable (fun (ω : ℕ → ℕ → Bool) (j i : ℕ) => ω (Nat.pair j i)) :=
    Measurable.of_eval fun j => Measurable.of_eval fun i => measurable_pi_apply _
  have hfail := original_medianFailure_le μ q J m b M hm hb hM
  rw [← infinitePi_map_blocks (originalPopulationTapeLaw μ q)] at hfail
  have h := one_sub_le_real_preimage
    (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)) hsplit
    (measurableSet_medianFailure _ _ _ _ _ _)
    (Good := {z | (∀ b' M' : ℕ → ℕ,
        μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤ medianUpper J m b' M' z) ∧
      medianUpper J m (fun _ => b) (fun _ => M) z ≤
        min 1 (128 * max (max (tailUnresolvedMass μ J)
          ((∫ d : Gap, tailWorkEnvelope J d ∂μ) / b)) (1 / M))})
    (fun z hz => median_good_of_not_failure hz) hfail
  have hcal := two_exp_le_of_log_le hδ hmδ
  exact le_trans (by linarith) h

/-- The observable tail estimator at depth `J`: `m` probes one after another,
each with a block of `b` flips and coin cap `M`. It reports the median
certificate computed from the observed word. -/
def tailEstimator (J m b M : ℕ) : AdaptiveEstimator Unit :=
  wordEstimator (m * b) (medianReader J M b m) (medianWordUpper J m b M)

/-- The tail estimator buys at most `m b` flips on every path. -/
theorem tailEstimator_cap (J m b M : ℕ) : PathwiseCap (tailEstimator J m b M) (m * b) :=
  wordEstimator_cap _ _ _

/-- On every table of coin tapes, the tail estimator reports the tape-level
median certificate of probes reading the coins `Nat.pair j i`. -/
theorem tailEstimator_output (J m b M : ℕ) (s : Table) :
    (tailEstimator J m b M).output
        ((), populationPath ((tailEstimator J m b M).policy ()) s) =
      medianUpper J m (fun _ => b) (fun _ => M) (fun j i => s (Nat.pair j i)) := by
  unfold tailEstimator
  rw [wordEstimator_output, medianWordUpper_readBlock]

/-- The observable median certificate with a coin cap. In the original
hidden-gap experiment, for `m ≥ 8 log(2/δ)` probes with `b ≥ 1` flips and coin
cap `M ≥ 1` each, with probability at least `1 - δ` the certificate computed
from the first `t` observed flips covers `F(2^{-J})` for every `t`, and the
estimator's output is at most `min{1, 128 max(u_J, W_J/b, 1/M)}`. -/
theorem observable_median_certificate (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (J m b M : ℕ) (hm : 0 < m) (hb : 0 < b) (hM : 0 < M) {δ : ℝ} (hδ : 0 < δ)
    (hmδ : 8 * log (2 / δ) ≤ m) :
    1 - δ ≤
      (experimentLaw μ (tailEstimator J m b M) q).real
        {z | (∀ t : ℕ, μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤
            medianWordUpper J m b M ((processHistory z.2 (m * b)).take t)) ∧
          (tailEstimator J m b M).output (z.1.1, z.2) ≤
            min 1 (128 * max (max (tailUnresolvedMass μ J)
              ((∫ d : Gap, tailWorkEnvelope J d ∂μ) / b)) (1 / M))} := by
  refine observable_of_array μ q (m * b) (medianReader J M b m) (medianWordUpper J m b M)
    {w | (∀ t : ℕ, μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤
        medianWordUpper J m b M (w.take t)) ∧
      medianWordUpper J m b M w ≤
        min 1 (128 * max (max (tailUnresolvedMass μ J)
          ((∫ d : Gap, tailWorkEnvelope J d ∂μ) / b)) (1 / M))} ?_
    (original_median_certificate_array μ q J m b M hm hb hM hδ hmδ)
  rintro ω ⟨h1, h2⟩
  refine ⟨fun t => ?_, ?_⟩
  · rw [medianWordUpper_take]
    exact h1 _ _
  · rw [medianWordUpper_readBlock]
    exact h2

/-- Statement (1) of the tail certificate in the observable experiment. For
`m ≥ 8 log(2/δ)` probes with `4^J` flips each, the estimator buys at most
`m 4^J` flips, and with probability at least `1 - δ` the certificate computed
from the first `t` observed flips covers `F(2^{-J})` for every `t`, and the
output `U` satisfies `U ≤ min{1, 128 max(u_J, W_J/4^J)}`. -/
theorem observable_tail_certificate (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (J m : ℕ) (hm : 0 < m) {δ : ℝ} (hδ : 0 < δ) (hmδ : 8 * log (2 / δ) ≤ m) :
    1 - δ ≤
      (experimentLaw μ (tailEstimator J m (4 ^ J) (4 ^ J)) q).real
        {z | (∀ t : ℕ, μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤
            medianWordUpper J m (4 ^ J) (4 ^ J) ((processHistory z.2 (m * 4 ^ J)).take t)) ∧
          (tailEstimator J m (4 ^ J) (4 ^ J)).output (z.1.1, z.2) ≤
            min 1 (128 * max (tailUnresolvedMass μ J)
              ((∫ d : Gap, tailWorkEnvelope J d ∂μ) / 4 ^ J))} := by
  refine observable_of_array μ q (m * 4 ^ J) (medianReader J (4 ^ J) (4 ^ J) m)
    (medianWordUpper J m (4 ^ J) (4 ^ J))
    {w | (∀ t : ℕ, μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤
        medianWordUpper J m (4 ^ J) (4 ^ J) (w.take t)) ∧
      medianWordUpper J m (4 ^ J) (4 ^ J) w ≤
        min 1 (128 * max (tailUnresolvedMass μ J)
          ((∫ d : Gap, tailWorkEnvelope J d ∂μ) / 4 ^ J))} ?_
    (original_tail_certificate_array μ q J m hm hδ hmδ)
  rintro ω ⟨h1, h2⟩
  refine ⟨fun t => ?_, ?_⟩
  · rw [medianWordUpper_take]
    exact h1 _ _
  · rw [medianWordUpper_readBlock]
    exact h2

/-- Statement (3) of the tail certificate in the observable experiment. At a
depth that meets the onset condition, with probability at least `1 - δ` the
certificate covers `F(2^{-J})` at every pause and the output is at most
`524288 K_{μ,ρ}(4^J)`. -/
theorem observable_tail_oracle (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) (J m : ℕ) (hm : 0 < m) {δ : ℝ} (hδ : 0 < δ)
    (hmδ : 8 * log (2 / δ) ≤ m) (hon : TailOnset μ ρ J) :
    1 - δ ≤
      (experimentLaw μ (tailEstimator J m (4 ^ J) (4 ^ J)) q).real
        {z | (∀ t : ℕ, μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤
            medianWordUpper J m (4 ^ J) (4 ^ J) ((processHistory z.2 (m * 4 ^ J)).take t)) ∧
          ENNReal.ofReal ((tailEstimator J m (4 ^ J) (4 ^ J)).output (z.1.1, z.2)) ≤
            524288 * EntropyTail.selection μ ρ (4 ^ J)} := by
  refine (observable_tail_certificate μ q J m hm hδ hmδ).trans (measureReal_mono ?_)
  rintro z ⟨h1, h2⟩
  exact ⟨h1, (ENNReal.ofReal_le_ofReal h2).trans (tail_bound_le_oracle μ hρ hρ4 J hon)⟩

/-- Statement (3) in the observable experiment, past the onset. There is a
finite onset `J₀`, depending on the gap law and `ρ` only, such that the bound
of `observable_tail_oracle` holds at every depth `J ≥ J₀`. -/
theorem observable_tail_oracle_eventually (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) :
    ∃ J₀ : ℕ, ∀ (J m : ℕ) (δ : ℝ), J₀ ≤ J → 0 < m → 0 < δ → 8 * log (2 / δ) ≤ m →
      1 - δ ≤
        (experimentLaw μ (tailEstimator J m (4 ^ J) (4 ^ J)) q).real
          {z | (∀ t : ℕ, μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤
              medianWordUpper J m (4 ^ J) (4 ^ J)
                ((processHistory z.2 (m * 4 ^ J)).take t)) ∧
            ENNReal.ofReal ((tailEstimator J m (4 ^ J) (4 ^ J)).output (z.1.1, z.2)) ≤
              524288 * EntropyTail.selection μ ρ (4 ^ J)} := by
  obtain ⟨J₀, hJ₀⟩ := tailOnset_eventually μ hρ (by linarith)
  exact ⟨J₀, fun J m δ hJ hm hδ hmδ =>
    observable_tail_oracle μ q hρ hρ4 J m hm hδ hmδ (hJ₀ J hJ)⟩

/-- The observable estimator of the depths `J ≤ L`. Depth `J` runs `m J`
probes, each with `b J` flips and coin cap `M J`. The estimator reports the
certificate of depth `J₀`; the flips it buys do not depend on `J₀`. -/
def depthsEstimator (m b M : ℕ → ℕ) (L J₀ : ℕ) : AdaptiveEstimator Unit :=
  wordEstimator (depthsCost m b (L + 1)) (depthsReader m b M (L + 1)) (depthWordUpper m b M J₀)

/-- The estimator of the depths buys at most `∑_{J ≤ L} m_J b_J` flips on every
path. -/
theorem depthsEstimator_cap (m b M : ℕ → ℕ) (L J₀ : ℕ) :
    PathwiseCap (depthsEstimator m b M L J₀) (depthsCost m b (L + 1)) :=
  wordEstimator_cap _ _ _

/-- The estimators of the depths differ only in the certificate they report. -/
theorem depthsEstimator_policy (m b M : ℕ → ℕ) (L J₀ J₁ : ℕ) :
    (depthsEstimator m b M L J₀).policy = (depthsEstimator m b M L J₁).policy := rfl

/-- On every table of coin tapes, the estimator of the depths reports the
tape-level median certificate of depth `J₀ ≤ L`, probe `j` reading the coins
`Nat.pair J₀ (Nat.pair j i)`. -/
theorem depthsEstimator_output (m b M : ℕ → ℕ) (L : ℕ) {J₀ : ℕ} (hJ : J₀ ≤ L) (s : Table) :
    (depthsEstimator m b M L J₀).output
        ((), populationPath ((depthsEstimator m b M L J₀).policy ()) s) =
      medianUpper J₀ (m J₀) (fun _ => b J₀) (fun _ => M J₀)
        (fun j i => s (Nat.pair J₀ (Nat.pair j i))) := by
  unfold depthsEstimator
  rw [wordEstimator_output, depthWordUpper_readBlock m b M (L + 1) s (Nat.lt_succ_of_le hJ)]

/-- Every depth up to `L` at once, in the observable experiment. Depth `J`
runs `m_J ≥ 8 log(2J(J+1)/δ)` probes with `b_J ≥ 1` flips and coin cap
`M_J ≥ 1` each. With probability at least `1 - δ`, at every depth
`1 ≤ J ≤ L` the certificate of depth `J` computed from the first `t` observed
flips covers `F(2^{-J})` for every `t`, and the certificate computed from the
whole observed word is at most `min{1, 128 max(u_J, W_J/b_J, 1/M_J)}`. -/
theorem observable_median_depths (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (m b M : ℕ → ℕ) (L J₀ : ℕ) {δ : ℝ} (hδ : 0 < δ) (hm : ∀ J : ℕ, 1 ≤ J → 0 < m J)
    (hmδ : ∀ J : ℕ, 1 ≤ J → 8 * log (2 * ((J : ℝ) * (J + 1)) / δ) ≤ m J)
    (hb : ∀ J : ℕ, 1 ≤ J → 0 < b J) (hM : ∀ J : ℕ, 1 ≤ J → 0 < M J) :
    1 - δ ≤
      (experimentLaw μ (depthsEstimator m b M L J₀) q).real
        {z | ∀ J, 1 ≤ J → J ≤ L →
          (∀ t : ℕ, μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤
            depthWordUpper m b M J ((processHistory z.2 (depthsCost m b (L + 1))).take t)) ∧
          (depthsEstimator m b M L J).output (z.1.1, z.2) ≤
            min 1 (128 * max (max (tailUnresolvedMass μ J)
              ((∫ d : Gap, tailWorkEnvelope J d ∂μ) / b J)) (1 / M J))} := by
  refine observable_of_array μ q (depthsCost m b (L + 1)) (depthsReader m b M (L + 1))
    (depthWordUpper m b M J₀)
    {w | ∀ J, 1 ≤ J → J ≤ L →
      (∀ t : ℕ, μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤
        depthWordUpper m b M J (w.take t)) ∧
      depthWordUpper m b M J w ≤
        min 1 (128 * max (max (tailUnresolvedMass μ J)
          ((∫ d : Gap, tailWorkEnvelope J d ∂μ) / b J)) (1 / M J))} ?_
    (original_median_all_depths_array μ q m b M hδ hm hmδ hb hM)
  intro ω hω J hJ1 hJL
  obtain ⟨h1, h2⟩ := hω J hJ1
  have hlt : J < L + 1 := Nat.lt_succ_of_le hJL
  refine ⟨fun t => ?_, ?_⟩
  · rw [depthWordUpper_take m b M (L + 1) ω hlt]
    exact h1 _ _
  · rw [depthWordUpper_readBlock m b M (L + 1) ω hlt]
    exact h2

/-- Every depth up to `L` at once in the observable experiment, with the
oracle comparison. Depth `J` runs `m_J ≥ 8 log(2J(J+1)/δ)` probes with `4^J`
flips each. With probability at least `1 - δ`, at every depth `1 ≤ J ≤ L` the
certificate covers `F(2^{-J})` at every pause, and at every such depth that
meets the onset condition it is at most `524288 K_{μ,ρ}(4^J)`. -/
theorem observable_tail_oracle_depths (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) (m : ℕ → ℕ) (L J₀ : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hm : ∀ J : ℕ, 1 ≤ J → 0 < m J)
    (hmδ : ∀ J : ℕ, 1 ≤ J → 8 * log (2 * ((J : ℝ) * (J + 1)) / δ) ≤ m J) :
    1 - δ ≤
      (experimentLaw μ (depthsEstimator m (fun J => 4 ^ J) (fun J => 4 ^ J) L J₀) q).real
        {z | ∀ J, 1 ≤ J → J ≤ L →
          (∀ t : ℕ, μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤
            depthWordUpper m (fun J => 4 ^ J) (fun J => 4 ^ J) J
              ((processHistory z.2 (depthsCost m (fun J => 4 ^ J) (L + 1))).take t)) ∧
          (TailOnset μ ρ J →
            ENNReal.ofReal ((depthsEstimator m (fun J => 4 ^ J) (fun J => 4 ^ J) L J).output
                (z.1.1, z.2)) ≤
              524288 * EntropyTail.selection μ ρ (4 ^ J))} := by
  have hN : ∀ J : ℕ, 1 ≤ J → 0 < 4 ^ J := fun J _ => pow_pos (by norm_num) J
  refine (observable_median_depths μ q m (fun J => 4 ^ J) (fun J => 4 ^ J) L J₀ hδ hm hmδ
    hN hN).trans (measureReal_mono ?_)
  intro z hz J hJ1 hJL
  obtain ⟨h1, h2⟩ := hz J hJ1 hJL
  refine ⟨h1, fun hon => ?_⟩
  rw [tail_bound_uncapped μ J] at h2
  exact (ENNReal.ofReal_le_ofReal h2).trans (tail_bound_le_oracle μ hρ hρ4 J hon)

/-- Every depth up to `L` at once in the observable experiment, past the
onset. There is a finite onset `J₀`, depending on the gap law and `ρ` only,
such that the oracle bound of `observable_tail_oracle_depths` holds at every
depth `J₀ ≤ J ≤ L`. -/
theorem observable_tail_oracle_depths_eventually (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) :
    ∃ J₀ : ℕ, ∀ (m : ℕ → ℕ) (L J₁ : ℕ) (δ : ℝ), 0 < δ → (∀ J : ℕ, 1 ≤ J → 0 < m J) →
      (∀ J : ℕ, 1 ≤ J → 8 * log (2 * ((J : ℝ) * (J + 1)) / δ) ≤ m J) →
      1 - δ ≤
        (experimentLaw μ (depthsEstimator m (fun J => 4 ^ J) (fun J => 4 ^ J) L J₁) q).real
          {z | ∀ J, 1 ≤ J → J ≤ L →
            (∀ t : ℕ, μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤
              depthWordUpper m (fun J => 4 ^ J) (fun J => 4 ^ J) J
                ((processHistory z.2 (depthsCost m (fun J => 4 ^ J) (L + 1))).take t)) ∧
            (J₀ ≤ J →
              ENNReal.ofReal ((depthsEstimator m (fun J => 4 ^ J) (fun J => 4 ^ J) L J).output
                  (z.1.1, z.2)) ≤
                524288 * EntropyTail.selection μ ρ (4 ^ J))} := by
  obtain ⟨J₀, hJ₀⟩ := tailOnset_eventually μ hρ (by linarith)
  refine ⟨J₀, fun m L J₁ δ hδ hm hmδ => ?_⟩
  refine (observable_tail_oracle_depths μ q hρ hρ4 m L J₁ hδ hm hmδ).trans
    (measureReal_mono ?_)
  intro z hz J hJ1 hJL
  obtain ⟨h1, h2⟩ := hz J hJ1 hJL
  exact ⟨h1, fun hJ0 => h2 (hJ₀ J hJ0)⟩

end ThresholdHC.ArbitraryLawAdaptation
