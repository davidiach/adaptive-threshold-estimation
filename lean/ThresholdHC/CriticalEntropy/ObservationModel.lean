import ThresholdHC.CriticalEntropy.PopulationModel

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ThresholdHC.CriticalEntropy

def wordHeads {n : ℕ} (x : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun i => x i = true)).card

def stoppedSeedCell {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) {n : ℕ} (x : Fin n → Bool) (S : Set R) : Set R :=
  {r | r ∈ S ∧ (r,x) ∈ A.stopPrefix n}

def wordLikelihood (p : unitInterval) (n k : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((p : ℝ)^k*(1-(p : ℝ))^(n-k))

def populationWordLikelihood {D : Type} [MeasurableSpace D]
    (μ : Measure D) (p₀ p₁ q : D → unitInterval) (n k : ℕ) : ℝ≥0∞ :=
  ∫⁻ d, ENNReal.ofReal (q d : ℝ)*wordLikelihood (p₁ d) n k +
    ENNReal.ofReal (1-(q d : ℝ))*wordLikelihood (p₀ d) n k ∂μ

/-- A stopped binary word of length at most the deterministic cap. -/
abbrev CappedWord (m : ℕ) := Σ n : Fin (m+1), Fin (n : ℕ) → Bool

instance cappedWord_fintype (m : ℕ) : Fintype (CappedWord m) :=
  inferInstanceAs (Fintype (Σ n : Fin (m+1), Fin (n : ℕ) → Bool))

instance cappedWord_measurableSpace (m : ℕ) : MeasurableSpace (CappedWord m) := ⊤

instance cappedWord_measurableSingleton (m : ℕ) : MeasurableSingletonClass (CappedWord m) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- Full seed and stopped word. Outside a cap guarantee this uses a bounded
fallback; all experiment identities below require actual stopping by the cap. -/
def cappedTranscript {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) (m : ℕ) (z : R × (ℕ → Bool)) : R × CappedWord m :=
  (z.1,⟨⟨min (A.stop z).toNat m, Nat.lt_succ_of_le (min_le_right _ _)⟩,
    Tier2.tapePrefix (min (A.stop z).toNat m) z.2⟩)

/-- The observation law is the pushforward of the actual hidden-coin generator. -/
def cappedTranscriptLaw {D R E : Type} [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) (ν : Measure R) (p₀ p₁ q : D → unitInterval)
    (A : StoppedProcedure R E) (m : ℕ) : Measure (R × CappedWord m) :=
  (populationMeasure μ ν).map (cappedTranscript A m ∘ populationInput p₀ p₁ q)

/-- Reference mass of each seed/word cell; independent of the sign prior. -/
def stoppedReference {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) (A : StoppedProcedure R E) (m : ℕ) : Measure (R × CappedWord m) :=
  (ν.prod Measure.count).restrict {z | (z.1,z.2.2) ∈ A.stopPrefix z.2.1.val}

/-- The finite statistic used in the common-pair argument. -/
def stoppedStatistic (m : ℕ) (w : CappedWord m) : Fin (m+1) × Fin (m+1) :=
  (w.1,⟨wordHeads w.2, lt_of_le_of_lt (by
    unfold wordHeads
    simpa using Finset.card_filter_le (s := Finset.univ) (fun i => w.2 i = true)) w.1.isLt⟩)

def cappedStatisticLaw {D R E : Type} [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) (ν : Measure R) (p₀ p₁ q : D → unitInterval)
    (A : StoppedProcedure R E) (m : ℕ) : Measure (Fin (m+1) × Fin (m+1)) :=
  (cappedTranscriptLaw μ ν p₀ p₁ q A m).map (fun z => stoppedStatistic m z.2)

/-- Conditional reconstruction on a finite-statistic cell. It depends on the
seed law and policy, not on the population. Null cells receive the zero measure. -/
def transcriptReconstruction {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) (A : StoppedProcedure R E) (m : ℕ) (i : Fin (m+1) × Fin (m+1)) :
    Measure (R × CappedWord m) :=
  cond (stoppedReference ν A m) ((fun z => stoppedStatistic m z.2) ⁻¹' {i})

end ThresholdHC.CriticalEntropy
