import ThresholdHC.ArbitraryLawAdaptation.LearnedOracle

/-! (A11) on the same event (A8), on the coin array.

The audited coin-array form `original_pilotStage_oracle` keeps the domination
by the learned law and drops both halves of (A8). Here the full event is kept:
with probability at least `1 - ε` on the coin array of the original simulation
law, the certificates read off the pilot's word satisfy both halves of (A8),
the learned law dominates the gap law in distribution, and it satisfies
(A11). The selection bound uses only the upper half of (A8). -/

noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace ThresholdHC.StagePilotLaw
open ThresholdHC.Tier6 ThresholdHC.ObservableSimulation ThresholdHC.ArbitraryLawAdaptation

variable {R : Type} [MeasurableSpace R]

/-- (A11) on the same event (A8), on the coin array. Under the pilot's onset
condition and with `m ≥ 8 log(2J/ε)` probes at every depth, with probability
at least `1 - ε` on the coin array of the original simulation law, the
certificates read off the pilot's word satisfy both halves of (A8), the
stage's learned law dominates the gap law in distribution, and its selection
functional is at most `2^24` times the oracle's. -/
theorem original_pilotStage_oracle_event (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (S : LearnedStage R) (J m : ℕ) {ρ ε : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4)
    (hJ : 1 ≤ J) (hon : PilotOnset μ ρ J) (hm : 0 < m) (hε : 0 < ε)
    (hmε : 8 * log (2 * (J : ℝ) / ε) ≤ m) :
    1 - ε ≤
      (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).real
        {ω | (∀ i, i < J →
            μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ (i + 1)} ≤
              (pilotStage S J m ρ).upper (pilotStageWord J m ρ ω) i ∧
            (pilotStage S J m ρ).upper (pilotStageWord J m ρ ω) i ≤
              pilotBound μ J ρ (i + 1)) ∧
          (∀ x : ℝ, (μ.map Subtype.val) (Set.Iic x) ≤
            (pilotStage S J m ρ).learnedLaw (pilotStageWord J m ρ ω) (Set.Iic x)) ∧
          zeroSelection ((pilotStage S J m ρ).learnedLaw (pilotStageWord J m ρ ω)) ρ (4 ^ J) ≤
            16777216 * EntropyTail.selection μ ρ (4 ^ J)} := by
  refine (original_pilotStage_event μ q S J m hρ hJ hm hε hmε).trans (measureReal_mono ?_)
  intro ω hω
  exact ⟨hω.1, hω.2, pilotStage_selection_le μ S hρ hρ4 hJ hon m _ fun i hi => (hω.1 i hi).2⟩

end ThresholdHC.StagePilotLaw
