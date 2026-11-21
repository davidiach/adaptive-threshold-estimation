import ThresholdHC.StagePilotLaw.Specification
import ThresholdHC.StagePilotLaw.Transfer
import ThresholdHC.StagePilotLaw.CoinEvent

/-! The pilot events (A8) and (A11) of the paid learning stage, under the law
of the original hidden-gap experiment of the whole stage, proved against the
specification.

Each event reads the certificates off the paid chronological prefix of the
observed history. `pilot_prefix_tape_real` turns its probability into the
probability, on the coin array of the original simulation law, of the same
event for the pilot's word on the coins `Nat.pair 0 i`; the coin-array events
are `original_pilotStage_event` and `original_pilotStage_oracle_event`. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.StagePilotLaw
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.ArbitraryLawAdaptation

theorem stage_pilot_event : StagePilotEventStatement := by
  intro R _ μ _ q S J m ρ ε hρ hJ hm hε hmε
  refine (original_pilotStage_event μ q S J m hρ hJ hm hε hmε).trans_eq ?_
  exact (pilot_prefix_tape_real (pilotStage S J m ρ) μ q (fun xs =>
    (∀ i, i < J →
      μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ (i + 1)} ≤ (pilotStage S J m ρ).upper xs i ∧
      (pilotStage S J m ρ).upper xs i ≤ pilotBound μ J ρ (i + 1)) ∧
    ∀ x : ℝ, (μ.map Subtype.val) (Set.Iic x) ≤
      (pilotStage S J m ρ).learnedLaw xs (Set.Iic x))).symm

theorem stage_pilot_oracle : StagePilotOracleStatement := by
  intro R _ μ _ q S J m ρ ε hρ hρ4 hJ hon hm hε hmε
  refine (original_pilotStage_oracle_event μ q S J m hρ hρ4 hJ hon hm hε hmε).trans_eq ?_
  exact (pilot_prefix_tape_real (pilotStage S J m ρ) μ q (fun xs =>
    (∀ i, i < J →
      μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ (i + 1)} ≤ (pilotStage S J m ρ).upper xs i ∧
      (pilotStage S J m ρ).upper xs i ≤ pilotBound μ J ρ (i + 1)) ∧
    (∀ x : ℝ, (μ.map Subtype.val) (Set.Iic x) ≤
      (pilotStage S J m ρ).learnedLaw xs (Set.Iic x)) ∧
    zeroSelection ((pilotStage S J m ρ).learnedLaw xs) ρ (4 ^ J) ≤
      16777216 * EntropyTail.selection μ ρ (4 ^ J))).symm

theorem stage_pilot_oracle_eventually : StagePilotOracleEventuallyStatement := by
  intro μ _ ρ hρ hρ4
  obtain ⟨J₀, hJ₀⟩ := pilotOnset_eventually μ hρ (by linarith : ρ ≤ 1)
  refine ⟨max J₀ 1, le_max_right _ _, ?_⟩
  intro R _ q S J m ε hJ hm hε hmε
  exact stage_pilot_oracle R μ q S J m ρ ε hρ hρ4 ((le_max_right _ _).trans hJ)
    (hJ₀ J ((le_max_left _ _).trans hJ)) hm hε hmε

end ThresholdHC.StagePilotLaw
