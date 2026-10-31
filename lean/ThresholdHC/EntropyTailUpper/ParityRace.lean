import ThresholdHC.EntropyTailUpper.BoundedSearch
import ThresholdHC.EntropyTailUpper.Ordinary
import ThresholdHC.EntropyTailUpper.PrefixCrossing
import Mathlib.Probability.Independence.InfinitePi

/-! An actual finite race between a prefix bank and the ordinary classifier.
The two competitors see alternating observations of the same coin. The
uncapped bank need not terminate: the ordinary classifier supplies the cap. -/

noncomputable section
open MeasureTheory Set

namespace ThresholdHC.EntropyTailUpper
open ThresholdHC.Tier2 ThresholdHC.CriticalEntropy ThresholdHC.BlindUpper

def parityTape (b : Fin 2) (ω : ℕ → Bool) (k : ℕ) : Bool := ω (2*k+b)

theorem measurable_parityTape (b : Fin 2) : Measurable (parityTape b) := by
  unfold parityTape
  fun_prop

theorem parityTape_measurePreserving (b : Fin 2) (p : unitInterval) :
    MeasurePreserving (parityTape b) (tapeMeasure p) (tapeMeasure p) := by
  refine ⟨measurable_parityTape b, ?_⟩
  exact Measure.map_infinitePi_infinitePi_of_inj (by
    intro i j h
    change 2*i+b.val = 2*j+b.val at h
    omega)

theorem parityTape_prefix_ext (b : Fin 2) {n : ℕ} {ω ω' : ℕ → Bool}
    (he : tapePrefix (2*n) ω = tapePrefix (2*n) ω') :
    tapePrefix n (parityTape b ω) = tapePrefix n (parityTape b ω') := by
  funext i
  exact congrFun he ⟨2*i.val+b.val, by omega⟩

theorem classifierStop_by_prefix (L n : ℕ) {ω ω' : ℕ → Bool}
    (he : tapePrefix n ω = tapePrefix n ω') :
    classifierStop L ω ≤ n ↔ classifierStop L ω' ≤ n := by
  constructor
  · intro h
    rw [(classifier_prefix_ext L ω ω' (prefix_eq_restrict he h)).1]
    exact h
  · intro h
    rw [(classifier_prefix_ext L ω' ω (prefix_eq_restrict he.symm h)).1]
    exact h

abbrev PrefixTest := (n : ℕ) → (Fin n → Bool) → Prop

def raceHit (neg pos : PrefixTest) (L : ℕ) (ω : ℕ → Bool) (n : ℕ) : Prop :=
  neg n (tapePrefix n (parityTape 0 ω)) ∨ pos n (tapePrefix n (parityTape 0 ω)) ∨
    classifierStop L (parityTape 1 ω) ≤ n

def raceRounds (neg pos : PrefixTest) (L : ℕ) (ω : ℕ → Bool) : ℕ :=
  boundedFirst (raceHit neg pos L ω) (2^L)

def raceCost (neg pos : PrefixTest) (L : ℕ) (ω : ℕ → Bool) : ℕ :=
  2 * raceRounds neg pos L ω

def raceValue (neg pos : PrefixTest) (L : ℕ) (ω : ℕ → Bool) : ℝ := by
  classical
  let n := raceRounds neg pos L ω
  exact if neg n (tapePrefix n (parityTape 0 ω)) then 0
    else if pos n (tapePrefix n (parityTape 0 ω)) then 1
    else classifierValue L (parityTape 1 ω)

theorem raceRounds_le (neg pos : PrefixTest) (L : ℕ) (ω : ℕ → Bool) :
    raceRounds neg pos L ω ≤ 2^L := (boundedFirst_spec _ _).1

theorem raceRounds_hit (neg pos : PrefixTest) (L : ℕ) (ω : ℕ → Bool) :
    raceHit neg pos L ω (raceRounds neg pos L ω) := by
  rcases (boundedFirst_spec (raceHit neg pos L ω) (2^L)).2 with h | h
  · exact h
  · apply Or.inr; apply Or.inr
    change classifierStop L (parityTape 1 ω) ≤ boundedFirst _ _
    rw [h]
    exact classifierStop_le L (parityTape 1 ω)

theorem raceRounds_le_ordinary (neg pos : PrefixTest) (L : ℕ) (ω : ℕ → Bool) :
    raceRounds neg pos L ω ≤ classifierStop L (parityTape 1 ω) :=
  boundedFirst_le_of_hit _ _ _ (Or.inr (Or.inr le_rfl))

theorem raceRounds_le_bank (neg pos : PrefixTest) (L n : ℕ) (ω : ℕ → Bool)
    (hh : neg n (tapePrefix n (parityTape 0 ω)) ∨ pos n (tapePrefix n (parityTape 0 ω))) :
    raceRounds neg pos L ω ≤ n :=
  boundedFirst_le_of_hit _ _ _ (hh.elim Or.inl (fun h => Or.inr (Or.inl h)))

theorem raceHit_prefix_ext (neg pos : PrefixTest) (L n : ℕ) {ω ω' : ℕ → Bool}
    (he : tapePrefix (2*n) ω = tapePrefix (2*n) ω') :
    raceHit neg pos L ω n ↔ raceHit neg pos L ω' n := by
  unfold raceHit
  rw [parityTape_prefix_ext 0 he, classifierStop_by_prefix L n (parityTape_prefix_ext 1 he)]

theorem raceRounds_prefix_ext (neg pos : PrefixTest) (L : ℕ) (ω ω' : ℕ → Bool)
    (he : tapePrefix (raceCost neg pos L ω) ω = tapePrefix (raceCost neg pos L ω) ω') :
    raceRounds neg pos L ω' = raceRounds neg pos L ω := by
  apply (boundedFirst_congr_until _ _ _ _).symm
  intro n hn
  change n ≤ raceRounds neg pos L ω at hn
  exact raceHit_prefix_ext neg pos L n (prefix_eq_restrict he (by unfold raceCost; omega))

theorem race_prefix_ext (neg pos : PrefixTest) (L : ℕ) (ω ω' : ℕ → Bool)
    (he : tapePrefix (raceCost neg pos L ω) ω = tapePrefix (raceCost neg pos L ω) ω') :
    raceCost neg pos L ω' = raceCost neg pos L ω ∧ raceValue neg pos L ω' = raceValue neg pos L ω := by
  have hr := raceRounds_prefix_ext neg pos L ω ω' he
  constructor
  · exact congrArg (2 * ·) hr
  · unfold raceValue
    dsimp only
    rw [hr, parityTape_prefix_ext 0 he]
    split_ifs with hn hp
    · rfl
    · rfl
    · have ho : classifierStop L (parityTape 1 ω) ≤ raceRounds neg pos L ω := by
        rcases raceRounds_hit neg pos L ω with h | h | h
        · exact False.elim (hn ((parityTape_prefix_ext 0 he) ▸ h))
        · exact False.elim (hp ((parityTape_prefix_ext 0 he) ▸ h))
        · exact h
      exact (classifier_prefix_ext L _ _ (prefix_eq_restrict (parityTape_prefix_ext 1 he) ho)).2

theorem raceCost_le (neg pos : PrefixTest) (L : ℕ) (ω : ℕ → Bool) :
    raceCost neg pos L ω ≤ 2*(2^L) := Nat.mul_le_mul_left 2 (raceRounds_le neg pos L ω)

theorem measurable_raceCost (neg pos : PrefixTest) (L : ℕ) :
    Measurable (raceCost neg pos L) := by
  have he : raceCost neg pos L =
      (fun w => raceCost neg pos L (completePrefix (2*(2^L)) w)) ∘ tapePrefix (2*(2^L)) := by
    funext ω
    exact ((race_prefix_ext neg pos L ω _
      (prefix_eq_restrict (tapePrefix_completePrefix _ _).symm (raceCost_le neg pos L ω))).1).symm
  rw [he]
  exact (measurable_of_countable _).comp (measurable_prefix _)

theorem measurable_raceValue (neg pos : PrefixTest) (L : ℕ) :
    Measurable (raceValue neg pos L) := by
  have he : raceValue neg pos L =
      (fun w => raceValue neg pos L (completePrefix (2*(2^L)) w)) ∘ tapePrefix (2*(2^L)) := by
    funext ω
    exact ((race_prefix_ext neg pos L ω _
      (prefix_eq_restrict (tapePrefix_completePrefix _ _).symm (raceCost_le neg pos L ω))).2).symm
  rw [he]
  exact (measurable_of_countable _).comp (measurable_prefix _)

def raceProcedure (neg pos : PrefixTest) (L : ℕ) : StoppedProcedure Unit ℝ :=
  finiteStoppedProcedure (fun z => raceCost neg pos L z.2) (fun z => raceValue neg pos L z.2)
    ((measurable_raceCost neg pos L).comp measurable_snd)
    ((measurable_raceValue neg pos L).comp measurable_snd)
    (fun _ ω ω' he => race_prefix_ext neg pos L ω ω' he)

theorem raceValue_zero_or_one (neg pos : PrefixTest) (L : ℕ) (ω : ℕ → Bool) :
    raceValue neg pos L ω = 0 ∨ raceValue neg pos L ω = 1 := by
  unfold raceValue
  dsimp only
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Model.decision_zero_or_one _ L

theorem race_error_positive_subset (neg pos : PrefixTest) (L : ℕ) :
    {ω | raceValue neg pos L ω ≠ 1} ⊆
      parityTape 0 ⁻¹' everPrefixHit neg ∪ parityTape 1 ⁻¹' {ω | classifierValue L ω ≠ 1} := by
  intro ω h
  change raceValue neg pos L ω ≠ 1 at h
  unfold raceValue at h
  dsimp only at h
  split_ifs at h with hn hp
  · exact Or.inl ⟨_, hn⟩
  · exact False.elim (h rfl)
  · exact Or.inr h

theorem race_error_negative_subset (neg pos : PrefixTest) (L : ℕ) :
    {ω | raceValue neg pos L ω ≠ 0} ⊆
      parityTape 0 ⁻¹' everPrefixHit pos ∪ parityTape 1 ⁻¹' {ω | classifierValue L ω ≠ 0} := by
  intro ω h
  change raceValue neg pos L ω ≠ 0 at h
  unfold raceValue at h
  dsimp only at h
  split_ifs at h with hn hp
  · exact False.elim (h rfl)
  · exact Or.inl ⟨_, hp⟩
  · exact Or.inr h

end ThresholdHC.EntropyTailUpper
