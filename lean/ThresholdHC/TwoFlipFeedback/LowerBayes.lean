import ThresholdHC.TwoFlipFeedback.Risk

/-! The two-point Bayes bound for one seed. The null is `q ≡ 0` and the hard
alternative is `(q(1/4), q(1/8)) = (0, 1/2)`, with prior weight
`π = 1074499095/2^31` on the alternative (`full_class-body.tex`). For every
policy of the noninteractive normal form and every terminal word function the
`π`-weighted squared error is at least `1547585/10^8`. The six shapes are a
stop, one flip, a revisit after a tail only, a revisit after a head only, two
flips of one coin, and two fresh coins; each is bounded directly, without the
paper's step that completes early stops. -/

noncomputable section
namespace ThresholdHC.TwoFlipFeedback
open MeasureTheory
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.CriticalEntropy

/-- Prior weight of the hard alternative. -/
def designPrior : ℝ := 1074499095/2147483648

/-- The internal lower constant, above `15475/10^6`. -/
def lowerValue : ℝ := 1547585/100000000

/-- Bayes loss of one word with null weight `u`, alternative weight `v` and estimate `X`. -/
def wordLoss (u v X : ℝ) : ℝ := (1 - designPrior) * u * X^2 + designPrior * v * (X - 1/4)^2

/-- Minimal Bayes loss of one word. -/
def bayesWord (u v : ℝ) : ℝ :=
  ((1 - designPrior) * u) * (designPrior * v) / (16 * ((1 - designPrior) * u + designPrior * v))

theorem word_bound (a b X : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * b / (16 * (a + b)) ≤ a * X^2 + b * (X - 1/4)^2 := by
  rcases (add_nonneg ha hb).eq_or_lt with h | h
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    subst ha0 hb0
    simp
  · rw [div_le_iff₀ (by linarith)]
    nlinarith [sq_nonneg ((a + b) * X - b/4)]

theorem wordLoss_ge (u v X : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) : bayesWord u v ≤ wordLoss u v X := by
  have hp : 0 ≤ designPrior := by norm_num [designPrior]
  have hq : 0 ≤ 1 - designPrior := by norm_num [designPrior]
  have h := word_bound ((1 - designPrior) * u) (designPrior * v) X (mul_nonneg hq hu)
    (mul_nonneg hp hv)
  unfold bayesWord wordLoss
  linarith

theorem wordLoss_nonneg (u v X : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) : 0 ≤ wordLoss u v X := by
  have hp : 0 ≤ designPrior := by norm_num [designPrior]
  have hq : 0 ≤ 1 - designPrior := by norm_num [designPrior]
  unfold wordLoss
  exact add_nonneg (mul_nonneg (mul_nonneg hq hu) (sq_nonneg _))
    (mul_nonneg (mul_nonneg hp hv) (sq_nonneg _))

/-- One-flip head and tail probabilities under the null and the alternative. -/
def oneNull (b : Bool) : ℝ := if b then 5/16 else 11/16
def oneHard (b : Bool) : ℝ := if b then 3/8 else 5/8

/-- Same-coin two-flip probabilities under the null and the alternative. -/
def twoNull (b b' : Bool) : ℝ :=
  if b then (if b' then 13/128 else 27/128) else (if b' then 27/128 else 61/128)
def twoHard (b b' : Bool) : ℝ :=
  if b then (if b' then 21/128 else 27/128) else (if b' then 27/128 else 53/128)

theorem oneBit_null (b : Bool) : oneBit twoGapLaw gapValue nullLaw.val b = oneNull b := by
  cases b
  · rw [oneBit_false, nullLaw_drift]; norm_num [oneNull]
  · rw [oneBit_true, nullLaw_drift]; norm_num [oneNull]

theorem oneBit_hard (b : Bool) : oneBit twoGapLaw gapValue hardLaw.val b = oneHard b := by
  cases b
  · rw [oneBit_false, hardLaw_drift]; norm_num [oneHard]
  · rw [oneBit_true, hardLaw_drift]; norm_num [oneHard]

theorem twoBit_null (b b' : Bool) : twoBit twoGapLaw gapValue nullLaw.val b b' = twoNull b b' := by
  cases b <;> cases b'
  · rw [twoBit_ff, nullLaw_drift]; norm_num [twoNull]
  · rw [twoBit_ft]; norm_num [twoNull]
  · rw [twoBit_tf]; norm_num [twoNull]
  · rw [twoBit_tt, nullLaw_drift]; norm_num [twoNull]

theorem twoBit_hard (b b' : Bool) : twoBit twoGapLaw gapValue hardLaw.val b b' = twoHard b b' := by
  cases b <;> cases b'
  · rw [twoBit_ff, hardLaw_drift]; norm_num [twoHard]
  · rw [twoBit_ft]; norm_num [twoHard]
  · rw [twoBit_tf]; norm_num [twoHard]
  · rw [twoBit_tt, hardLaw_drift]; norm_num [twoHard]

/-- Bayes value of a branch after the first answer `b`: stop, revisit, or fresh coin. -/
def stopBranch (b : Bool) : ℝ := bayesWord (oneNull b) (oneHard b)
def revisitBranch (b : Bool) : ℝ :=
  bayesWord (twoNull b false) (twoHard b false) + bayesWord (twoNull b true) (twoHard b true)
def freshBranch (b : Bool) : ℝ :=
  bayesWord (oneNull b * oneNull false) (oneHard b * oneHard false) +
    bayesWord (oneNull b * oneNull true) (oneHard b * oneHard true)

def branchValue (c : ℕ) (b : Bool) (o : Option ℕ) : ℝ :=
  match o with
  | none => stopBranch b
  | some c' => if c' = c then revisitBranch b else freshBranch b

/-- Bayes loss of the word `w` for the policy `pol` and the terminal function `X`. -/
def policyLoss (pol : List Bool → Option ℕ) (X : Prefix 2 → ℝ) (w : Prefix 2) : ℝ :=
  wordLoss (creationPopulationWeight twoGapLaw pol gapValue nullLaw.val w)
    (creationPopulationWeight twoGapLaw pol gapValue hardLaw.val w) (X w)

private theorem weight_nonneg (pol : List Bool → Option ℕ) (q : SignLaw) (w : Prefix 2) :
    0 ≤ creationPopulationWeight twoGapLaw pol gapValue q.val w :=
  (creationPopulationWeight_total twoGapLaw pol gapValue q.val measurable_subtype_coe q.property.1
    (fun d : Gap => ⟨d.property.1.le, d.property.2⟩) q.property.2).1 w

theorem policyLoss_nonneg (pol : List Bool → Option ℕ) (X : Prefix 2 → ℝ) (w : Prefix 2) :
    0 ≤ policyLoss pol X w :=
  wordLoss_nonneg _ _ _ (weight_nonneg pol nullLaw w) (weight_nonneg pol hardLaw w)

private theorem hd : Measurable gapValue := measurable_subtype_coe

theorem branch_bound (pol : List Bool → Option ℕ) (X : Prefix 2 → ℝ) (c : ℕ)
    (hc : pol [] = some c) (b : Bool) :
    branchValue c b (pol [b]) ≤ policyLoss pol X ![some b, none] +
      policyLoss pol X ![some b, some false] + policyLoss pol X ![some b, some true] := by
  have n1 := policyLoss_nonneg pol X ![some b, none]
  have n2 := policyLoss_nonneg pol X ![some b, some false]
  have n3 := policyLoss_nonneg pol X ![some b, some true]
  cases hb : pol [b] with
  | none =>
    have h := wordLoss_ge (oneNull b) (oneHard b) (X ![some b, none])
      (by cases b <;> norm_num [oneNull]) (by cases b <;> norm_num [oneHard])
    have e0 := weight_one twoGapLaw pol gapValue nullLaw.val hd nullLaw.property.1 c hc b hb
      ![some b, none] rfl rfl
    have e1 := weight_one twoGapLaw pol gapValue hardLaw.val hd hardLaw.property.1 c hc b hb
      ![some b, none] rfl rfl
    rw [oneBit_null] at e0
    rw [oneBit_hard] at e1
    have : policyLoss pol X ![some b, none] = wordLoss (oneNull b) (oneHard b) (X ![some b, none]) := by
      rw [policyLoss, e0, e1]
    simp only [branchValue, stopBranch]
    linarith
  | some c' =>
    by_cases hcc : c' = c
    · subst hcc
      have e (q : SignLaw) (b' : Bool) := weight_same twoGapLaw pol gapValue q.val hd q.property.1
        c' hc b hb b' ![some b, some b'] rfl rfl
      have l2 : policyLoss pol X ![some b, some false] =
          wordLoss (twoNull b false) (twoHard b false) (X ![some b, some false]) := by
        rw [policyLoss, e nullLaw false, e hardLaw false, twoBit_null, twoBit_hard]
      have l3 : policyLoss pol X ![some b, some true] =
          wordLoss (twoNull b true) (twoHard b true) (X ![some b, some true]) := by
        rw [policyLoss, e nullLaw true, e hardLaw true, twoBit_null, twoBit_hard]
      have h2 := wordLoss_ge (twoNull b false) (twoHard b false) (X ![some b, some false])
        (by cases b <;> norm_num [twoNull]) (by cases b <;> norm_num [twoHard])
      have h3 := wordLoss_ge (twoNull b true) (twoHard b true) (X ![some b, some true])
        (by cases b <;> norm_num [twoNull]) (by cases b <;> norm_num [twoHard])
      simp only [branchValue, revisitBranch, ite_true]
      linarith
    · have e (q : SignLaw) (b' : Bool) := weight_fresh twoGapLaw pol gapValue q.val hd q.property.1
        c hc b c' hb hcc b' ![some b, some b'] rfl rfl
      have l2 : policyLoss pol X ![some b, some false] =
          wordLoss (oneNull b * oneNull false) (oneHard b * oneHard false) (X ![some b, some false]) := by
        rw [policyLoss, e nullLaw false, e hardLaw false, oneBit_null, oneBit_null, oneBit_hard,
          oneBit_hard]
      have l3 : policyLoss pol X ![some b, some true] =
          wordLoss (oneNull b * oneNull true) (oneHard b * oneHard true) (X ![some b, some true]) := by
        rw [policyLoss, e nullLaw true, e hardLaw true, oneBit_null, oneBit_null, oneBit_hard,
          oneBit_hard]
      have h2 := wordLoss_ge (oneNull b * oneNull false) (oneHard b * oneHard false)
        (X ![some b, some false]) (by cases b <;> norm_num [oneNull]) (by cases b <;> norm_num [oneHard])
      have h3 := wordLoss_ge (oneNull b * oneNull true) (oneHard b * oneHard true)
        (X ![some b, some true]) (by cases b <;> norm_num [oneNull]) (by cases b <;> norm_num [oneHard])
      simp only [branchValue, freshBranch, hcc, ite_false]
      linarith

theorem stop_value : lowerValue ≤ bayesWord 1 1 := by
  norm_num [lowerValue, bayesWord, designPrior]

theorem one_value : lowerValue ≤ stopBranch false + stopBranch true := by
  norm_num [lowerValue, stopBranch, bayesWord, designPrior, oneNull, oneHard]

theorem revisit_tail_value : lowerValue ≤ revisitBranch false + stopBranch true := by
  norm_num [lowerValue, stopBranch, revisitBranch, bayesWord, designPrior, oneNull, oneHard,
    twoNull, twoHard]

theorem revisit_head_value : lowerValue ≤ stopBranch false + revisitBranch true := by
  norm_num [lowerValue, stopBranch, revisitBranch, bayesWord, designPrior, oneNull, oneHard,
    twoNull, twoHard]

theorem same_value : lowerValue ≤ revisitBranch false + revisitBranch true := by
  norm_num [lowerValue, revisitBranch, bayesWord, designPrior, twoNull, twoHard]

theorem fresh_value : lowerValue ≤ freshBranch false + freshBranch true := by
  norm_num [lowerValue, freshBranch, bayesWord, designPrior, oneNull, oneHard]

/-- The per-seed Bayes bound for every policy of the noninteractive normal form. -/
theorem policy_bayes (pol : List Bool → Option ℕ)
    (hpol : ∀ c : ℕ, pol [] = some c →
      (∀ b : Bool, pol [b] = none ∨ pol [b] = some c) ∨
      ((∀ b : Bool, pol [b] ≠ some c) ∧ (pol [false]).isSome = (pol [true]).isSome))
    (X : Prefix 2 → ℝ) : lowerValue ≤ ∑ w, policyLoss pol X w := by
  rw [sum_words]
  have n1 := policyLoss_nonneg pol X ![none, none]
  have n2 := policyLoss_nonneg pol X ![none, some false]
  have n3 := policyLoss_nonneg pol X ![none, some true]
  cases h0 : pol [] with
  | none =>
    have e (q : SignLaw) := weight_stop twoGapLaw pol gapValue q.val hd q.property.1 h0
      ![none, none] rfl rfl
    have l1 : policyLoss pol X ![none, none] = wordLoss 1 1 (X ![none, none]) := by
      rw [policyLoss, e nullLaw, e hardLaw]
    have h1 := wordLoss_ge 1 1 (X ![none, none]) zero_le_one zero_le_one
    have := stop_value
    have m1 := policyLoss_nonneg pol X ![some false, none]
    have m2 := policyLoss_nonneg pol X ![some false, some false]
    have m3 := policyLoss_nonneg pol X ![some false, some true]
    have m4 := policyLoss_nonneg pol X ![some true, none]
    have m5 := policyLoss_nonneg pol X ![some true, some false]
    have m6 := policyLoss_nonneg pol X ![some true, some true]
    linarith
  | some c =>
    have bF := branch_bound pol X c h0 false
    have bT := branch_bound pol X c h0 true
    have key : lowerValue ≤ branchValue c false (pol [false]) + branchValue c true (pol [true]) := by
      rcases hpol c h0 with ha | ⟨hb, hs⟩
      · rcases ha false with hF | hF <;> rcases ha true with hT | hT <;>
          simp only [hF, hT, branchValue, ite_true]
        · exact one_value
        · exact revisit_head_value
        · exact revisit_tail_value
        · exact same_value
      · cases hF : pol [false] with
        | none =>
          cases hT : pol [true] with
          | none => simpa only [branchValue] using one_value
          | some c2 => simp [hF, hT] at hs
        | some c1 =>
          cases hT : pol [true] with
          | none => simp [hF, hT] at hs
          | some c2 =>
            have h1 : c1 ≠ c := fun e => hb false (by rw [hF, e])
            have h2 : c2 ≠ c := fun e => hb true (by rw [hT, e])
            simp only [branchValue, h1, h2, ite_false]
            exact fresh_value
    linarith

end ThresholdHC.TwoFlipFeedback
