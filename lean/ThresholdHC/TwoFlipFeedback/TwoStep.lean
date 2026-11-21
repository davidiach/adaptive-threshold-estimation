import ThresholdHC.CriticalEntropy.CreationPopulation

/-! Horizon-two observable prefix weights of an arbitrary countable-label
policy after integrating the iid hidden magnitudes and signs, for an arbitrary
magnitude law. Only the words that the policy can produce are evaluated. -/

noncomputable section
namespace ThresholdHC.TwoFlipFeedback
open MeasureTheory
open ThresholdHC ThresholdHC.Proofs ThresholdHC.Tier5 ThresholdHC.CriticalEntropy

/-- Probability that one fresh coin shows `b`. -/
def oneBit {D : Type} [MeasurableSpace D] (μ : Measure D) (d q : D → ℝ) (b : Bool) : ℝ :=
  ∫ x, q x * obsProb (1/2 + d x) (some b) + (1 - q x) * obsProb (1/2 - d x) (some b) ∂μ

/-- Probability that two flips of one fresh coin show `b` and then `b'`. -/
def twoBit {D : Type} [MeasurableSpace D] (μ : Measure D) (d q : D → ℝ) (b b' : Bool) : ℝ :=
  ∫ x, q x * (obsProb (1/2 + d x) (some b) * obsProb (1/2 + d x) (some b')) +
    (1 - q x) * (obsProb (1/2 - d x) (some b) * obsProb (1/2 - d x) (some b')) ∂μ

theorem histBefore_two_zero (w : Fin 2 → Option Bool) : histBefore w 0 = [] := by
  simp [histBefore]

theorem histBefore_two_one (w : Fin 2 → Option Bool) (b : Bool) (h : w 0 = some b) :
    histBefore w 1 = [b] := by
  simp [histBefore, List.ofFn_succ, h]

private theorem coinLike_two {m : ℕ} (P : List Bool → Option (Fin m)) (w : Fin 2 → Option Bool)
    (i : Fin m) (p : ℝ) :
    coinLike P w i p = (if P [] = some i then obsProb p (w 0) else 1) *
      (if P (histBefore w 1) = some i then obsProb p (w 1) else 1) := by
  rw [coinLike, Fin.prod_univ_two, histBefore_two_zero]

private theorem pathValidity_two {m : ℕ} (P : List Bool → Option (Fin m)) (w : Fin 2 → Option Bool) :
    pathValidity P w = (if P [] = none then (if w 0 = none then 1 else 0) else 1) *
      (if P (histBefore w 1) = none then (if w 1 = none then 1 else 0) else 1) := by
  rw [pathValidity, Fin.prod_univ_two, histBefore_two_zero]

private theorem weight_factor {D : Type} [MeasurableSpace D] (μ : Measure D) [IsProbabilityMeasure μ]
    (pol : List Bool → Option ℕ) (d q : D → ℝ) (hd : Measurable d) (hq : Measurable q)
    (w : Fin 2 → Option Bool) :
    creationPopulationWeight μ pol d q w =
      pathValidity (capPolicy (coinCap 2 pol) pol) w *
      ∏ i, ∫ x, q x * coinLike (capPolicy (coinCap 2 pol) pol) w i (1/2 + d x) +
        (1 - q x) * coinLike (capPolicy (coinCap 2 pol) pol) w i (1/2 - d x) ∂μ := by
  rw [creationPopulationWeight_eq_finite μ pol d q hd hq w, finite_population_factor]

private theorem cap_some {pol : List Bool → Option ℕ} {w : Fin 2 → Option Bool} {t : Fin 2}
    {c : ℕ} (h : pol (histBefore w t) = some c) :
    capPolicy (coinCap 2 pol) pol (histBefore w t) =
      some ⟨c, selected_lt_coinCap pol w t c h⟩ := by
  simp [capPolicy, h, selected_lt_coinCap pol w t c h]

private theorem cap_none {pol : List Bool → Option ℕ} {xs : List Bool} (h : pol xs = none) :
    capPolicy (coinCap 2 pol) pol xs = none := by
  simp [capPolicy, h]

/-- A policy that stops at once produces the empty word with probability one. -/
theorem weight_stop {D : Type} [MeasurableSpace D] (μ : Measure D) [IsProbabilityMeasure μ]
    (pol : List Bool → Option ℕ) (d q : D → ℝ) (hd : Measurable d) (hq : Measurable q)
    (h : pol [] = none) (w : Fin 2 → Option Bool) (h0 : w 0 = none) (h1 : w 1 = none) :
    creationPopulationWeight μ pol d q w = 1 := by
  have e1 : histBefore w 1 = [] := by simp [histBefore, List.ofFn_succ, h0]
  have hc : capPolicy (coinCap 2 pol) pol [] = none := cap_none h
  rw [weight_factor μ pol d q hd hq w, pathValidity_two]
  simp only [e1, hc, h0, h1, ite_true, mul_one, coinLike_two, reduceCtorEq, ite_false]
  simp

/-- One flip of the first coin and then a stop. -/
theorem weight_one {D : Type} [MeasurableSpace D] (μ : Measure D) [IsProbabilityMeasure μ]
    (pol : List Bool → Option ℕ) (d q : D → ℝ) (hd : Measurable d) (hq : Measurable q)
    (c : ℕ) (hc : pol [] = some c) (b : Bool) (hb : pol [b] = none)
    (w : Fin 2 → Option Bool) (h0 : w 0 = some b) (h1 : w 1 = none) :
    creationPopulationWeight μ pol d q w = oneBit μ d q b := by
  have e1 := histBefore_two_one w b h0
  have hc0 : pol (histBefore w 0) = some c := by rw [histBefore_two_zero]; exact hc
  have p0 := cap_some hc0
  rw [histBefore_two_zero] at p0
  have p1 : capPolicy (coinCap 2 pol) pol [b] = none := cap_none hb
  rw [weight_factor μ pol d q hd hq w, pathValidity_two]
  simp only [e1, p0, p1, h0, h1, reduceCtorEq, ite_false, ite_true, mul_one, one_mul, coinLike_two]
  rw [Fintype.prod_eq_single ⟨c, selected_lt_coinCap pol w 0 c hc0⟩]
  · simp only [ite_true]
    rfl
  · intro i hi
    have hne : (some ⟨c, selected_lt_coinCap pol w 0 c hc0⟩ : Option (Fin (coinCap 2 pol))) ≠ some i :=
      fun e => hi (Option.some_injective _ e).symm
    simp only [hne, ite_false]
    simp

/-- Two flips of the same coin. -/
theorem weight_same {D : Type} [MeasurableSpace D] (μ : Measure D) [IsProbabilityMeasure μ]
    (pol : List Bool → Option ℕ) (d q : D → ℝ) (hd : Measurable d) (hq : Measurable q)
    (c : ℕ) (hc : pol [] = some c) (b : Bool) (hb : pol [b] = some c) (b' : Bool)
    (w : Fin 2 → Option Bool) (h0 : w 0 = some b) (h1 : w 1 = some b') :
    creationPopulationWeight μ pol d q w = twoBit μ d q b b' := by
  have e1 := histBefore_two_one w b h0
  have hc0 : pol (histBefore w 0) = some c := by rw [histBefore_two_zero]; exact hc
  have hc1 : pol (histBefore w 1) = some c := by rw [e1]; exact hb
  have p0 := cap_some hc0
  rw [histBefore_two_zero] at p0
  have p1 := cap_some hc1
  rw [e1] at p1
  have hlt : selected_lt_coinCap pol w 1 c hc1 = selected_lt_coinCap pol w 0 c hc0 := rfl
  rw [weight_factor μ pol d q hd hq w, pathValidity_two]
  simp only [e1, p0, p1, h0, h1, reduceCtorEq, ite_false, mul_one, one_mul, coinLike_two]
  rw [Fintype.prod_eq_single ⟨c, selected_lt_coinCap pol w 0 c hc0⟩]
  · simp only [ite_true]
    rfl
  · intro i hi
    have hne : (some ⟨c, selected_lt_coinCap pol w 0 c hc0⟩ : Option (Fin (coinCap 2 pol))) ≠ some i :=
      fun e => hi (Option.some_injective _ e).symm
    simp only [hne, ite_false]
    simp

/-- A flip of the first coin and then a flip of a different coin. -/
theorem weight_fresh {D : Type} [MeasurableSpace D] (μ : Measure D) [IsProbabilityMeasure μ]
    (pol : List Bool → Option ℕ) (d q : D → ℝ) (hd : Measurable d) (hq : Measurable q)
    (c : ℕ) (hc : pol [] = some c) (b : Bool) (c' : ℕ) (hb : pol [b] = some c') (hne : c' ≠ c)
    (b' : Bool) (w : Fin 2 → Option Bool) (h0 : w 0 = some b) (h1 : w 1 = some b') :
    creationPopulationWeight μ pol d q w = oneBit μ d q b * oneBit μ d q b' := by
  have e1 := histBefore_two_one w b h0
  have hc0 : pol (histBefore w 0) = some c := by rw [histBefore_two_zero]; exact hc
  have hc1 : pol (histBefore w 1) = some c' := by rw [e1]; exact hb
  have p0 := cap_some hc0
  rw [histBefore_two_zero] at p0
  have p1 := cap_some hc1
  rw [e1] at p1
  set j : Fin (coinCap 2 pol) := ⟨c, selected_lt_coinCap pol w 0 c hc0⟩ with hj
  set j' : Fin (coinCap 2 pol) := ⟨c', selected_lt_coinCap pol w 1 c' hc1⟩ with hj'
  have hjj : j ≠ j' := fun e => hne (congrArg Fin.val e).symm
  rw [weight_factor μ pol d q hd hq w, pathValidity_two]
  simp only [e1, p0, p1, h0, h1, reduceCtorEq, ite_false, mul_one, one_mul, coinLike_two]
  rw [Fintype.prod_eq_mul j j' hjj]
  · have a1 : (some j' : Option (Fin (coinCap 2 pol))) ≠ some j := fun e => hjj (Option.some_injective _ e).symm
    have a2 : (some j : Option (Fin (coinCap 2 pol))) ≠ some j' := fun e => hjj (Option.some_injective _ e)
    simp only [a1, a2, ite_true, ite_false, mul_one, one_mul]
    rfl
  · intro i hi
    have n1 : (some j : Option (Fin (coinCap 2 pol))) ≠ some i := fun e => hi.1 (Option.some_injective _ e).symm
    have n2 : (some j' : Option (Fin (coinCap 2 pol))) ≠ some i := fun e => hi.2 (Option.some_injective _ e).symm
    simp only [n1, n2, ite_false]
    simp

end ThresholdHC.TwoFlipFeedback
