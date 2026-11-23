import ThresholdHC.SharpRMS.GridArithmetic

/-! Integer upper sums on the intermediate bias window: the bound checked on
each bias interval, the chain of adjacent intervals and its 140 endpoints,
and a faster kernel evaluation of the bound. The closed comparisons are in
the WindowPart modules. -/
namespace ThresholdHC.SharpRMS.Window

/-- After multiplying by (hi/lo)^2, the scaled upper sum is at most 2/3. -/
def gridBound (lo hi : Nat) : Prop :=
  0 < lo ∧ lo ≤ hi ∧ 3*hi^2*upperSum hi ≤ 2*lo^2*bins*scale

instance decidableGridBound (lo hi : Nat) : Decidable (gridBound lo hi) := inferInstanceAs
  (Decidable (0 < lo ∧ lo ≤ hi ∧ 3*hi^2*upperSum hi ≤ 2*lo^2*bins*scale))

def gridChain (lo : Nat) : List Nat → Prop
  | [] => True
  | hi :: rest => gridBound lo hi ∧ gridChain hi rest

def endpoints : List Nat := [
    16407, 16430, 16453, 16476, 16499, 16522, 16545, 16568, 16591, 16614, 16637, 16660,
    16683, 16706, 16729, 16752, 16775, 16798, 16821, 16844, 16867, 16890, 16913, 16936,
    16959, 16982, 17028, 17074, 17120, 17166, 17212, 17258, 17304, 17350, 17396, 17442,
    17488, 17534, 17580, 17626, 17672, 17718, 17764, 17810, 17856, 17902, 17948, 17994,
    18040, 18086, 18132, 18224, 18316, 18408, 18500, 18592, 18684, 18776, 18868, 18960,
    19052, 19144, 19236, 19328, 19420, 19512, 19604, 19696, 19788, 19880, 19972, 20064,
    20156, 20248, 20432, 20616, 20800, 20984, 21168, 21352, 21536, 21720, 21904, 22088,
    22272, 22456, 22640, 22824, 23008, 23192, 23376, 23560, 23744, 23928, 24112, 24480,
    24848, 25216, 25584, 25952, 26320, 26688, 27056, 27424, 27792, 28160, 28528, 28896,
    29264, 29632, 30000, 30368, 30736, 31104, 31472, 31840, 32208, 32576, 32944, 33312,
    33680, 34048, 34416, 34784, 35152, 35520, 35888, 36256, 36624, 36992, 37360, 37728,
    38096, 38464, 38832, 39200, 39384, 39568, 39752, 39936]

/-! ### Kernel evaluation

The kernel reduces `upperSum` through the type-class instances of `*`, `^`,
`max` and `min` and through the compiled structural recursion of
`List.foldl`. The definitions below compute the same sum with the primitive
`Nat` operations, which the kernel evaluates on literals directly, and with
the recursors `Nat.rec`, `List.rec` and `Bool.rec`. They read the same
barrier list. `fastSum_eq` proves `fastSum u = upperSum u` for every `u`,
and `gridBound_of_fastBound` turns a reduced comparison into `gridBound`. -/

/-- `max a b`, decided by one `Nat.ble`. -/
def fastMax (a b : Nat) : Nat := Bool.rec (motive := fun _ => Nat) a b (Nat.ble a b)

/-- `min a b`, decided by one `Nat.ble`. -/
def fastMin (a b : Nat) : Nat := Bool.rec (motive := fun _ => Nat) b a (Nat.ble a b)

/-- `roundUp` with the primitive operations. -/
def fastRoundUp (a b : Nat) : Nat := Nat.div (Nat.sub (Nat.add a b) 1) b

/-- `weight` with the primitive operations. -/
def fastWeight (j : Nat) : Nat := Nat.sub (Nat.pow bins 2) (Nat.pow (Nat.sub j 1) 2)

/-- `signHeight` with the primitive operations. -/
def fastSign (j u w : Nat) : Nat :=
  fastRoundUp (Nat.mul (Nat.mul scale (fastWeight j)) (Nat.pow w 2))
    (Nat.mul (Nat.pow bins 2) (Nat.pow u 2))

/-- `roundedExit` with the primitive operations. -/
def fastExit (j u w : Nat) (b : Barrier) : Nat :=
  let den := Nat.mul (Nat.mul (Nat.mul (Nat.mul bins u)
      (Nat.sub (Nat.mul bins b.denominator) (Nat.mul j b.numerator)))
      (Nat.add (Nat.mul bins w) (Nat.mul j u)))
    (Nat.sub (Nat.mul (Nat.mul bins b.slopeDenominator) (Nat.add b.height 1))
      (Nat.mul j b.slopeNumerator))
  Bool.rec (motive := fun _ => Nat)
    (fastRoundUp (Nat.mul b.top (Nat.pow (fastWeight j) 2)) den) (fastSign j u w) (Nat.beq den 0)

/-- `maximumFor`, started from `best`, by recursion on the barrier list. -/
def fastMaximum (j u w : Nat) (prices : List Barrier) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun best => best)
    (fun b _ rest best => rest (fastMax best (fastExit j u w b))) prices

/-- The first `n` rectangles of `upperSum`, by recursion on `n`. -/
def fastPartial (u : Nat) (prices : List Barrier) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun k acc => Nat.add acc (fastMin (fastMaximum (k+1) u biasDenominator prices 0)
      (fastSign (k+1) u biasDenominator))) n

/-- `upperSum` with the primitive operations and recursors. -/
def fastSum (u : Nat) : Nat := fastPartial u (barrierList u biasDenominator) bins

/-- `gridBound` as one Boolean, with the primitive operations. -/
def fastBound (lo hi : Nat) : Bool :=
  Nat.ble 1 lo && Nat.ble lo hi &&
    Nat.ble (Nat.mul (Nat.mul 3 (Nat.pow hi 2)) (fastSum hi))
      (Nat.mul (Nat.mul (Nat.mul 2 (Nat.pow lo 2)) bins) scale)

theorem fastMax_eq (a b : Nat) : fastMax a b = max a b := by
  show Bool.rec (motive := fun _ => Nat) a b (Nat.ble a b) = if a ≤ b then b else a
  cases h : Nat.ble a b with
  | false => exact (ite_eq_right (Nat.not_le_of_not_ble_eq_true (Bool.ne_true_of_eq_false h))).symm
  | true => exact (ite_eq_left (Nat.le_of_ble_eq_true h)).symm

theorem fastMin_eq (a b : Nat) : fastMin a b = min a b := by
  show Bool.rec (motive := fun _ => Nat) b a (Nat.ble a b) = if a ≤ b then a else b
  cases h : Nat.ble a b with
  | false => exact (ite_eq_right (Nat.not_le_of_not_ble_eq_true (Bool.ne_true_of_eq_false h))).symm
  | true => exact (ite_eq_left (Nat.le_of_ble_eq_true h)).symm

theorem fastSign_eq (j u w : Nat) : fastSign j u w = signHeight j u w := rfl

theorem fastExit_eq (j u w : Nat) (b : Barrier) : fastExit j u w b = roundedExit j u w b := by
  have step (den x y : Nat) :
      Bool.rec (motive := fun _ => Nat) x y (Nat.beq den 0) = if den = 0 then y else x := by
    cases h : Nat.beq den 0 with
    | false => exact (ite_eq_right (Nat.ne_of_beq_eq_false h)).symm
    | true => exact (ite_eq_left (Nat.eq_of_beq_eq_true h)).symm
  exact step _ _ _

theorem fastMaximum_eq (j u w : Nat) (prices : List Barrier) (best : Nat) :
    fastMaximum j u w prices best =
      prices.foldl (fun best b => max best (roundedExit j u w b)) best := by
  induction prices generalizing best with
  | nil => rfl
  | cons b bs ih =>
    show fastMaximum j u w bs (fastMax best (fastExit j u w b)) = _
    rw [ih, fastMax_eq, fastExit_eq]
    rfl

theorem fastPartial_eq (u : Nat) (prices : List Barrier) (n : Nat) :
    fastPartial u prices n = (List.range n).foldl (fun acc i => acc +
      min (maximumFor (i+1) u biasDenominator prices) (signHeight (i+1) u biasDenominator)) 0 := by
  -- `List.foldl_append` would add `Quot.sound` to the certificate's axioms.
  have snoc (f : Nat → Nat → Nat) (l : List Nat) (a x : Nat) :
      (l ++ [x]).foldl f a = f (l.foldl f a) x := by
    induction l generalizing a with
    | nil => rfl
    | cons y ys ih => exact ih (f a y)
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, snoc, ← ih]
    show Nat.add (fastPartial u prices k) (fastMin (fastMaximum (k+1) u biasDenominator prices 0)
      (fastSign (k+1) u biasDenominator)) = fastPartial u prices k +
        min (maximumFor (k+1) u biasDenominator prices) (signHeight (k+1) u biasDenominator)
    rw [fastMin_eq, fastMaximum_eq, fastSign_eq]
    rfl

theorem fastSum_eq (u : Nat) : fastSum u = upperSum u :=
  fastPartial_eq u (barrierList u biasDenominator) bins

theorem gridBound_of_fastBound {lo hi : Nat} (h : fastBound lo hi = true) : gridBound lo hi := by
  unfold fastBound at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨positive, ordered⟩, bound⟩ := h
  refine ⟨Nat.le_of_ble_eq_true positive, Nat.le_of_ble_eq_true ordered, ?_⟩
  have h := Nat.le_of_ble_eq_true bound
  rw [fastSum_eq] at h
  exact h

end ThresholdHC.SharpRMS.Window
