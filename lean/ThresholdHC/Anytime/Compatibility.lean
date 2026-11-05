import ThresholdHC.Anytime.Intervals

noncomputable section
namespace ThresholdHC.Anytime
open ThresholdHC.Tier6 ThresholdHC.HardBudget ThresholdHC.BlindUpper

variable {R : ℕ → Type} [∀ j, MeasurableSpace (R j)]

theorem planReader_compatible (base : ∀ j, AdaptiveEstimator (R j)) (r : ∀ j, R j)
    {k l : ℕ} (hkl : k ≤ l) (xs : List Bool) (hx : xs.length < paid k) :
    planReader base r l xs = planReader base r k xs := by
  induction l with
  | zero =>
    have hk : k=0 := by omega
    rw [hk]
  | succ l ih =>
    by_cases he : k=l+1
    · rw [he]
    · have hk : k ≤ l := by omega
      have hlen : xs.length < paid l := hx.trans_le (paid_strict.monotone hk)
      rw [planReader,thenRead,ite_eq_left hlen]
      exact ih hk

/-- Before the smaller reservation is exhausted, both endpoint policies
make identical choices for every observed history. -/
theorem endpoint_policy_compatible (base : ∀ j, AdaptiveEstimator (R j)) (M : ℝ) (radius : ℕ → ℝ)
    {k l : ℕ} (hkl : k ≤ l) (upper upper' : Bool) (r : ∀ j, R j)
    (xs : List Bool) (hx : xs.length < paid k) :
    (endpointEstimator base M radius l upper').policy r xs =
      (endpointEstimator base M radius k upper).policy r xs := by
  have hl := hx.trans_le (paid_strict.monotone hkl)
  change stopAt (paid l) (planReader base r l) xs = stopAt (paid k) (planReader base r k) xs
  rw [stopAt,ite_eq_left hl,stopAt,ite_eq_left hx,planReader_compatible base r hkl xs hx]

theorem readBlock_prefix {n m : ℕ} (h : n ≤ m) (p q : Reader) (s : Table)
    (hp : ∀ xs, xs.length < n → p xs = q xs) :
    ((readBlock m q s).1).take n = (readBlock n p s).1 := by
  induction n generalizing m p q s with
  | zero => simp [readBlock]
  | succ n ih =>
    cases m with
    | zero => omega
    | succ m =>
      have he := hp [] (by simp)
      rw [readBlock,readBlock,he]
      simp only [List.take_succ_cons]
      congr 1
      apply ih (by omega)
      intro xs hx
      exact hp (_::xs) (by simpa only [List.length_cons] using Nat.succ_lt_succ hx)

theorem planWord_prefix (base : ∀ j, AdaptiveEstimator (R j)) (r : ∀ j, R j)
    {k l : ℕ} (hkl : k ≤ l) (s : Table) :
    ((readBlock (paid l) (planReader base r l) s).1).take (paid k) =
      (readBlock (paid k) (planReader base r k) s).1 :=
  readBlock_prefix (paid_strict.monotone hkl) _ _ s
    (fun xs hx => (planReader_compatible base r hkl xs hx).symm)

end ThresholdHC.Anytime
