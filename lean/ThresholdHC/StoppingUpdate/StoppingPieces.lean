import ThresholdHC.StoppingUpdate.StoppingBounds

/-! The research certificate checks each pilot count `j` with one kernel
evaluation of `rowCheck j`; its build ran out of memory above 13.5 GB (with
`lean -j2`, so possibly with two rows at once). Here a row is split by its first three initial actions into 27
pieces `pieceCheck j a b c`, each evaluated in its own kernel check. A piece
with an illegal prefix reduces to `true` without evaluating the recursion. -/
namespace ThresholdHC.StoppingUpdate
open ThresholdHC.PilotFeedback ThresholdHC.PilotFeedback.Ordered

/-- The three follow-up actions: fresh coin, pilot head, pilot tail. -/
def modeOf (a : Fin 3) : Mode := ![none, some true, some false] a

/-- The part of `rowCheck j` whose initial plans begin with the actions
`modeOf a`, `modeOf b`, `modeOf c`. -/
def pieceCheck (j : ℕ) (a b c : Fin 3) : Bool :=
  if modeOf a ∈ menu j 0 ∧ modeOf b ∈ menu j 1 ∧ modeOf c ∈ menu j 2 then
    (plans j 3 3).all fun ms =>
      decide (floorRow j ≤ unused j (modeOf a :: modeOf b :: modeOf c :: ms) 0 (pilotWeights 18 j))
  else true

theorem mem_plans_succ {j n k : ℕ} {ms : List Mode} :
    ms ∈ plans j (n+1) k ↔ ∃ m ∈ menu j k, ∃ rest ∈ plans j n (k+1), ms = m :: rest := by
  simp only [plans, List.mem_flatMap, List.mem_map]
  constructor <;> rintro ⟨m, hm, r, hr, e⟩ <;> exact ⟨m, hm, r, hr, e.symm⟩

theorem modeOf_surj : ∀ m : Mode, ∃ a, modeOf a = m
  | none => ⟨0, rfl⟩
  | some true => ⟨1, rfl⟩
  | some false => ⟨2, rfl⟩

/-- A row holds once each of its 27 pieces holds. -/
theorem row_of_pieces (j : ℕ) (h : ∀ a b c : Fin 3, pieceCheck j a b c = true) :
    rowCheck j = true := by
  rw [rowCheck, List.all_eq_true]
  intro ms hms
  obtain ⟨m0, h0, r0, hr0, rfl⟩ := mem_plans_succ.mp hms
  obtain ⟨m1, h1, r1, hr1, rfl⟩ := mem_plans_succ.mp hr0
  obtain ⟨m2, h2, rest, hrest, rfl⟩ := mem_plans_succ.mp hr1
  obtain ⟨a, rfl⟩ := modeOf_surj m0
  obtain ⟨b, rfl⟩ := modeOf_surj m1
  obtain ⟨c, rfl⟩ := modeOf_surj m2
  have hc : modeOf a ∈ menu j 0 ∧ modeOf b ∈ menu j 1 ∧ modeOf c ∈ menu j 2 := ⟨h0, h1, h2⟩
  have p := h a b c
  rw [pieceCheck, ite_eq_left_of_eq_true _ _ (eq_true hc)] at p
  exact List.all_eq_true.mp p rest hrest

end ThresholdHC.StoppingUpdate
