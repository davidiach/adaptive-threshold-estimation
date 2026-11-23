import ThresholdHC.StoppingUpdate.StoppingBounds

/-! The research certificate checks each pilot count `j` with one kernel
evaluation of `rowCheck j`; its build ran out of memory above 13.5 GB (with
`lean -j2`, so possibly with two rows at once). The library first split each
row by its first three initial actions into 27 pieces `pieceCheck j a b c`,
each evaluated in its own kernel check; a piece with an illegal prefix
reduces to `true` without evaluating the recursion. `pieceCheck` and
`row_of_pieces` remain below. Since 23 November 2026 the row modules evaluate
each row whole, in the form `fastRowCheck` of the last section, and
`rowCheck_eq_fast` proves it equal to `rowCheck`. -/
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

/-! ### Kernel evaluation of whole rows

`rowCheck` holds its weights as functions `Fin 4 → ℕ`. Along different
paths of `unused`, `tailCost` and `suffix` the kernel meets equal weights as
different terms and evaluates them again. Here the weights are a `Quad` of
numbers and `force` reduces each number to a literal before passing it on,
so equal weights, counts and positions are equal terms and the kernel's
cache can reuse their values. `fastSuffix` computes `suffix leaf` of
`canonical h t f` by recursion on the three counts. The lemmas after the
definitions prove each step equal to the original, ending with
`rowCheck_eq_fast`. -/

/-- `k n`, with `n` reduced to a literal first: the kernel reduces the
recursor on `n+1` by evaluating `n`. -/
def force {α : Sort _} (n : ℕ) (k : ℕ → α) : α :=
  Nat.rec (motive := fun _ => α) (k 0) (fun m _ => k m) (Nat.succ n)

theorem force_eq {α : Sort _} (n : ℕ) (k : ℕ → α) : force n k = k n := rfl

/-- Four weights held as numbers. -/
structure Quad where
  w0 : ℕ
  w1 : ℕ
  w2 : ℕ
  w3 : ℕ

def Quad.toWeights (q : Quad) : Weights := ![q.w0, q.w1, q.w2, q.w3]

/-- `k` applied to the weights of `advance`, each reduced to a literal. -/
def advanceK {α : Sort _} (q : Quad) (m : Mode) (b : Bool) (k : Quad → α) : α :=
  force (Nat.mul q.w0 (code m b 0)) fun a =>
  force (Nat.mul q.w1 (code m b 1)) fun c =>
  force (Nat.mul q.w2 (code m b 2)) fun d =>
  force (Nat.mul q.w3 (code m b 3)) fun e => k ⟨a, c, d, e⟩

def fastMin (a b : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) b a (Nat.ble a b)

def fastLeaf (q : Quad) : ℕ := leaf q.toWeights

/-- `suffix leaf (canonical h t f)`, by recursion on the three counts. -/
def fastSuffix (h : ℕ) : ℕ → ℕ → Quad → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Quad → ℕ)
    (fun t => Nat.rec (motive := fun _ => ℕ → Quad → ℕ)
      (fun f => Nat.rec (motive := fun _ => Quad → ℕ) fastLeaf
        (fun _ ih q => advanceK q none false fun a => advanceK q none true fun b =>
          Nat.add (ih a) (ih b)) f)
      (fun _ ih f q => advanceK q (some false) false fun a => advanceK q (some false) true fun b =>
          Nat.add (ih f a) (ih f b)) t)
    (fun _ ih t f q => advanceK q (some true) false fun a => advanceK q (some true) true fun b =>
          Nat.add (ih t f a) (ih t f b)) h

def fastMinThrough (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) (f 0) (fun n ih => fastMin ih (force (n+1) f)) n

def fastTail (j k : ℕ) (q : Quad) : ℕ :=
  fastMinThrough (fun h => fastMinThrough (fun t => force (7-k-h-t) fun f => fastSuffix h t f q)
    (min (7-k-h) (18-j-k))) (min (7-k) (j-k))

def fastUnused (j : ℕ) (ms : List Mode) : ℕ → Quad → ℕ :=
  List.rec (motive := fun _ => ℕ → Quad → ℕ) (fun k q => fastTail j k q)
    (fun m _ ih k q => fastMin (fastTail j k q) (force (k+1) fun k' =>
      advanceK q m false fun a => advanceK q m true fun b => Nat.add (ih k' a) (ih k' b))) ms

def fastPilot (j : ℕ) : Quad :=
  force (pilotWeights 18 j 0) fun a => force (pilotWeights 18 j 1) fun b =>
  force (pilotWeights 18 j 2) fun c => force (pilotWeights 18 j 3) fun d => ⟨a, b, c, d⟩

def fastRowCheck (j : ℕ) : Bool := (plans j 6 0).all fun ms =>
  decide (floorRow j ≤ fastUnused j ms 0 (fastPilot j))

theorem advance_toWeights (q : Quad) (m : Mode) (b : Bool) :
    advance q.toWeights m b = (⟨Nat.mul q.w0 (code m b 0), Nat.mul q.w1 (code m b 1),
      Nat.mul q.w2 (code m b 2), Nat.mul q.w3 (code m b 3)⟩ : Quad).toWeights := by
  funext i
  fin_cases i <;> rfl

theorem fastMin_eq (a b : ℕ) : fastMin a b = min a b := by
  show Bool.rec (motive := fun _ => ℕ) b a (Nat.ble a b) = if a ≤ b then a else b
  cases h : Nat.ble a b with
  | false => exact (ite_eq_right (Nat.not_le_of_not_ble_eq_true (Bool.ne_true_of_eq_false h))).symm
  | true => exact (ite_eq_left (Nat.le_of_ble_eq_true h)).symm

theorem fastSuffix_eq (h t f : ℕ) (q : Quad) :
    fastSuffix h t f q = suffix leaf (canonical h t f) q.toWeights := by
  induction h generalizing q with
  | succ h ih =>
    show Nat.add (fastSuffix h t f _) (fastSuffix h t f _) = _
    simp only [canonical, List.replicate_succ, List.cons_append, suffix]
    rw [ih, ih, advance_toWeights, advance_toWeights]
    rfl
  | zero =>
  induction t generalizing q with
  | succ t ih =>
    show Nat.add (fastSuffix 0 t f _) (fastSuffix 0 t f _) = _
    simp only [canonical, List.replicate_succ, List.replicate_zero, List.nil_append,
      List.cons_append, suffix] at ih ⊢
    rw [ih, ih, advance_toWeights, advance_toWeights]
    rfl
  | zero =>
  induction f generalizing q with
  | succ f ih =>
    show Nat.add (fastSuffix 0 0 f _) (fastSuffix 0 0 f _) = _
    simp only [canonical, List.replicate_succ, List.replicate_zero, List.nil_append,
      suffix] at ih ⊢
    rw [ih, ih, advance_toWeights, advance_toWeights]
    rfl
  | zero => rfl

theorem fastMinThrough_eq (f : ℕ → ℕ) (n : ℕ) :
    fastMinThrough f n = Scheduled.minThrough f n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show fastMin (fastMinThrough f n) (f (n+1)) = _
    rw [fastMin_eq, ih]
    rfl

theorem fastTail_eq (j k : ℕ) (q : Quad) : fastTail j k q = Scheduled.tailCost j k q.toWeights := by
  simp only [fastTail, Scheduled.tailCost, fastMinThrough_eq, force_eq, fastSuffix_eq]

theorem fastUnused_eq (j : ℕ) (ms : List Mode) (k : ℕ) (q : Quad) :
    fastUnused j ms k q = unused j ms k q.toWeights := by
  induction ms generalizing k q with
  | nil => exact fastTail_eq j k q
  | cons m ms ih =>
    show fastMin (fastTail j k q) (Nat.add (fastUnused j ms (k+1) _) (fastUnused j ms (k+1) _)) = _
    rw [fastMin_eq, fastTail_eq, ih, ih, unused, advance_toWeights, advance_toWeights]
    rfl

theorem fastPilot_toWeights (j : ℕ) : (fastPilot j).toWeights = pilotWeights 18 j := by
  funext i
  fin_cases i <;> rfl

theorem rowCheck_eq_fast (j : ℕ) : rowCheck j = fastRowCheck j := by
  simp only [rowCheck, fastRowCheck, fastUnused_eq, fastPilot_toWeights]

end ThresholdHC.StoppingUpdate
