import ThresholdHC.PilotFeedback.ScheduledBounds

/-! The integer certificate of the one-update class, with the research
statements. The research module checks each `Row j` by one kernel evaluation
of its `Decidable` instance. That evaluation holds the weights as functions
`Fin 4 → ℕ`, so the kernel meets equal weights as different terms along
different paths of `suffix` and `tailCost` and evaluates them again. Since
23 November 2026 each row is checked instead in the form of `fastRows`: the
weights are a `Quad` of numbers, `force` reduces each number to a literal
before passing it on, so equal weights and counts are equal terms and the
kernel's cache can reuse their values, and `fastSuffix` computes `suffix`
of `canonical h t f` by recursion on the three counts. The lemmas before
`certified` prove each step equal to the original. -/
namespace ThresholdHC.PilotFeedback.Scheduled
open Ordered

set_option maxHeartbeats 0
set_option maxRecDepth 100000

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

/-- `suffix` of `canonical h t f` with terminal `T`, by recursion on the
three counts. -/
def fastSuffix (T : Quad → ℕ) (h : ℕ) : ℕ → ℕ → Quad → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Quad → ℕ)
    (fun t => Nat.rec (motive := fun _ => ℕ → Quad → ℕ)
      (fun f => Nat.rec (motive := fun _ => Quad → ℕ) T
        (fun _ ih q => advanceK q none false fun a => advanceK q none true fun b =>
          Nat.add (ih a) (ih b)) f)
      (fun _ ih f q => advanceK q (some false) false fun a => advanceK q (some false) true fun b =>
          Nat.add (ih f a) (ih f b)) t)
    (fun _ ih t f q => advanceK q (some true) false fun a => advanceK q (some true) true fun b =>
          Nat.add (ih t f a) (ih t f b)) h

def fastMinThrough (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) (f 0) (fun n ih => fastMin ih (force (n+1) f)) n

/-- `tailCost` with the counts and weights reduced to literals. -/
def fastTail (j k : ℕ) (q : Quad) : ℕ :=
  fastMinThrough (fun h => fastMinThrough (fun t => force (7-k-h-t) fun f =>
    fastSuffix fastLeaf h t f q) (min (7-k-h) (18-j-k))) (min (7-k) (j-k))

def fastPilot (j : ℕ) : Quad :=
  force (pilotWeights 18 j 0) fun a => force (pilotWeights 18 j 1) fun b =>
  force (pilotWeights 18 j 2) fun c => force (pilotWeights 18 j 3) fun d => ⟨a, b, c, d⟩

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

theorem fastSuffix_eq (T : Quad → ℕ) (terminal : Weights → ℕ)
    (hT : ∀ q, T q = terminal q.toWeights) (h t f : ℕ) (q : Quad) :
    fastSuffix T h t f q = suffix terminal (canonical h t f) q.toWeights := by
  induction h generalizing q with
  | succ h ih =>
    show Nat.add (fastSuffix T h t f _) (fastSuffix T h t f _) = _
    simp only [canonical, List.replicate_succ, List.cons_append, suffix]
    rw [ih, ih, advance_toWeights, advance_toWeights]
    rfl
  | zero =>
  induction t generalizing q with
  | succ t ih =>
    show Nat.add (fastSuffix T 0 t f _) (fastSuffix T 0 t f _) = _
    simp only [canonical, List.replicate_succ, List.replicate_zero, List.nil_append,
      List.cons_append, suffix] at ih ⊢
    rw [ih, ih, advance_toWeights, advance_toWeights]
    rfl
  | zero =>
  induction f generalizing q with
  | succ f ih =>
    show Nat.add (fastSuffix T 0 0 f _) (fastSuffix T 0 0 f _) = _
    simp only [canonical, List.replicate_succ, List.replicate_zero, List.nil_append,
      suffix] at ih ⊢
    rw [ih, ih, advance_toWeights, advance_toWeights]
    rfl
  | zero => exact hT q

theorem fastMinThrough_eq (f : ℕ → ℕ) (n : ℕ) : fastMinThrough f n = minThrough f n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show fastMin (fastMinThrough f n) (f (n+1)) = _
    rw [fastMin_eq, ih]
    rfl

theorem fastTail_eq (j k : ℕ) (q : Quad) : fastTail j k q = tailCost j k q.toWeights := by
  simp only [fastTail, tailCost, fastMinThrough_eq, force_eq,
    fastSuffix_eq fastLeaf leaf (fun _ => rfl)]

theorem fastPilot_toWeights (j : ℕ) : (fastPilot j).toWeights = pilotWeights 18 j := by
  funext i
  fin_cases i <;> rfl

/-- Each row in the fast form, one kernel evaluation per pilot count. -/
theorem fastRows (j : Fin 19) : ∀ (k h t : Fin 8), firstOK j k h t →
    pilotFloor j ≤ fastSuffix (fastTail j k) h t (k-h-t) (fastPilot j) := by
  fin_cases j <;> decide +kernel

theorem certified (j : Fin 19) : Row j := by
  intro k h t ok
  have row := fastRows j k h t ok
  rwa [fastSuffix_eq _ _ (fastTail_eq j k), fastPilot_toWeights] at row

theorem certificate_total : 186960371^2 * 10^6 ≤ pilotSum 18 0 := by decide +kernel

end ThresholdHC.PilotFeedback.Scheduled
