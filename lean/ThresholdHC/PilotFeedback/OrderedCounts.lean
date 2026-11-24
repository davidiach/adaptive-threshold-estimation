import ThresholdHC.PilotFeedback.FeedbackComparison

/-! An integer likelihood for each ordered bit word at the four prior points.
An adjacent interchange of two precommitted actions preserves the sum of a
terminal function of these likelihoods. -/
namespace ThresholdHC.PilotFeedback.Ordered
open PilotFeedback

abbrev Mode := Option Bool
abbrev Weights := Fin 4 → ℕ

def radix : ℕ := 1450
def precision : ℕ := 10^24
def denominator : ℕ := 10 * radix^25

def headCode : Mode → Weights
  | none => ![435,609,841,1015]
  | some true => ![435,725,925,1015]
  | some false => ![435,525,725,1015]

def code (m : Mode) (b : Bool) (i : Fin 4) :=
  if b then headCode m i else radix - headCode m i

def advance (w : Weights) (m : Mode) (b : Bool) : Weights := fun i => w i * code m b i

def pilotWeights (n j : ℕ) : Weights := fun i =>
  (![2,3,3,2] i : ℕ) * (code none true i)^j * (code none false i)^(n-j)

theorem advance_pilot (n j : ℕ) (hj : j ≤ n) (b : Bool) :
    advance (pilotWeights n j) none b = pilotWeights (n+1) (j+b.toNat) := by
  funext i
  cases b <;> simp [advance,pilotWeights,show n+1-j=n-j+1 by omega,pow_succ] <;> ring

def leaf (w : Weights) : ℕ :=
  precision * pairSum (w 0) (w 1) (w 2) (w 3) /
    (100 * denominator * (w 0 + w 1 + w 2 + w 3))

def suffix (terminal : Weights → ℕ) : List Mode → Weights → ℕ
  | [], w => terminal w
  | m :: ms, w => suffix terminal ms (advance w m false) + suffix terminal ms (advance w m true)

private theorem commute (w : Weights) (m l : Mode) (b c : Bool) :
    advance (advance w m b) l c = advance (advance w l c) m b := by
  funext i
  simp only [advance]
  ac_rfl

theorem suffix_perm (terminal : Weights → ℕ) {xs ys : List Mode} (p : xs.Perm ys)
    (w : Weights) : suffix terminal xs w = suffix terminal ys w := by
  induction p generalizing w with
  | nil => rfl
  | cons m _ ih => simp only [suffix,ih]
  | swap a b xs =>
    simp only [suffix,commute (m := b) (l := a)]
    omega
  | trans _ _ ih₁ ih₂ => exact (ih₁ w).trans (ih₂ w)

def canonical (h t f : ℕ) : List Mode :=
  List.replicate h (some true) ++ List.replicate t (some false) ++ List.replicate f none

theorem counts_perm (xs : List Mode) :
    xs.Perm (canonical (xs.count (some true)) (xs.count (some false)) (xs.count none)) := by
  apply List.perm_iff_count.mpr
  intro m
  cases m with
  | none => simp [canonical,List.count_replicate]
  | some b => cases b <;> simp [canonical,List.count_replicate]

def pilotBound (j : ℕ) := rowBound j * (precision / scale) / binom 18 j

/-! ### Kernel evaluation with literal weights

The research module checks `certified` by kernel evaluation of `suffix` with
the weights as functions `Fin 4 → ℕ`, so the kernel meets equal weights as
different terms along different paths and evaluates them again. Since 24
November 2026 the library checks it in the form of `Literal.certified`: the
weights are a `Literal.Quad` of numbers, `Literal.force` reduces each number
to a literal before passing it on, so equal weights and counts are equal terms
and the kernel's cache can reuse their values, and `Literal.suffix` computes
`suffix` of `canonical h t f` by recursion on the three counts. The names
carry the prefix `Literal` because `Scheduled` and `StoppingUpdate` open this
namespace and define copies of the same evaluation. -/

/-- `k n`, with `n` reduced to a literal first: the kernel reduces the
recursor on `n+1` by evaluating `n`. -/
def Literal.force {α : Sort _} (n : ℕ) (k : ℕ → α) : α :=
  Nat.rec (motive := fun _ => α) (k 0) (fun m _ => k m) (Nat.succ n)

theorem Literal.force_eq {α : Sort _} (n : ℕ) (k : ℕ → α) : Literal.force n k = k n := rfl

/-- Four weights held as numbers. -/
structure Literal.Quad where
  w0 : ℕ
  w1 : ℕ
  w2 : ℕ
  w3 : ℕ

/-- The four numbers of `q` are the four weights of `w`. -/
def Literal.Agrees (q : Literal.Quad) (w : Weights) : Prop :=
  q.w0 = w 0 ∧ q.w1 = w 1 ∧ q.w2 = w 2 ∧ q.w3 = w 3

/-- `k` applied to the weights of `advance`, each reduced to a literal. -/
def Literal.advanceK {α : Sort _} (q : Literal.Quad) (m : Mode) (b : Bool)
    (k : Literal.Quad → α) : α :=
  Literal.force (Nat.mul q.w0 (code m b 0)) fun a =>
  Literal.force (Nat.mul q.w1 (code m b 1)) fun c =>
  Literal.force (Nat.mul q.w2 (code m b 2)) fun d =>
  Literal.force (Nat.mul q.w3 (code m b 3)) fun e => k ⟨a, c, d, e⟩

/-- `leaf` of the four numbers. -/
def Literal.leaf (q : Literal.Quad) : ℕ :=
  precision * pairSum q.w0 q.w1 q.w2 q.w3 / (100 * denominator * (q.w0 + q.w1 + q.w2 + q.w3))

/-- `suffix` of `canonical h t f` with terminal `T`, by recursion on the
three counts. -/
def Literal.suffix (T : Literal.Quad → ℕ) (h : ℕ) : ℕ → ℕ → Literal.Quad → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Literal.Quad → ℕ)
    (fun t => Nat.rec (motive := fun _ => ℕ → Literal.Quad → ℕ)
      (fun f => Nat.rec (motive := fun _ => Literal.Quad → ℕ) T
        (fun _ ih q => Literal.advanceK q none false fun a => Literal.advanceK q none true fun b =>
          Nat.add (ih a) (ih b)) f)
      (fun _ ih f q => Literal.advanceK q (some false) false fun a =>
          Literal.advanceK q (some false) true fun b => Nat.add (ih f a) (ih f b)) t)
    (fun _ ih t f q => Literal.advanceK q (some true) false fun a =>
          Literal.advanceK q (some true) true fun b => Nat.add (ih t f a) (ih t f b)) h

def Literal.pilot (j : ℕ) : Literal.Quad :=
  Literal.force (pilotWeights 18 j 0) fun a => Literal.force (pilotWeights 18 j 1) fun b =>
  Literal.force (pilotWeights 18 j 2) fun c => Literal.force (pilotWeights 18 j 3) fun d =>
    ⟨a, b, c, d⟩

/- The lemmas compare the four numbers pointwise, without equations between
functions, so `certified` keeps the axioms of the research proof. -/

theorem Literal.agrees_advance {q : Literal.Quad} {w : Weights} (hq : Literal.Agrees q w)
    (m : Mode) (b : Bool) :
    Literal.Agrees ⟨Nat.mul q.w0 (code m b 0), Nat.mul q.w1 (code m b 1),
      Nat.mul q.w2 (code m b 2), Nat.mul q.w3 (code m b 3)⟩ (advance w m b) := by
  obtain ⟨h0, h1, h2, h3⟩ := hq
  exact ⟨by rw [h0]; rfl, by rw [h1]; rfl, by rw [h2]; rfl, by rw [h3]; rfl⟩

theorem Literal.leaf_agrees (q : Literal.Quad) (w : Weights) (hq : Literal.Agrees q w) :
    Literal.leaf q = Ordered.leaf w := by
  obtain ⟨h0, h1, h2, h3⟩ := hq
  unfold Literal.leaf Ordered.leaf
  rw [h0, h1, h2, h3]

theorem Literal.suffix_eq (T : Literal.Quad → ℕ) (terminal : Weights → ℕ)
    (hT : ∀ q w, Literal.Agrees q w → T q = terminal w) (h t f : ℕ) :
    ∀ (q : Literal.Quad) (w : Weights), Literal.Agrees q w →
      Literal.suffix T h t f q = Ordered.suffix terminal (canonical h t f) w := by
  induction h with
  | succ h ih =>
    intro q w hq
    show Nat.add (Literal.suffix T h t f _) (Literal.suffix T h t f _) = _
    rw [ih _ _ (Literal.agrees_advance hq _ false), ih _ _ (Literal.agrees_advance hq _ true)]
    rfl
  | zero =>
  induction t with
  | succ t ih =>
    intro q w hq
    show Nat.add (Literal.suffix T 0 t f _) (Literal.suffix T 0 t f _) = _
    rw [ih _ _ (Literal.agrees_advance hq _ false), ih _ _ (Literal.agrees_advance hq _ true)]
    rfl
  | zero =>
  induction f with
  | succ f ih =>
    intro q w hq
    show Nat.add (Literal.suffix T 0 0 f _) (Literal.suffix T 0 0 f _) = _
    rw [ih _ _ (Literal.agrees_advance hq _ false), ih _ _ (Literal.agrees_advance hq _ true)]
    rfl
  | zero => exact hT

theorem Literal.pilot_agrees (j : ℕ) : Literal.Agrees (Literal.pilot j) (pilotWeights 18 j) :=
  ⟨rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- `certified` in the literal form, one kernel evaluation. -/
theorem Literal.certified : ∀ (j : Fin 19) (h t : Fin 8), legal j h t →
    pilotBound j ≤ Literal.suffix Literal.leaf h t (7-h-t) (Literal.pilot j) := by
  decide +kernel

theorem certified (j : Fin 19) (h t : Fin 8) : legal j h t →
    pilotBound j ≤ suffix leaf (canonical h t (7-h-t)) (pilotWeights 18 j) := by
  intro ok
  rw [← Literal.suffix_eq Literal.leaf leaf Literal.leaf_agrees _ _ _ _ _ (Literal.pilot_agrees j)]
  exact Literal.certified j h t ok

def pilotTree : ℕ → ℕ → ℕ
  | 0, j => pilotBound j
  | n+1, j => pilotTree n j + pilotTree n (j+1)

theorem total : 18735887^2 * (precision / 10^16) ≤ pilotTree 18 0 := by decide +kernel

end ThresholdHC.PilotFeedback.Ordered
