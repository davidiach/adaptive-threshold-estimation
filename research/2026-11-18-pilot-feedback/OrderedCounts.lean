import FeedbackComparison

/-! An integer likelihood for each ordered bit word at the four prior points.
An adjacent interchange of two precommitted actions preserves the sum of a
terminal function of these likelihoods. -/
namespace PilotFeedback.Ordered
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

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem certified (j : Fin 19) (h t : Fin 8) : legal j h t →
    pilotBound j ≤ suffix leaf (canonical h t (7-h-t)) (pilotWeights 18 j) := by
  revert j h t
  decide +kernel

def pilotTree : ℕ → ℕ → ℕ
  | 0, j => pilotBound j
  | n+1, j => pilotTree n j + pilotTree n (j+1)

theorem total : 18735887^2 * (precision / 10^16) ≤ pilotTree 18 0 := by decide +kernel

end PilotFeedback.Ordered
