import Mathlib.Data.Nat.Factorial.Basic

/-! Integer lower bounds for every precommitted 18+7 allocation at gap 1/5. -/
namespace PilotFeedback

def sumTo {α : Type} [Zero α] [Add α] (f : ℕ → α) : ℕ → α
  | 0 => 0
  | n+1 => sumTo f n + f n

/-- Used only at 0 ≤ k ≤ n. The factorial formula avoids Pascal recursion. -/
def binom (n k : ℕ) := n.factorial / (k.factorial * (n-k).factorial)

def massDen : ℕ := 10 * 100^25
def scale : ℕ := 10^16

/-- Numerator over massDen for pilot count j, allocation (h,t,f), and
suffix head counts (a,b,c). The bias is p=u/10 and its prior mass is w/10.
Each paired coin supplies two flips, hence the compensating factor 100. -/
def mass (j h t a b c u w : ℕ) : ℕ :=
  let f := 7-h-t
  let heads := 30+4*u
  let tails := 70-4*u
  w * binom 18 j * binom h a * binom t b * binom f c *
    heads^(j-h+c) * tails^(18-j-t+(f-c)) *
    (9+4*u)^a * 21^(h-a+b) * (49-4*u)^(t-b) * 100^(h+t)

/-- Sum over the six unordered pairs of prior points of the product
of their masses times the squared separation in units of 1/10. -/
def pairSum (a b c d : ℕ) : ℕ :=
  9*a*b + 49*a*c + 100*a*d + 16*b*c + 49*b*d + 9*c*d

def varianceFloor (a b c d : ℕ) : ℕ :=
  scale * pairSum a b c d / (100 * massDen * (a+b+c+d))

def cellFloor (j h t a b c : ℕ) : ℕ :=
  let m := mass j h t a b c
  varianceFloor (m 0 2) (m 3 3) (m 7 3) (m 10 2)

def cells {α : Type} [Zero α] [Add α] (h t : ℕ) (v : ℕ → ℕ → ℕ → α) : α :=
  sumTo (fun a => sumTo (fun b => sumTo (v a b) (7-h-t+1)) (t+1)) (h+1)

def rowFloor (j h t : ℕ) := cells h t (cellFloor j h t)

/-- Lower bounds in units of 1e-16, chosen independently of the allocation. -/
def rowBound (j : ℕ) : ℕ :=
  [14042,175382,1012920,3601217,8960334,17126490,27383705,39052332,
   50546816,55287008,50546816,39052332,27383705,17126490,8960334,
   3601217,1012920,175382,14042][j]?.getD 0 * 10^6

def legal (j h t : ℕ) : Prop := h ≤ j ∧ t ≤ 18-j ∧ h+t ≤ 7
instance (j h t : ℕ) : Decidable (legal j h t) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem all_rows (j : Fin 19) (h t : Fin 8) :
    legal j h t → rowBound j ≤ rowFloor j h t := by
  revert j h t
  decide +kernel

theorem total_bound : sumTo rowBound 19 = 351033484000000 := by decide +kernel

end PilotFeedback
