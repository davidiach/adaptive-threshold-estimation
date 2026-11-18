import OrderedBayes

namespace PilotFeedback.TwoUpdates
open Ordered

/-- Integer loss bounds when zero, one or two replacements remain. -/
structure Costs where
  fixed : ℕ
  once : ℕ
  twice : ℕ
  deriving Inhabited

def Costs.add (x y : Costs) : Costs := ⟨x.fixed+y.fixed, x.once+y.once, x.twice+y.twice⟩
def Costs.meet (x y : Costs) : Costs := ⟨min x.fixed y.fixed, min x.once y.once, min x.twice y.twice⟩

/-- Each path indexes an ordered, preselected schedule of nominal actions.
An unavailable revisit uses the fresh branch of the experiment. -/
inductive Table : ℕ → Type
  | tip (cost : Costs) : Table 0
  | node (fresh head tail : Table n) : Table (n+1)

def lookup : Table n → (ℕ → Mode) → ℕ → Costs
  | .tip x, _, _ => x
  | .node f h t, s, k => lookup (match s k with
      | none => f | some true => h | some false => t) s (k+1)

def least : Table n → Costs
  | .tip x => x
  | .node f h t => (least f).meet ((least h).meet (least t))

def addTables : Table n → Table n → Table n
  | .tip x, .tip y => .tip (x.add y)
  | .node f h t, .node f' h' t' => .node (addTables f f') (addTables h h') (addTables t t')

def cap (best : Costs) : Table n → Table n
  | .tip x => .tip ⟨x.fixed, min x.once best.fixed, min x.twice best.once⟩
  | .node f h t => .node (cap best f) (cap best h) (cap best t)

def allow (j k : ℕ) : Mode → Mode
  | none => none
  | some true => if k<j then some true else none
  | some false => if k<18-j then some false else none

/-- Each branch first takes the prescribed action. Its two answer costs are
added pointwise, so the same remaining schedule is used on both children.
Spending an update then minimizes over all possible replacement schedules. -/
def candidates (j k : ℕ) (child : Mode → Bool → Table n) : Table (n+1) :=
  let step := fun m => addTables (child m false) (child m true)
  .node (step none) (step (allow j k (some true))) (step (allow j k (some false)))

def solve (j : ℕ) : (n k : ℕ) → Weights → Table n
  | 0, _, w => .tip ⟨leaf w,leaf w,leaf w⟩
  | n+1, k, w =>
    let q := candidates j k fun m b => solve j n (k+1) (advance w m b)
    cap (least q) q

theorem lookup_add (a b : Table n) (s : ℕ → Mode) (k : ℕ) :
    lookup (addTables a b) s k = (lookup a s k).add (lookup b s k) := by
  induction a generalizing k with
  | tip => cases b; rfl
  | node f h t ihf ihh iht =>
    cases b
    cases e : s k with
    | none => simp [addTables,lookup,e,ihf]
    | some b => cases b <;> simp [addTables,lookup,e,ihh,iht]

theorem lookup_cap (best : Costs) (a : Table n) (s : ℕ → Mode) (k : ℕ) :
    lookup (cap best a) s k =
      ⟨(lookup a s k).fixed,min (lookup a s k).once best.fixed,min (lookup a s k).twice best.once⟩ := by
  induction a generalizing k with
  | tip => rfl
  | node f h t ihf ihh iht =>
    cases e : s k with
    | none => simp [cap,lookup,e,ihf]
    | some b => cases b <;> simp [cap,lookup,e,ihh,iht]

theorem least_le (a : Table n) (s : ℕ → Mode) (k : ℕ) :
    (least a).fixed ≤ (lookup a s k).fixed ∧ (least a).once ≤ (lookup a s k).once ∧
    (least a).twice ≤ (lookup a s k).twice := by
  induction a generalizing k with
  | tip => exact ⟨le_rfl,le_rfl,le_rfl⟩
  | node f h t ihf ihh iht =>
    have F := ihf (k+1)
    have H := ihh (k+1)
    have T := iht (k+1)
    cases e : s k with
    | none => simp only [least,Costs.meet,lookup,e]; omega
    | some b => cases b <;> simp only [least,Costs.meet,lookup,e] <;> omega

theorem lookup_candidates (j k : ℕ) (child : Mode → Bool → Table n) (s : ℕ → Mode) :
    lookup (candidates j k child) s k =
      (lookup (child (allow j k (s k)) false) s (k+1)).add
        (lookup (child (allow j k (s k)) true) s (k+1)) := by
  cases e : s k with
  | none => simp [candidates,lookup,e,allow,lookup_add]
  | some b => cases b <;> simp [candidates,lookup,e,lookup_add]

def floorRow (j : ℕ) : ℕ :=
  [1404278950786292244,974345025231250304,662039274152383219,441325711876518097,
   292821378530636801,199889013807594716,147482344772790146,122360581857734553,
   114021610213704873,112308513794185728,114021610213704873,122360581857734553,
   147482344772790146,199889013807594716,292821378530636801,441325711876518097,
   662039274152383219,974345025231250304,1404278950786292244][j]?.getD 0

def Row (j : ℕ) := floorRow j ≤ (least (solve j 7 0 (pilotWeights 18 j))).twice
instance (j : ℕ) : Decidable (Row j) := by unfold Row; infer_instance

def pilotSum : ℕ → ℕ → ℕ
  | 0, j => floorRow j
  | n+1, j => pilotSum n j + pilotSum n (j+1)

end PilotFeedback.TwoUpdates
