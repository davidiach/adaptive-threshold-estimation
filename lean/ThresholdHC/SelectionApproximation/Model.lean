import ThresholdHC.EntropyTailQuantile.CostEntropy
import ThresholdHC.BandCostSelection.Dynamic

/-! Statements and definitions for the two approximation components.
The entropy is the existing project entropy, including zero coordinates.
The solver keeps actual traces with maximum saving in each reachable bin.
These statements do not assert the full approximation scheme or its bit complexity. -/

noncomputable section
open scoped BigOperators Classical
namespace ThresholdHC.SelectionApproximation
open ThresholdHC.EntropyTailQuantile ThresholdHC.BandCostSelection

/-- Symmetric multiplicative comparison, meaningful also at zero. -/
def Close (c x y : ℝ) : Prop := x ≤ c*y ∧ y ≤ c*x

def baseSummary {ι : Type*} [Fintype ι] (r : ℝ) (a : ι → ℝ) : ℝ :=
  ∑ i, a i * (1 + Real.log (a i / r))

def potential (r A : ℝ) : ℝ := A * (2 + Real.log A - Real.log r)

/-- A bin certificate is required only for nonnegative inputs. -/
def ValidBins {κ : Type*} (c : ℝ) (key : ℝ → κ) : Prop :=
  ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → key x = key y → Close c x y

def summaryKey {α κ : Type*} (key : ℝ → κ) (a h : α → ℝ) (xs : List α) : κ × κ :=
  (key (traceSaved a xs), key (traceSaved h xs))

def trimSolve {α κ : Type*} (key : ℝ → κ) (a h saving : α → ℝ) :
    List (Finset α) → Finset (List α)
  | [] => {[]}
  | menu :: rest => compress (summaryKey key a h) (traceSaved saving)
      (extend (trimSolve key a h saving rest) menu)

/-- Actual entropy comparison from certified summary enclosures and multiplicative
proximity. The inputs may have different finite index types. -/
def EntropyPerturbationStatement : Prop :=
  ∀ {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ℝ) (b : κ → ℝ) (r U L δ η Ha Hb : ℝ),
    (∀ i, 0 ≤ a i) → (∀ i, 0 ≤ b i) →
    0 < r → 0 ≤ L → 0 ≤ δ → 0 ≤ η →
    r ≤ costTotal a → costTotal a ≤ U →
    r ≤ costTotal b → costTotal b ≤ U →
    3 + Real.log (U/r) ≤ L →
    baseSummary r a ≤ Ha → Ha ≤ baseSummary r a + δ*costTotal a →
    baseSummary r b ≤ Hb → Hb ≤ baseSummary r b + δ*costTotal b →
    0 ≤ Ha → Ha ≤ L*costTotal a →
    Close (1+η) (costTotal a) (costTotal b) → Close (1+η) Ha Hb →
    costEntropy b ≤ costEntropy a + (2*L*η+δ*(1+η))*costTotal a

/-- The retained witness is feasible, improves saving, and approximates both additive
coordinates at every finite stage. No ratio or nonzero-coordinate premise is needed. -/
def CompressionInvariantStatement : Prop :=
  ∀ {α κ : Type*} (key : ℝ → κ) (a h saving : α → ℝ) (c : ℝ),
    1 ≤ c → (∀ x, 0 ≤ a x) → (∀ x, 0 ≤ h x) → ValidBins c key →
    ∀ (menus : List (Finset α)) (xs : List α), xs ∈ enumerate menus →
      ∃ ys ∈ trimSolve key a h saving menus,
        ys ∈ enumerate menus ∧ traceSaved saving xs ≤ traceSaved saving ys ∧
        Close (c^menus.length) (traceSaved a xs) (traceSaved a ys) ∧
        Close (c^menus.length) (traceSaved h xs) (traceSaved h ys)

end ThresholdHC.SelectionApproximation
