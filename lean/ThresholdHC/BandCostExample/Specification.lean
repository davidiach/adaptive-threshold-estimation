import ThresholdHC.GapLawMenus.Full

/-! The 64-band example of the finite-law section of the paper
(`paper/v6/finite-laws.tex`, section `fg:sec:model`, paragraph on repeated
suffix costs: the selection algorithm certifies an optimizer on a 64-band
example using 65 terminal states). The example itself is defined in
`docs/BAND_COST_SELECTION.md`, section Example with 64 occupied bands: take
`d_i = 2^{-i}` and masses proportional to `d_i^2` for `i = 1, ..., 64`, with
`rho = 1/4` and budget `B = 2^32`. Every nonempty suffix has the same cost;
the run checks 4160 transitions and 65 terminal states and certifies that
selecting the two largest gaps attains `K`.

Here atom `i : Fin 64` is the gap `2^{-(i+1)}` (the paper's `d_{i+1}`); it lies
in canonical band `i`. The counts are stated for the formal solver
`BandCostSelection.solve` and `BandCostSelection.transitionCount` on the actual
support menus `GapLawMenus.menus`, not for the Python toolkit. The strict
uniqueness over all `2^64` hard masks is an added strengthening; the source
only asserts that the two largest gaps attain `K`. -/
noncomputable section
open MeasureTheory
open scoped ENNReal Classical
namespace ThresholdHC.BandCostExample
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTail ThresholdHC.BandwiseSuffix
open ThresholdHC.BandCostSelection ThresholdHC.GapLawMenus

/-- The gap `2^{-(i+1)}` (the paper's `d_{i+1}`); it lies in canonical band `i`. -/
def atoms (i : Fin 64) : Gap :=
  ⟨(1/2 : ℝ)^(i.val+1), pow_pos (by norm_num) _,
    pow_le_of_le_one (by norm_num) (by norm_num) (Nat.succ_ne_zero _)⟩

/-- Masses proportional to `d^2`, normalized by `z = ∑ d^2`. -/
def masses (i : Fin 64) : ℝ := (atoms i : ℝ)^2 / ∑ j, (atoms j : ℝ)^2

/-- The 64-atom law. -/
def law : Measure Gap := ∑ i, ENNReal.ofReal (masses i) • Measure.dirac (atoms i)

/-- The hard retained part for the mask `s`: atom `i` is retained iff `s i`. -/
def retained (s : Fin 64 → Bool) : Measure Gap :=
  ∑ i, (if s i then ENNReal.ofReal (masses i) else 0) • Measure.dirac (atoms i)

/-- Retain the two largest gaps `1/2` and `1/4`. -/
def topTwo : Fin 64 → Bool := fun i => decide (i.val < 2)

/-- The finite atom set read by the solver. -/
def atomSet : Finset Gap := Finset.univ.image atoms

/-- The law is a probability law supported on the 64 atoms, atom `i` lies in
canonical band `i`, `h = B^{-1/2} = 2^{-16}`, and every hard retained part is a
submeasure. -/
def SetupStatement : Prop :=
  IsProbabilityMeasure law ∧ law.support = Set.range atoms ∧
  (∀ i, atoms i ∈ band i.val) ∧ 1 / Real.sqrt 4294967296 = (1/65536 : ℝ) ∧
  ∀ s, retained s ≤ law

/-- Each one-atom suffix `{atoms i}` has the same positive inverse-square cost
`c = 1/∑ d_j^2`. Atom `i` is alone in band `i`, so this is the only nonempty
suffix of that band (`Solver.mem_menus`). -/
def EqualCostStatement : Prop :=
  (∀ i : Fin 64, GapLawMenus.cost law ({atoms i} : Finset Gap) = 1 / ∑ j, (atoms j : ℝ)^2) ∧
  0 < 1 / ∑ j : Fin 64, (atoms j : ℝ)^2

/-- Added strengthening (not in the source): among the `2^64` hard masks the two
largest gaps are the strict unique minimum. -/
def UniqueHardMinimumStatement : Prop :=
  ∀ s : Fin 64 → Bool, s ≠ topTwo →
    selectionObjective law (1/4) 4294967296 (retained topTwo) <
      selectionObjective law (1/4) 4294967296 (retained s)

/-- The cap is inactive, the original functional over all submeasures takes the
value of the hard minimum, and that retained part is the restriction of the law
to `{1/2, 1/4}`. -/
def OptimizerStatement : Prop :=
  selectionObjective law (1/4) 4294967296 (retained topTwo) < ENNReal.ofReal (1/4) ∧
  selection law (1/4) 4294967296 =
    selectionObjective law (1/4) 4294967296 (retained topTwo) ∧
  retained topTwo = law.restrict {d : Gap | (d : ℝ) = 1/2 ∨ (d : ℝ) = 1/4}

/-- The formal solver run on the actual support menus: `2^64` suffixes, 64
two-option menus, 4160 transitions, 65 terminal states, and a retained terminal
trace that selects `{1/2, 1/4}` and has value `K`. -/
def SolverRunStatement : Prop :=
  (suffixChoices atomSet).card = 2^64 ∧
  (menus atomSet (occupiedBands atomSet)).length = 64 ∧
  (∀ M ∈ menus atomSet (occupiedBands atomSet), M.card = 2) ∧
  transitionCount (GapLawMenus.cost law) (GapLawMenus.saving law (1 / Real.sqrt 4294967296))
      (menus atomSet (occupiedBands atomSet)) = 4160 ∧
  (solve (GapLawMenus.cost law) (GapLawMenus.saving law (1 / Real.sqrt 4294967296))
      (menus atomSet (occupiedBands atomSet))).card = 65 ∧
  ∃ xs ∈ solve (GapLawMenus.cost law) (GapLawMenus.saving law (1 / Real.sqrt 4294967296))
      (menus atomSet (occupiedBands atomSet)),
    (traceSet xs : Set Gap) = {d : Gap | (d : ℝ) = 1/2 ∨ (d : ℝ) = 1/4} ∧
    selection law (1/4) 4294967296 =
      ENNReal.ofReal (menuObjective law (1/4) 4294967296 xs)

end ThresholdHC.BandCostExample
