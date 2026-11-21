import ThresholdHC.BandCostExample.Solver

/-! The 64-band example of the finite-law section of the paper
(`paper/v6/finite-laws.tex`, in the section labelled `fg:sec:model`; the example
is defined in `docs/BAND_COST_SELECTION.md`, in the part headed Example with 64
occupied bands): the five target statements of `Specification.lean`. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.BandCostExample
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTail

/-- The law is a probability law supported on the 64 atoms, atom `i` lies in
band `i`, `h = 2^{-16}`, and every hard retained part is a submeasure. -/
theorem setup : SetupStatement :=
  ⟨law_probability, law_support, atoms_mem_band, by rw [sqrt_budget], retained_le⟩

/-- Each one-atom suffix `{atoms i}` has the same positive cost `c = 1/∑ d_j^2`. -/
theorem equal_cost : EqualCostStatement :=
  ⟨fun i => cost_atom i, cc_pos⟩

/-- The two largest gaps are the strict unique minimum over all `2^64` hard masks. -/
theorem unique_hard_minimum : UniqueHardMinimumStatement :=
  objective_topTwo_lt

/-- The cap is inactive and the two largest gaps attain the original functional `K`. -/
theorem optimizer : OptimizerStatement :=
  ⟨objective_topTwo_lt_cap, selection_eq_topTwo, retained_topTwo_eq⟩

/-- The formal solver run: `2^64` suffixes, 64 two-option menus, 4160
transitions, 65 terminal states and a retained trace selecting `{1/2, 1/4}` with
value `K`. -/
theorem solver_run : SolverRunStatement :=
  ⟨suffixChoices_card, menus_length, menus_card, transitions, solve_card, solver_trace⟩

end ThresholdHC.BandCostExample
