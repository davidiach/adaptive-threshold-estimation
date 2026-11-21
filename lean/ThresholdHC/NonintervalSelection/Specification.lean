import ThresholdHC.EntropyTail.Model

/-! The noninterval optimal assignment of the rare-event paper
(`paper/v6/rare-discussion.tex`, subsection Two scope examples, paragraph A
noninterval optimal assignment; preserved source
`paper/rare-event/v2/sections/discussion.tex`, same paragraph).

Let `ε = 1/1024` and put masses `(1-ε)/2`, `ε`, `(1-ε)/2` at the gaps `1/2`,
`1/4`, `1/8`, with `ρ = 1/4` and `h = B^{-1/2} = 1/1024`, that is `B = 2^20`.
All three atoms lie above `h`. Among the eight hard retained sets the unique
minimum of the inner cost `h√(ρ Γ_σ) + ∫ min{1,h/d} d(μ-σ)`
(`EntropyTail.selectionObjective`) retains `{1/2, 1/8}`. The paper's table
gives open rational enclosures of the inner cost divided by `h` for all eight
sets. The outer cap `ρ` is inactive, so the original functional
`EntropyTail.selection` (an infimum over all submeasures) takes the same value,
and no interval retention attains it.

The atoms are listed in the paper's order `1/2, 1/4, 1/8`, and a mask `s`
retains atom `i` exactly when `s i = true`. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.NonintervalSelection
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTail

/-- The gaps `1/2`, `1/4`, `1/8`, in the paper's order. -/
def atoms : Fin 3 → Gap :=
  ![⟨1/2, by norm_num⟩, ⟨1/4, by norm_num⟩, ⟨1/8, by norm_num⟩]

/-- The masses `(1-ε)/2`, `ε`, `(1-ε)/2` with `ε = 1/1024`. -/
def masses : Fin 3 → ℝ := ![(1 - 1/1024)/2, 1/1024, (1 - 1/1024)/2]

/-- The three-atom law. -/
def law : Measure Gap := ∑ i, ENNReal.ofReal (masses i) • Measure.dirac (atoms i)

/-- The hard retained part for the mask `s`: atom `i` is retained iff `s i`. -/
def retained (s : Fin 3 → Bool) : Measure Gap :=
  ∑ i, (if s i then ENNReal.ofReal (masses i) else 0) • Measure.dirac (atoms i)

/-- The optimal mask: retain `1/2` and `1/8`, treat `1/4` ordinarily. -/
def optimalMask : Fin 3 → Bool := ![true, false, true]

/-- The paper's table: a mask and the open enclosure `(lower, upper)` of the
inner cost divided by `h`. -/
def enclosures : List ((Fin 3 → Bool) × ℚ × ℚ) :=
  [(![false, false, false], 499902/100000, 499903/100000),
   (![true, false, false], 470676/100000, 470677/100000),
   (![false, true, false], 505761/100000, 505762/100000),
   (![true, true, false], 472155/100000, 472156/100000),
   (![false, false, true], 382997/100000, 382998/100000),
   (![true, false, true], 322748/100000, 322749/100000),
   (![false, true, true], 383271/100000, 383272/100000),
   (![true, true, true], 322943/100000, 322944/100000)]

/-- The law is a probability law, `h = B^{-1/2} = 1/1024` at `B = 1048576`,
every atom lies above `h`, and every hard retained part is a submeasure. -/
def SetupStatement : Prop :=
  IsProbabilityMeasure law ∧ 1 / Real.sqrt 1048576 = (1/1024 : ℝ) ∧
    (∀ i, (1/1024 : ℝ) < (atoms i : ℝ)) ∧ ∀ s, retained s ≤ law

/-- The table covers all eight masks, and each displayed open interval contains
the inner cost divided by `h`. -/
def EnclosureStatement : Prop :=
  (∀ s, ∃ e ∈ enclosures, e.1 = s) ∧
  ∀ e ∈ enclosures,
    (e.2.1 : ℝ) < (selectionObjective law (1/4) 1048576 (retained e.1)).toReal / (1 / Real.sqrt 1048576) ∧
    (selectionObjective law (1/4) 1048576 (retained e.1)).toReal / (1 / Real.sqrt 1048576) < (e.2.2 : ℝ)

/-- Among the eight hard retained sets, `{1/2, 1/8}` is the unique minimum. -/
def UniqueHardMinimumStatement : Prop :=
  ∀ s : Fin 3 → Bool, s ≠ optimalMask →
    selectionObjective law (1/4) 1048576 (retained optimalMask) <
      selectionObjective law (1/4) 1048576 (retained s)

/-- The cap is inactive, the original functional over all submeasures takes the
value of the hard minimum, and that retained part is the restriction of the law
to `{1/2, 1/8}`. -/
def OriginalOptimizerStatement : Prop :=
  selectionObjective law (1/4) 1048576 (retained optimalMask) < ENNReal.ofReal (1/4) ∧
  selection law (1/4) 1048576 = selectionObjective law (1/4) 1048576 (retained optimalMask) ∧
  retained optimalMask = law.restrict {d : Gap | (d : ℝ) = 1/2 ∨ (d : ℝ) = 1/8}

/-- The intervening atom has positive mass, the optimal mask is not cut out by
any interval, and no interval retention attains the original functional. -/
def NonintervalStatement : Prop :=
  0 < masses 1 ∧
  (¬ ∃ I : Set ℝ, I.OrdConnected ∧ ∀ i, (optimalMask i = true ↔ (atoms i : ℝ) ∈ I)) ∧
  ∀ I : Set ℝ, I.OrdConnected →
    selection law (1/4) 1048576 <
      selectionObjective law (1/4) 1048576 (law.restrict {d : Gap | (d : ℝ) ∈ I})

end ThresholdHC.NonintervalSelection
