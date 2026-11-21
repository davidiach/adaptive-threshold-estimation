import ThresholdHC.NonintervalSelection.Specification
import ThresholdHC.GlobalSelectionCertificates.Menu

/-! Rational data for the noninterval example, in the paper's order
`1/2, 1/4, 1/8`, and its bridge to the measure-level specification. The three
gaps lie in the canonical bands `0, 1, 2`. The capped objective of a hard mask is
the value of the checker expression `objectiveExpr`; while that value is below the
cap `1/4`, it is the inner cost `selectionObjective` itself. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.NonintervalSelection
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTail ThresholdHC.FiniteLawCertificates
open ThresholdHC.GlobalSelectionCertificates

/-- The rational gaps `1/2, 1/4, 1/8`. -/
def gaps : Fin 3 → ℚ := ![1/2, 1/4, 1/8]

/-- The rational masses `1023/2048, 1/1024, 1023/2048`. -/
def weights : Fin 3 → ℚ := ![1023/2048, 1/1024, 1023/2048]

/-- The band of each gap; also the list of occupied bands. -/
def labels : Fin 3 → ℕ := ![0, 1, 2]

theorem gaps_valid : ∀ i, 0 < gaps i ∧ gaps i ≤ 1/2 := by
  norm_num [gaps, Fin.forall_fin_succ]

theorem weights_positive : ∀ i, 0 < weights i := by
  norm_num [weights, Fin.forall_fin_succ]

theorem weights_nonneg : ∀ i, 0 ≤ weights i := fun i => (weights_positive i).le

theorem weights_sum : ∑ i, weights i = 1 := by
  norm_num [weights, Fin.sum_univ_succ]

theorem labels_injective : Function.Injective labels := by
  intro i j h
  fin_cases i <;> fin_cases j <;> norm_num [labels] at *

theorem labels_valid : ∀ i, inBand (gaps i) (labels i) = true := by
  norm_num [gaps, labels, inBand, Fin.forall_fin_succ]

theorem labels_cover : ∀ i, ∃ j, inBand (gaps i) (labels j) = true :=
  fun i => ⟨i, labels_valid i⟩

/-- The capped objective of the hard mask `s`, as a checker expression. -/
def J (s : Fin 3 → Bool) : ℝ :=
  (objectiveExpr gaps weights (fractions s) labels (1/4) 1048576).eval

theorem J_nonneg (s : Fin 3 → Bool) : 0 ≤ J s :=
  objectiveExpr_nonneg _ _ _ _ _ _ (by norm_num) weights_nonneg (fractions_valid s)

theorem atoms_eq : atoms = points gaps gaps_valid := by
  funext i
  fin_cases i <;> apply Subtype.ext <;> norm_num [atoms, points, gaps]

theorem masses_eq (i : Fin 3) : ENNReal.ofReal (masses i) = ENNReal.ofReal (weights i : ℝ) := by
  fin_cases i <;> norm_num [masses, weights]

theorem law_eq : law = atomicMeasure (points gaps gaps_valid) weights := by
  simp only [law, atomicMeasure, atoms_eq, masses_eq]

theorem retained_eq (s : Fin 3 → Bool) :
    retained s = atomicMeasure (points gaps gaps_valid) (fun i => weights i * fractions s i) := by
  unfold retained atomicMeasure
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [atoms_eq]
  cases h : s i <;> simp [fractions, h, masses_eq]

theorem retained_le (s : Fin 3 → Bool) : retained s ≤ law := by
  rw [retained_eq, law_eq]
  exact selected_le _ _ _ weights_nonneg (fractions_valid s)

theorem sqrt_budget : Real.sqrt 1048576 = 1024 := by
  rw [show (1048576 : ℝ) = 1024^2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

/-- The capped inner cost of a hard mask is the checker expression. -/
theorem capped_eq (s : Fin 3 → Bool) :
    min (ENNReal.ofReal (1/4)) (selectionObjective law (1/4) 1048576 (retained s)) =
      ENNReal.ofReal (J s) := by
  have h := capped_objective_eq gaps weights (fractions s) labels (1/4) 1048576 gaps_valid
    weights_nonneg (fractions_valid s) (by norm_num) (by norm_num) labels_injective labels_cover
  rw [← retained_eq, ← law_eq] at h
  have h1 : ((1/4 : ℚ) : ℝ) = 1/4 := by norm_num
  have h2 : ((1048576 : ℚ) : ℝ) = 1048576 := by norm_num
  rw [h1, h2] at h
  exact h

/-- Below the cap, the inner cost of a hard mask is the checker expression. -/
theorem objective_eq (s : Fin 3 → Bool) (hs : J s < 1/4) :
    selectionObjective law (1/4) 1048576 (retained s) = ENNReal.ofReal (J s) := by
  have h := capped_eq s
  rcases le_total (ENNReal.ofReal (1/4)) (selectionObjective law (1/4) 1048576 (retained s)) with
    hle | hle
  · rw [min_eq_left hle] at h
    have := (ENNReal.ofReal_eq_ofReal_iff (by norm_num) (J_nonneg s)).1 h
    linarith
  · rw [min_eq_right hle] at h
    exact h

theorem objective_toReal (s : Fin 3 → Bool) (hs : J s < 1/4) :
    (selectionObjective law (1/4) 1048576 (retained s)).toReal = J s := by
  rw [objective_eq s hs, ENNReal.toReal_ofReal (J_nonneg s)]

/-- The original functional is attained by a hard mask (bandwise suffix theorem). -/
theorem selection_attained : ∃ s : Fin 3 → Bool, (selection law (1/4) 1048576).toReal = J s := by
  obtain ⟨s, -, hs⟩ := suffix_attains gaps weights labels labels (1/4) 1048576 gaps_valid
    weights_positive weights_sum labels_injective labels_cover labels_valid
    (by norm_num) (by norm_num) (by norm_num)
  rw [← law_eq] at hs
  have h1 : ((1/4 : ℚ) : ℝ) = 1/4 := by norm_num
  have h2 : ((1048576 : ℚ) : ℝ) = 1048576 := by norm_num
  rw [h1, h2] at hs
  exact ⟨s, hs⟩

/-- Every restriction of the law is the hard retained part of a mask. -/
theorem restrict_eq (S : Set Gap) :
    ∃ m : Fin 3 → Bool, law.restrict S = retained m ∧ ∀ i, (m i = true ↔ atoms i ∈ S) := by
  classical
  refine ⟨fun i => decide (atoms i ∈ S), ?_, fun i => by simp⟩
  rw [law_eq, atomicMeasure_restrict, retained_eq]
  congr 1
  funext i
  rw [← atoms_eq]
  by_cases h : atoms i ∈ S <;> simp [h, fractions]

/-- No interval of reals cuts out the optimal mask on the three atoms. -/
theorem optimalMask_not_interval :
    ¬ ∃ I : Set ℝ, I.OrdConnected ∧ ∀ i, (optimalMask i = true ↔ (atoms i : ℝ) ∈ I) := by
  rintro ⟨I, hI, h⟩
  have h0 : (1/2 : ℝ) ∈ I := by
    have := (h 0).1 (by simp [optimalMask])
    simpa [atoms] using this
  have h2 : (1/8 : ℝ) ∈ I := by
    have := (h 2).1 (by simp [optimalMask])
    simpa [atoms] using this
  have h1 : (1/4 : ℝ) ∈ I := hI.out h2 h0 ⟨by norm_num, by norm_num⟩
  have := (h 1).2 (by simpa [atoms] using h1)
  simp [optimalMask] at this

end ThresholdHC.NonintervalSelection
