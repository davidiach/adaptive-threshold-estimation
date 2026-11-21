import ThresholdHC.EntropyTailForms.Specification
import ThresholdHC.EntropyTail.HardSelection

/-! The fixed-core split behind form (62) and the equality of the selection and
three-piece infima. At fixed `σ` the remainder `ν = μ - σ` splits into the
magnitudes `d ≥ h`, which pay `h/d`, and the magnitudes `d < h`, which pay `1`;
no other split of `ν` is cheaper. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.EntropyTailForms
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTail

theorem measurable_inverseWeight : Measurable fun d : Gap => ENNReal.ofReal ((d : ℝ)⁻¹) :=
  measurable_subtype_coe.inv.ennreal_ofReal

theorem ofReal_mul_inverseMass (τ : Measure Gap) {h : ℝ} (hh : 0 ≤ h) :
    ENNReal.ofReal h * inverseMass τ = ∫⁻ d, ENNReal.ofReal (h / (d : ℝ)) ∂τ := by
  unfold inverseMass
  rw [← lintegral_const_mul _ measurable_inverseWeight]
  refine lintegral_congr fun d => ?_
  rw [← ENNReal.ofReal_mul hh, ← div_eq_mul_inv]

theorem tailCost_add (τ ζ : Measure Gap) (h : ℝ) :
    tailCost (τ + ζ) h = tailCost τ h + tailCost ζ h :=
  lintegral_add_measure _ _ _

/-- Any split `τ + ζ` of the remainder costs at least the truncated cost. -/
theorem tailCost_add_le (τ ζ : Measure Gap) {h : ℝ} (hh : 0 ≤ h) :
    tailCost (τ + ζ) h ≤ ζ Set.univ + ENNReal.ofReal h * inverseMass τ := by
  rw [tailCost_add, add_comm]
  refine add_le_add (tailCost_le_mass ζ h) ?_
  rw [ofReal_mul_inverseMass τ hh]
  exact lintegral_mono fun d => ENNReal.ofReal_le_ofReal (min_le_right _ _)

theorem measurableSet_ge_gap (h : ℝ) : MeasurableSet {d : Gap | h ≤ (d : ℝ)} :=
  measurableSet_le measurable_const measurable_subtype_coe

theorem measurableSet_lt_gap (h : ℝ) : MeasurableSet {d : Gap | (d : ℝ) < h} :=
  measurableSet_lt measurable_subtype_coe measurable_const

theorem compl_ge_gap (h : ℝ) : {d : Gap | h ≤ (d : ℝ)}ᶜ = {d : Gap | (d : ℝ) < h} := by
  ext d
  simp [not_le]

theorem split_add (ν : Measure Gap) (h : ℝ) :
    ν.restrict {d : Gap | h ≤ (d : ℝ)} + ν.restrict {d : Gap | (d : ℝ) < h} = ν := by
  rw [← compl_ge_gap]
  exact Measure.restrict_add_restrict_compl (measurableSet_ge_gap h)

/-- The cheapest split: `d ≥ h` pays `h/d`, `d < h` pays `1`. -/
theorem tailCost_split_eq (ν : Measure Gap) {h : ℝ} (hh : 0 ≤ h) :
    tailCost ν h = ν.restrict {d : Gap | (d : ℝ) < h} Set.univ +
      ENNReal.ofReal h * inverseMass (ν.restrict {d : Gap | h ≤ (d : ℝ)}) := by
  have hν : tailCost ν h = tailCost (ν.restrict {d : Gap | h ≤ (d : ℝ)}) h +
      tailCost (ν.restrict {d : Gap | (d : ℝ) < h}) h := by
    rw [← tailCost_add, split_add]
  rw [hν, ofReal_mul_inverseMass _ hh, Measure.restrict_apply_univ, add_comm]
  congr 1
  · rw [← setLIntegral_one]
    refine setLIntegral_congr_fun (measurableSet_lt_gap h) fun d hd => ?_
    have hd' : (d : ℝ) < h := hd
    rw [min_eq_left ((one_le_div d.2.1).2 hd'.le), ENNReal.ofReal_one]
  · refine setLIntegral_congr_fun (measurableSet_ge_gap h) fun d hd => ?_
    have hd' : h ≤ (d : ℝ) := hd
    rw [min_eq_right ((div_le_one d.2.1).2 hd')]

/-- The fixed-core split: the infimum over splits of the remainder is the truncated cost. -/
theorem iInf_split_eq_tailCost : FixedCoreSplitStatement := by
  intro ν h hh
  refine le_antisymm ?_ ?_
  · rw [tailCost_split_eq ν hh]
    exact iInf_le_of_le (ν.restrict {d : Gap | h ≤ (d : ℝ)})
      (iInf_le_of_le (ν.restrict {d : Gap | (d : ℝ) < h}) (iInf_le_of_le (split_add ν h) le_rfl))
  · refine le_iInf fun τ => le_iInf fun ζ => le_iInf fun hτζ => ?_
    rw [← hτζ]
    exact tailCost_add_le τ ζ hh

theorem budgetScale_nonneg (B : ℝ) : 0 ≤ 1 / Real.sqrt B := by positivity

/-- A decomposition `σ + τ + ζ = μ` of a finite law has `σ ≤ μ` and remainder `τ + ζ`. -/
theorem core_le_of_add {μ σ τ ζ : Measure Gap} [IsFiniteMeasure μ] (hsum : σ + τ + ζ = μ) :
    σ ≤ μ ∧ μ - σ = τ + ζ := by
  have hσ : σ ≤ μ := by
    rw [← hsum, add_assoc]
    exact Measure.le_add_right le_rfl
  have : IsFiniteMeasure σ := isFiniteMeasure_of_le μ hσ
  refine ⟨hσ, ?_⟩
  rw [← hsum, add_assoc, add_comm σ, Measure.add_sub_cancel]

theorem selectionObjective_le_threePiece {μ σ τ ζ : Measure Gap} [IsFiniteMeasure μ]
    (hsum : σ + τ + ζ = μ) (ρ B : ℝ) :
    selectionObjective μ ρ B σ ≤ threePieceObjective ρ B σ τ ζ := by
  obtain ⟨-, hres⟩ := core_le_of_add hsum
  unfold selectionObjective threePieceObjective
  rw [hres]
  refine (add_le_add le_rfl (tailCost_add_le τ ζ (budgetScale_nonneg B))).trans (le_of_eq ?_)
  ring

/-- At fixed `σ ≤ μ` the cheapest split of the remainder attains the selection objective. -/
theorem threePiece_attained {μ σ : Measure Gap} [IsFiniteMeasure μ] (hσ : σ ≤ μ) (ρ B : ℝ) :
    σ + (μ - σ).restrict {d : Gap | 1 / Real.sqrt B ≤ (d : ℝ)} +
        (μ - σ).restrict {d : Gap | (d : ℝ) < 1 / Real.sqrt B} = μ ∧
      threePieceObjective ρ B σ ((μ - σ).restrict {d : Gap | 1 / Real.sqrt B ≤ (d : ℝ)})
          ((μ - σ).restrict {d : Gap | (d : ℝ) < 1 / Real.sqrt B}) =
        selectionObjective μ ρ B σ := by
  have : IsFiniteMeasure σ := isFiniteMeasure_of_le μ hσ
  constructor
  · rw [add_assoc, split_add, add_comm, Measure.sub_add_cancel_of_le hσ]
  · unfold threePieceObjective selectionObjective
    rw [tailCost_split_eq (μ - σ) (budgetScale_nonneg B)]
    ring

/-- (61) = (62) before the cap. -/
theorem iInf_selection_eq_threePiece : ThreePieceInfStatement := by
  intro μ _ ρ B
  refine le_antisymm ?_ ?_
  · refine le_iInf fun σ => le_iInf fun τ => le_iInf fun ζ => le_iInf fun hsum => ?_
    exact (iInf_le_of_le σ (iInf_le _ (core_le_of_add hsum).1)).trans
      (selectionObjective_le_threePiece hsum ρ B)
  · refine le_iInf₂ fun σ hσ => ?_
    obtain ⟨hsum, heq⟩ := threePiece_attained hσ ρ B
    rw [← heq]
    exact iInf_le_of_le σ (iInf_le_of_le _ (iInf_le_of_le _ (iInf_le_of_le hsum le_rfl)))

/-- (61) = (62) with the cap. -/
theorem selection_eq_threePieceSelection : ThreePieceFormStatement := by
  intro μ _ ρ B
  unfold selection threePieceSelection
  rw [iInf_selection_eq_threePiece μ ρ B]

end ThresholdHC.EntropyTailForms
