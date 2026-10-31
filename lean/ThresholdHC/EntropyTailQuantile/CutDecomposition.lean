import ThresholdHC.EntropyTailQuantile.QuantileSplit

/-! Positive linear fractional cuts. They decompose any submeasure using the
same threshold and boundary fraction, without introducing latent labels. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace ThresholdHC.EntropyTailQuantile
open ThresholdHC.Tier6

def lowerCut (t r : ℝ) (σ : Measure Gap) : Measure Gap :=
  σ.restrict {d : Gap | (d:ℝ) < t} + ENNReal.ofReal r • σ.restrict {d : Gap | (d:ℝ) = t}

def upperCut (t r : ℝ) (σ : Measure Gap) : Measure Gap :=
  σ.restrict {d : Gap | t < (d:ℝ)} + ENNReal.ofReal (1-r) • σ.restrict {d : Gap | (d:ℝ) = t}

theorem lowerCut_add_upperCut (t : ℝ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (σ : Measure Gap) : lowerCut t r σ + upperCut t r σ = σ := by
  have hc : ENNReal.ofReal r + ENNReal.ofReal (1-r) = 1 := by
    rw [← ENNReal.ofReal_add hr0 (sub_nonneg.mpr hr1)]
    simp
  have hd₁ : Disjoint {d : Gap | (d:ℝ) < t} {d : Gap | (d:ℝ) = t} := by
    rw [Set.disjoint_left]
    intro d h₁ h₂
    exact (ne_of_lt h₁) h₂
  have hd₂ : Disjoint ({d : Gap | (d:ℝ) < t} ∪ {d : Gap | (d:ℝ) = t})
      {d : Gap | t < (d:ℝ)} := by
    rw [Set.disjoint_left]
    rintro d (hlt | heq) hgt
    · exact (lt_asymm (show (d:ℝ) < t from hlt)) hgt
    · exact (ne_of_gt hgt) heq
  have hu : ({d : Gap | (d:ℝ) < t} ∪ {d : Gap | (d:ℝ) = t}) ∪
      {d : Gap | t < (d:ℝ)} = univ := by
    ext d
    simp only [mem_union, mem_ofPred_eq, mem_univ, iff_true]
    rcases lt_trichotomy (d:ℝ) t with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  calc
    lowerCut t r σ + upperCut t r σ =
        σ.restrict {d : Gap | (d:ℝ) < t} +
          (ENNReal.ofReal r + ENNReal.ofReal (1-r)) • σ.restrict {d : Gap | (d:ℝ) = t} +
            σ.restrict {d : Gap | t < (d:ℝ)} := by
      unfold lowerCut upperCut
      rw [add_smul]
      abel
    _ = σ := by
      rw [hc, one_smul, ← Measure.restrict_union hd₁
        (measurableSet_eq_fun measurable_subtype_coe measurable_const),
        ← Measure.restrict_union hd₂ (measurableSet_lt measurable_const measurable_subtype_coe),
        hu, Measure.restrict_univ]

theorem lowerCut_le (t : ℝ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (σ : Measure Gap) :
    lowerCut t r σ ≤ σ := by
  calc
    _ ≤ lowerCut t r σ + upperCut t r σ := le_add_of_nonneg_right bot_le
    _ = _ := lowerCut_add_upperCut t hr0 hr1 σ

theorem upperCut_le (t : ℝ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (σ : Measure Gap) :
    upperCut t r σ ≤ σ := by
  calc
    _ ≤ lowerCut t r σ + upperCut t r σ := le_add_of_nonneg_left bot_le
    _ = _ := lowerCut_add_upperCut t hr0 hr1 σ

theorem lowerCut_add (t r : ℝ) (σ τ : Measure Gap) :
    lowerCut t r (σ+τ) = lowerCut t r σ + lowerCut t r τ := by
  simp only [lowerCut, Measure.restrict_add, smul_add]
  abel

theorem upperCut_add (t r : ℝ) (σ τ : Measure Gap) :
    upperCut t r (σ+τ) = upperCut t r σ + upperCut t r τ := by
  simp only [upperCut, Measure.restrict_add, smul_add]
  abel

theorem lowerCut_mono (t r : ℝ) {σ τ : Measure Gap} (h : σ ≤ τ) :
    lowerCut t r σ ≤ lowerCut t r τ := by
  apply add_le_add (Measure.restrict_mono le_rfl h)
  intro s
  simp only [Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul_right (Measure.restrict_mono le_rfl h s) _

theorem upperCut_mono (t r : ℝ) {σ τ : Measure Gap} (h : σ ≤ τ) :
    upperCut t r σ ≤ upperCut t r τ := by
  apply add_le_add (Measure.restrict_mono le_rfl h)
  intro s
  simp only [Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul_right (Measure.restrict_mono le_rfl h s) _

theorem upperCut_support (t r : ℝ) (σ : Measure Gap) :
    ∀ᵐ d : Gap ∂upperCut t r σ, t ≤ (d:ℝ) := by
  rw [upperCut, ae_add_measure_iff]
  constructor
  · exact (ae_restrict_mem (measurableSet_lt measurable_const measurable_subtype_coe)).mono
      (fun _ hd => hd.le)
  · apply Measure.ae_smul_measure
    exact (ae_restrict_mem (measurableSet_eq_fun measurable_subtype_coe measurable_const)).mono
      (fun _ hd => hd.symm.le)

theorem quantileCore_eq_upperCut (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    quantileCore μ ρ = upperCut (quantileThreshold μ ρ) (quantileBoundaryFraction μ ρ) μ := by
  have hr := quantileBoundaryFraction_properties μ hρ hρ1
  have : IsFiniteMeasure (lowerCut (quantileThreshold μ ρ) (quantileBoundaryFraction μ ρ) μ) :=
    isFiniteMeasure_of_le μ (lowerCut_le _ hr.1 hr.2.1 μ)
  change μ - lowerCut (quantileThreshold μ ρ) (quantileBoundaryFraction μ ρ) μ = _
  conv_lhs => lhs; rw [← lowerCut_add_upperCut (quantileThreshold μ ρ) hr.1 hr.2.1 μ]
  rw [add_comm, Measure.add_sub_cancel]

end ThresholdHC.EntropyTailQuantile
