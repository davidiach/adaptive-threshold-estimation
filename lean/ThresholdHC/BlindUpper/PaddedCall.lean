import ThresholdHC.BlindUpper.CallLaw

noncomputable section
namespace ThresholdHC.BlindUpper
open MeasureTheory ThresholdHC.CriticalEntropy ThresholdHC.Uniform713
open ThresholdHC.Tier6 ThresholdHC.ObservableSimulation
open scoped ENNReal

/-- One unused flip is taken when the geometric level exceeds the cutoff.
Every call therefore advances the observed history, with the same output. -/
def paddedCutoffCost (L : ℕ) (z : ℕ × (ℕ → Bool)) : ℕ := max 1 (cutoffCost L z)

theorem measurable_paddedCutoffCost (L : ℕ) : Measurable (paddedCutoffCost L) :=
  measurable_const.max (measurable_cutoffCost L)

theorem paddedCutoffCost_bounds (L : ℕ) (z : ℕ × (ℕ → Bool)) :
    1 ≤ paddedCutoffCost L z ∧ paddedCutoffCost L z ≤ 2^L := by
  refine ⟨le_max_left _ _,max_le ?_ (cutoffCost_le L z)⟩
  have h := Nat.two_pow_pos L
  omega

theorem paddedCutoff_prefix_ext (L l : ℕ) (ω ω' : ℕ → Bool)
    (h : Tier2.tapePrefix (paddedCutoffCost L (l,ω)) ω =
      Tier2.tapePrefix (paddedCutoffCost L (l,ω)) ω') :
    paddedCutoffCost L (l,ω') = paddedCutoffCost L (l,ω) ∧
      cutoffValue L (l,ω') = cutoffValue L (l,ω) := by
  have hl : cutoffCost L (l,ω) ≤ paddedCutoffCost L (l,ω) := le_max_right _ _
  obtain ⟨hc,hv⟩ := cutoff_prefix_ext L l ω ω' (prefix_eq_restrict h hl)
  exact ⟨congrArg (max 1) hc,hv⟩

def paddedCutoffProcedure (L : ℕ) : StoppedProcedure ℕ ℝ :=
  finiteStoppedProcedure (paddedCutoffCost L) (cutoffValue L)
    (measurable_paddedCutoffCost L) (measurable_cutoffValue L) (paddedCutoff_prefix_ext L)

theorem callScale_one_le (L : ℕ) (d : Gap) : 1 ≤ callScale L d := by
  apply le_min
  · exact Real.one_le_sqrt.mpr (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  · exact (one_le_inv₀ d.property.1).mpr (by have hd := d.property.2; linarith)

theorem callScale_integral_one_le (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] :
    1 ≤ ∫ d, callScale L d ∂μ := by
  have h := integral_mono (integrable_const (1 : ℝ)) (callScale_integrable L μ) (callScale_one_le L)
  simpa using h

theorem paddedCutoff_cost_integrable (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    Integrable (fun z => (paddedCutoffCost L z : ℝ)) (callMeasure μ q) := by
  have hm : Measurable (fun z => (paddedCutoffCost L z : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (measurable_paddedCutoffCost L)
  apply Integrable.of_bound hm.aestronglyMeasurable ((2 : ℝ)^L)
  exact ae_of_all _ (fun z => by
    rw [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast (paddedCutoffCost_bounds L z).2)

theorem paddedCutoff_work_lower (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    1 ≤ ∫ z, (paddedCutoffCost L z : ℝ) ∂callMeasure μ q := by
  have h := integral_mono (integrable_const (1 : ℝ)) (paddedCutoff_cost_integrable L μ q)
    (fun z => by exact_mod_cast (paddedCutoffCost_bounds L z).1)
  simpa using h

theorem paddedCutoff_work_upper (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    (∫ z, (paddedCutoffCost L z : ℝ) ∂callMeasure μ q) ≤ 150*∫ d, callScale L d ∂μ := by
  have hcost : ∀ z : ℕ × (ℕ → Bool), (paddedCutoffCost L z : ℝ) ≤ (cutoffCost L z : ℝ)+1 := by
    intro z
    have hnat : paddedCutoffCost L z ≤ cutoffCost L z+1 := max_le (by omega) (by omega)
    exact_mod_cast hnat
  have h := integral_mono (paddedCutoff_cost_integrable L μ q)
    ((cutoff_call_cost_integrable L μ q).add (integrable_const 1)) hcost
  change (∫ z, (paddedCutoffCost L z : ℝ) ∂callMeasure μ q) ≤
    (∫ z, (cutoffCost L z : ℝ)+1 ∂callMeasure μ q) at h
  rw [integral_add (cutoff_call_cost_integrable L μ q) (integrable_const 1)] at h
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul] at h
  have hbase := cutoff_call_work_real_le L μ q
  have hA := callScale_integral_one_le L μ
  linarith

end ThresholdHC.BlindUpper
