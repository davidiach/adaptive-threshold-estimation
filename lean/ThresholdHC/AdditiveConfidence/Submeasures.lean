import ThresholdHC.AdditiveConfidence.Decomposition

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace ThresholdHC.AdditiveConfidence
open ThresholdHC.Tier6

def normalizedGapLaw (σ : Measure Gap) : Measure Gap := (σ Set.univ)⁻¹ • σ

/-- Normalize finitely many nonzero submeasures and retain their exact residual.
No disjointness of supports is required. -/
def submeasureMixture {I : Type} [Fintype I] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (σ : I → Measure Gap) (hs : (∑ i, σ i) ≤ μ) (hn : ∀ i, σ i Set.univ ≠ 0) :
    GapMixture I μ := by
  have hle (i : I) : σ i ≤ μ :=
    (Finset.single_le_sum (fun j _ => bot_le) (Finset.mem_univ i)).trans hs
  let (i : I) : IsFiniteMeasure (σ i) := isFiniteMeasure_of_le μ (hle i)
  let w := fun i => (σ i Set.univ).toNNReal
  let law := fun i => normalizedGapLaw (σ i)
  have hp (i : I) : IsProbabilityMeasure (law i) := by
    constructor
    change ((σ i Set.univ)⁻¹ • σ i) Set.univ = 1
    rw [Measure.smul_apply,smul_eq_mul,ENNReal.inv_mul_cancel (hn i) (measure_ne_top _ _)]
  have he (i : I) : w i • law i = σ i := by
    change ((σ i Set.univ).toNNReal : ℝ≥0∞) • ((σ i Set.univ)⁻¹ • σ i) = σ i
    rw [ENNReal.coe_toNNReal (measure_ne_top _ _),smul_smul,
      ENNReal.mul_inv_cancel (hn i) (measure_ne_top _ _),one_smul]
  refine {weight := w,law := law,law_probability := hp,residual := μ-∑ i, σ i,eq_measure := ?_}
  simp_rw [he]
  exact (Measure.sub_add_cancel_of_le hs).symm

theorem submeasureMixture_law {I : Type} [Fintype I]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (σ : I → Measure Gap)
    (hs : (∑ i, σ i) ≤ μ) (hn : ∀ i, σ i Set.univ ≠ 0) (i : I) :
    (submeasureMixture μ σ hs hn).law i = normalizedGapLaw (σ i) := rfl

theorem submeasureMixture_weight {I : Type} [Fintype I]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (σ : I → Measure Gap)
    (hs : (∑ i, σ i) ≤ μ) (hn : ∀ i, σ i Set.univ ≠ 0) (i : I) :
    ((submeasureMixture μ σ hs hn).weight i : ℝ) = (σ i).real Set.univ := rfl

end ThresholdHC.AdditiveConfidence
