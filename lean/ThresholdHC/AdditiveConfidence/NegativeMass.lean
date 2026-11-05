import ThresholdHC.AdditiveConfidence.PositiveMass

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace ThresholdHC.AdditiveConfidence
open ThresholdHC.Tier6

def complementSign (q : SignLaw) : SignLaw :=
  ⟨fun d => 1-q.val d, measurable_const.sub q.property.1,
    fun d => ⟨sub_nonneg.mpr (q.property.2 d).2,sub_le_self _ (q.property.2 d).1⟩⟩

theorem positive_complement_sum (μ : Measure Gap) (q : SignLaw) :
    positiveMeasure μ q+positiveMeasure μ (complementSign q) = μ := by
  have hm : Measurable (fun d => ENNReal.ofReal (q.val d)) :=
    ENNReal.measurable_ofReal.comp q.property.1
  rw [positiveMeasure,positiveMeasure,← withDensity_add_left hm]
  have he : (fun d => ENNReal.ofReal (q.val d)+ENNReal.ofReal ((complementSign q).val d)) =
      (fun _ => (1 : ℝ≥0∞)) := by
    funext d
    rw [← ENNReal.ofReal_add (q.property.2 d).1 ((complementSign q).property.2 d).1]
    simp [complementSign]
  change μ.withDensity (fun d => ENNReal.ofReal (q.val d)+ENNReal.ofReal ((complementSign q).val d)) = μ
  rw [he,withDensity_const,one_smul]

theorem GapMixture.mixedSign_complement {I : Type} [Fintype I] {μ : Measure Gap}
    [IsProbabilityMeasure μ] (M : GapMixture I μ) (q : I → SignLaw)
    (hq : ∀ i d, (q i).val d ≤ 1/2) :
    positiveMeasure μ (complementSign (M.mixedSign q)) =
      M.residual+∑ i, M.weight i • positiveMeasure (M.law i) (complementSign (q i)) := by
  apply (Measure.add_right_inj (M.positiveMass q) _ _).mp
  calc
    _ = μ := by rw [← M.mixedSign_density q hq,positive_complement_sum]
    _ = M.residual+∑ i, M.weight i • M.law i := M.eq_measure
    _ = _ := by
      simp only [GapMixture.positiveMass,add_left_comm,
        ← Finset.sum_add_distrib,← smul_add,positive_complement_sum]

end ThresholdHC.AdditiveConfidence
