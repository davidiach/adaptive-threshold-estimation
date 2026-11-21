import ThresholdHC.BiasSubtraction.Witness

/-! The remark after Proposition prop:psi-null: the coefficient four of the bias
subtraction cannot be reduced, whatever the denominator constant. -/
noncomputable section
namespace ThresholdHC.BiasSubtraction

theorem bias_subtraction : BiasSubtractionStatement := by
  refine ⟨remarkBias_range, fun c hc K hK => ?_⟩
  obtain ⟨δ, hδ, h⟩ := remark_bound_gt c hc K hK
  exact ⟨δ, hδ, fun d hd => not_obstruction_of_gt d _ (h d hd)⟩

end ThresholdHC.BiasSubtraction
