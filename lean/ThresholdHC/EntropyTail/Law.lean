import ThresholdHC.EntropyTail.Upper
import ThresholdHC.EntropyTail.Lower

/-! The universal two-sided entropy-tail law for arbitrary probability laws. -/
noncomputable section
namespace ThresholdHC.EntropyTail

theorem entropy_tail_law : EntropyTailLawStatement := by
  obtain ⟨c,hc,hl⟩ := entropy_tail_lower
  obtain ⟨C,hC,hu⟩ := entropy_tail_upper
  refine ⟨c,C,hc,hC,?_⟩
  intro ρ B hρ hρ4 hB μ _
  exact ⟨hl ρ B hρ hρ4 hB μ,hu ρ B hρ hρ4 hB μ⟩

end ThresholdHC.EntropyTail
