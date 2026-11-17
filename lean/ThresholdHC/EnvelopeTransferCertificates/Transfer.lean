import ThresholdHC.EnvelopeTransferCertificates.Rounding

namespace ThresholdHC.EnvelopeTransferCertificates
open ThresholdHC.DeterministicCertificates

/-- Arithmetic output check; the input enclosure and law premises stay explicit. -/
def transferCheck (input output : Interval) (r η ρ : ℚ) : Bool :=
  decide (output.lower ≤ max 0 (input.lower-η) ∧ min ρ (r*input.upper+η) ≤ output.upper)

theorem transferCheck_sound {input output : Interval} {r η ρ x : ℚ}
    (h : transferCheck input output r η ρ = true)
    (hx : max 0 (input.lower-η) ≤ x ∧ x ≤ min ρ (r*input.upper+η)) :
    output.lower ≤ x ∧ x ≤ output.upper := by
  simp only [transferCheck, decide_eq_true_eq] at h
  exact ⟨h.1.trans hx.1, hx.2.trans h.2⟩

open MeasureTheory
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTail

/-- A conditional certificate about original K, not an assertion of its input hypotheses. -/
theorem transfer_original (μ μ₀ : Measure Gap) [IsProbabilityMeasure μ] [IsProbabilityMeasure μ₀]
    (T : Gap → Gap) (hm : Measurable T) (r η ρ B : ℚ) (hr : 1 ≤ r)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4) (hB : 0 < B)
    (hη : tvDist μ μ₀ / 2 ≤ (η:ℝ))
    (hd : ∀ d : Gap, (d:ℝ) ≤ (T d:ℝ) ∧ (T d:ℝ) ≤ (r:ℝ)*(d:ℝ))
    (hb : ∀ j, T ⁻¹' band j = band j)
    (input output : Interval) (hi : Contains input (selection (μ₀.map T) (ρ:ℝ) (B:ℝ)).toReal)
    (hc : transferCheck input output r η ρ = true) :
    Contains output (selection μ (ρ:ℝ) (B:ℝ)).toReal := by
  have hρ1' : (ρ:ℝ) ≤ 1/4 := by
    have h : (ρ:ℝ) ≤ ((1/4:ℚ):ℝ) := Rat.cast_le.mpr hρ1
    norm_num at h ⊢; exact h
  have h := ThresholdHC.SelectionStability.transfer_enclosure μ μ₀ T hm
    (by exact_mod_cast hr) (by exact_mod_cast hρ) hρ1' (by exact_mod_cast hB) hη hd hb hi.1 hi.2
  simp only [transferCheck, decide_eq_true_eq] at hc
  constructor
  · have hl : (output.lower:ℝ) ≤ max 0 ((input.lower:ℝ)-(η:ℝ)) := by exact_mod_cast hc.1
    exact hl.trans h.1
  · exact h.2.trans (by exact_mod_cast hc.2)

end ThresholdHC.EnvelopeTransferCertificates
