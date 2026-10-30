import ThresholdHC.EntropyTail.SingleAtom

/-! The functional is positive and finite on every admissible input, and strictly
below the trivial rate on a point mass with a large budget. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.EntropyTail
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo

theorem entropy_tail_nonvacuity : EntropyTailNonvacuityStatement := by
  refine ⟨fun ρ B hρ _ hB μ _ => ⟨?_, ?_⟩, ?_⟩
  · have hsB : 0 < Real.sqrt B := Real.sqrt_pos.2 hB
    have hsr : 0 < Real.sqrt ρ := Real.sqrt_pos.2 hρ
    have hh : 0 < 2 * (1 / Real.sqrt B) := mul_pos two_pos (one_div_pos.2 hsB)
    have hpos : 0 < ENNReal.ofReal
        (min (2 * (1 / Real.sqrt B) * Real.sqrt ρ) (min 1 (2 * (1 / Real.sqrt B)))) :=
      ENNReal.ofReal_pos.2 (lt_min (mul_pos hh hsr) (lt_min one_pos hh))
    unfold selection
    exact lt_min (ENNReal.ofReal_pos.2 hρ) (hpos.trans_le (iInf_objective_lower μ hρ.le B))
  · exact (selection_le_rho μ ρ B).trans_lt ENNReal.ofReal_lt_top
  · refine ⟨Measure.dirac ⟨1/2, by norm_num, le_rfl⟩, inferInstance, 1/4, 64,
      by norm_num, le_rfl, by norm_num, ?_⟩
    rw [single_atom (1/4) 64 (by norm_num) le_rfl (by norm_num),
      ENNReal.ofReal_lt_ofReal_iff (show (0 : ℝ) < 1/4 by norm_num)]
    unfold aboveTwoRate
    have h64 : Real.sqrt 64 = 8 := by
      rw [show (64 : ℝ) = 8^2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    have h14 : Real.sqrt (1/4) = 1/2 := by
      rw [show (1/4 : ℝ) = (1/2)^2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    rw [h64, h14, min_lt_iff]
    right
    norm_num

end ThresholdHC.EntropyTail
