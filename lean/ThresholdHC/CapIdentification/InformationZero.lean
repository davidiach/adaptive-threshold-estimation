import ThresholdHC.CapIdentification.CountMatching
import ThresholdHC.StoppingProgram.FullCapFlow

/-! The stopping information ratio is zero exactly for the moment-matching
pairs. A deterministic full-depth flow witnesses strict positivity otherwise. -/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators

namespace ThresholdHC.CapIdentification
open ThresholdHC.Tier6 (Gap SignLaw)
open ThresholdHC.StoppingProgram

theorem count_match_of_terminal (μ : Measure Gap) [IsFiniteMeasure μ]
    (qH qL : SignLaw) (N : ℕ)
    (h : ∀ s : CountState N, s.1.val = N → countCoefficient μ qH s = countCoefficient μ qL s) :
    CountMatch μ qH qL N := by
  apply (odd_moments_iff_count_match μ qH qL N).mp
  apply (odd_moments_iff_prefix_contrast μ qH qL N).mpr
  intro k hk
  let s : CountState N := ⟨⟨N,by omega⟩,⟨k,by change k < N+1; omega⟩⟩
  exact (countCoefficient_eq_iff_contrast μ qH qL s).mp (h s rfl)

theorem perspective_zero_left (y : ℝ) : perspective 0 y = 0 := by
  by_cases hy : 0 < y <;> simp [perspective,hy]

theorem perspective_strict_pos {x y : ℝ} (hx : x ≠ 0) : 0 < perspective x y := by
  by_cases hy : 0 < y
  · rw [perspective_pos hy]
    exact ENNReal.ofReal_pos.mpr (div_pos (sq_pos_of_ne_zero hx) hy)
  · simp [perspective,hy,hx]

theorem informationRatio_zero_of_count_match (μ : Measure Gap) (N : ℕ) (Q : FourPriors)
    (h : CountMatch μ Q.high Q.low N) : informationRatio μ N Q = 0 := by
  unfold informationRatio
  apply le_antisymm ?_ bot_le
  refine iSup_le (fun f => iSup_le (fun _ => iSup_le (fun _ => ?_)))
  have hI : flowInformation μ Q f = 0 := by
    unfold flowInformation
    apply Finset.sum_eq_zero
    intro s _
    rw [h s,sub_self,perspective_zero_left,mul_zero]
  rw [hI,ENNReal.zero_div]
  exact le_rfl

theorem informationRatio_pos_of_not_count_match (μ : Measure Gap) [IsProbabilityMeasure μ]
    (N : ℕ) (Q : FourPriors) (h : ¬CountMatch μ Q.high Q.low N) : 0 < informationRatio μ N Q := by
  classical
  have hN : 0 < N := by
    by_contra hn
    have he : N = 0 := by omega
    apply h
    intro s
    have hs : s = rootState N := state_eq_root s (by have hh := s.1.isLt; omega)
    rw [hs,countCoefficient_root,countCoefficient_root]
  have ht : ∃ s : CountState N, s.1.val = N ∧ countCoefficient μ Q.high s ≠ countCoefficient μ Q.low s := by
    by_contra hn
    push Not at hn
    exact h (count_match_of_terminal μ Q.high Q.low N hn)
  obtain ⟨s,hs,hd⟩ := ht
  have hp := perspective_strict_pos (y := countCoefficient μ Q.variance s) (sub_ne_zero.mpr hd)
  have hI : 0 < flowInformation μ Q (fullCapFlow N) := by
    apply lt_of_lt_of_le hp
    have hterm := Finset.single_le_sum (s := Finset.univ)
      (f := fun t : CountState N => ENNReal.ofReal ((fullCapFlow N).stopWeight t)*perspective
        (countCoefficient μ Q.high t-countCoefficient μ Q.low t) (countCoefficient μ Q.variance t))
      (fun _ _ => bot_le) (Finset.mem_univ s)
    simpa only [flowInformation,fullCapFlow,hs,ite_true,ENNReal.ofReal_one,one_mul] using hterm
  have hdiv : 0 < flowInformation μ Q (fullCapFlow N)/
      ENNReal.ofReal (countMean μ Q.work (fullCapFlow N).continueWeight) := by
    exact ENNReal.div_pos hI.ne' ENNReal.ofReal_ne_top
  exact hdiv.trans_le (le_iSup_of_le (fullCapFlow N)
    (le_iSup_of_le (fullCapFlow_cone hN) (le_iSup_of_le (fullCapFlow_intensity hN) le_rfl)))

theorem informationRatio_zero_iff_moments (μ : Measure Gap) [IsProbabilityMeasure μ]
    (N : ℕ) (Q : FourPriors) : informationRatio μ N Q = 0 ↔ OddMomentMatch μ Q.high Q.low N := by
  rw [odd_moments_iff_count_match]
  constructor
  · intro hz
    by_contra hn
    have hp := informationRatio_pos_of_not_count_match μ N Q hn
    rw [hz] at hp
    exact (lt_irrefl _ hp)
  · exact informationRatio_zero_of_count_match μ N Q

end ThresholdHC.CapIdentification
