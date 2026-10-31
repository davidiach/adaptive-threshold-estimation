import ThresholdHC.StoppingProgram.InformationBellman
import ThresholdHC.StoppingProgram.InformationBound
import ThresholdHC.StoppingProgram.FullCapFlow

/-! A singular nonzero prefix contrast makes the actual information ratio
infinite. Otherwise all prefix rewards are finite and Bellman applies. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap)

theorem prefixInformation_finite_of_terminal (μ : Measure Gap) [IsProbabilityMeasure μ]
    (N : ℕ) (Q : FourPriors) (hfin : ∀ k, k ≤ N → prefixInformation μ Q N k ≠ ⊤) :
    ∀ n k, n ≤ N → k ≤ n → prefixInformation μ Q n k ≠ ⊤ := by
  have hdepth : ∀ d n k, n+d = N → k ≤ n → prefixInformation μ Q n k ≠ ⊤ := by
    intro d
    induction d with
    | zero => intro n k hn hk; simp only [Nat.add_zero] at hn; subst n; exact hfin k hk
    | succ d ih =>
      intro n k hn hk
      have hleft := ih (n+1) k (by omega) (by omega)
      have hright := ih (n+1) (k+1) (by omega) (by omega)
      exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hleft,hright⟩)
        (prefixInformation_children μ Q n k hk)
  intro n k hn hk
  exact hdepth (N-n) n k (by omega) hk

theorem prefixInformation_finite_of_ratio {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (Q : FourPriors) (hN : 0 < N) (hK : informationRatio μ N Q ≠ ⊤) :
    ∀ n k, n ≤ N → k ≤ n → prefixInformation μ Q n k ≠ ⊤ := by
  have hI := flowInformation_finite_of_ratio_finite μ Q (fullCapFlow N) (fullCapFlow_cone hN) hK
  apply prefixInformation_finite_of_terminal μ N Q
  intro k hk
  let s : CountState N := ⟨⟨N,by omega⟩,⟨k,by change k < N+1; omega⟩⟩
  have ht : perspective (countCoefficient μ Q.high s-countCoefficient μ Q.low s)
      (countCoefficient μ Q.variance s) ≠ ⊤ := by
    apply ne_top_of_le_ne_top hI
    have hh := Finset.single_le_sum (s := Finset.univ)
      (f := fun t : CountState N => ENNReal.ofReal ((fullCapFlow N).stopWeight t)*perspective
        (countCoefficient μ Q.high t-countCoefficient μ Q.low t) (countCoefficient μ Q.variance t))
      (fun _ _ => bot_le) (Finset.mem_univ s)
    simpa only [flowInformation,fullCapFlow,show s.1.val = N from rfl,ite_true,ENNReal.ofReal_one,one_mul] using hh
  rw [countInformation_eq] at ht
  change ENNReal.ofReal (N.choose k:ℝ)*prefixInformation μ Q N k ≠ ⊤ at ht
  have hc : ENNReal.ofReal (N.choose k:ℝ) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (by exact_mod_cast Nat.choose_pos hk)
  intro h
  rw [h,ENNReal.mul_top hc] at ht
  exact ht rfl

theorem informationRatio_finite_iff (μ : Measure Gap) [IsProbabilityMeasure μ]
    (N : ℕ) (Q : FourPriors) (hN : 0 < N) :
    informationRatio μ N Q ≠ ⊤ ↔ ∀ n k, n ≤ N → k ≤ n → prefixInformation μ Q n k ≠ ⊤ := by
  constructor
  · exact prefixInformation_finite_of_ratio μ Q hN
  · intro h
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (informationRatio_le_bellmanRatio μ N Q h)

theorem prefixInformation_top_iff (μ : Measure Gap) (Q : FourPriors) (n k : ℕ) :
    prefixInformation μ Q n k = ⊤ ↔ prefixCoefficient μ Q.variance n k = 0 ∧
      prefixCoefficient μ Q.high n k ≠ prefixCoefficient μ Q.low n k := by
  have hv := prefixCoefficient_nonneg μ Q.variance n k
  by_cases hpos : 0 < prefixCoefficient μ Q.variance n k
  · simp [prefixInformation,perspective,hpos,hpos.ne']
  · have hz : prefixCoefficient μ Q.variance n k = 0 := by linarith
    simp [prefixInformation,perspective,hz,sub_eq_zero]

theorem informationRatio_top_iff (μ : Measure Gap) [IsProbabilityMeasure μ]
    (N : ℕ) (Q : FourPriors) (hN : 0 < N) :
    informationRatio μ N Q = ⊤ ↔ ∃ n k, n ≤ N ∧ k ≤ n ∧
      prefixCoefficient μ Q.variance n k = 0 ∧
      prefixCoefficient μ Q.high n k ≠ prefixCoefficient μ Q.low n k := by
  have hh := not_congr (informationRatio_finite_iff μ N Q hN)
  push Not at hh
  simpa only [prefixInformation_top_iff] using hh

end ThresholdHC.StoppingProgram
