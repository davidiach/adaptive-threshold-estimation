import ThresholdHC.StoppingProgram.FlowConservation

/-! Extended prefix information and its exact relation to count-flow
information. Infinite values retain the closed perspective convention. -/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap)

def prefixInformation (μ : Measure Gap) (Q : FourPriors) (n k : ℕ) : ℝ≥0∞ :=
  perspective (prefixCoefficient μ Q.high n k-prefixCoefficient μ Q.low n k)
    (prefixCoefficient μ Q.variance n k)

def prefixReward (μ : Measure Gap) (Q : FourPriors) (n k : ℕ) : ℝ :=
  (prefixInformation μ Q n k).toReal

theorem prefixInformation_root (μ : Measure Gap) [IsProbabilityMeasure μ] (Q : FourPriors) :
    prefixInformation μ Q 0 0 = 0 := by
  simp [prefixInformation,prefixCoefficient_root,perspective]

theorem prefixInformation_children (μ : Measure Gap) [IsProbabilityMeasure μ]
    (Q : FourPriors) (n k : ℕ) (hk : k ≤ n) :
    prefixInformation μ Q n k ≤ prefixInformation μ Q (n+1) k+prefixInformation μ Q (n+1) (k+1) := by
  have he : prefixCoefficient μ Q.high n k-prefixCoefficient μ Q.low n k =
      (prefixCoefficient μ Q.high (n+1) k-prefixCoefficient μ Q.low (n+1) k)+
      (prefixCoefficient μ Q.high (n+1) (k+1)-prefixCoefficient μ Q.low (n+1) (k+1)) := by
    rw [← prefixCoefficient_add μ Q.high n k hk,← prefixCoefficient_add μ Q.low n k hk]
    ring
  unfold prefixInformation
  rw [he,← prefixCoefficient_add μ Q.variance n k hk]
  exact perspective_add_le (prefixCoefficient_nonneg μ Q.variance _ _) (prefixCoefficient_nonneg μ Q.variance _ _)

theorem countInformation_eq {N : ℕ} (μ : Measure Gap) (Q : FourPriors) (s : CountState N) :
    perspective (countCoefficient μ Q.high s-countCoefficient μ Q.low s) (countCoefficient μ Q.variance s) =
      ENNReal.ofReal (s.1.val.choose s.2.val:ℝ)*prefixInformation μ Q s.1.val s.2.val := by
  change perspective ((s.1.val.choose s.2.val:ℝ)*prefixCoefficient μ Q.high s.1.val s.2.val-
    (s.1.val.choose s.2.val:ℝ)*prefixCoefficient μ Q.low s.1.val s.2.val)
      ((s.1.val.choose s.2.val:ℝ)*prefixCoefficient μ Q.variance s.1.val s.2.val) = _
  rw [← mul_sub,perspective_scale _ _ (Nat.cast_nonneg _)]
  rfl

theorem flowInformation_raw_states {N : ℕ} (μ : Measure Gap) (Q : FourPriors) (f : Flow N) :
    flowInformation μ Q f = ∑ s : CountState N,
      ENNReal.ofReal (rawArray f.stopWeight s.1.val s.2.val)*prefixInformation μ Q s.1.val s.2.val := by
  unfold flowInformation
  apply Finset.sum_congr rfl
  intro s _
  rw [countInformation_eq,rawArray,arrayAt_state,ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  ac_rfl

theorem flowInformation_raw {N : ℕ} (μ : Measure Gap) (Q : FourPriors) (f : Flow N) :
    flowInformation μ Q f = ∑ n ∈ Finset.range (N+1), ∑ k ∈ Finset.range (n+1),
      ENNReal.ofReal (rawArray f.stopWeight n k)*prefixInformation μ Q n k := by
  rw [flowInformation_raw_states,Fintype.sum_sigma]
  calc
    _ = ∑ n : Fin (N+1), ∑ k ∈ Finset.range (n.val+1),
        ENNReal.ofReal (rawArray f.stopWeight n.val k)*prefixInformation μ Q n.val k := by
      apply Finset.sum_congr rfl
      intro n _
      exact Fin.sum_univ_eq_sum_range
        (fun k => ENNReal.ofReal (rawArray f.stopWeight n.val k)*prefixInformation μ Q n.val k) _
    _ = _ := Fin.sum_univ_eq_sum_range
      (fun n => ∑ k ∈ Finset.range (n+1), ENNReal.ofReal (rawArray f.stopWeight n k)*prefixInformation μ Q n k) _

theorem flowInformation_finite_prefixes {N : ℕ} (μ : Measure Gap) (Q : FourPriors) (f : Flow N)
    (hfin : ∀ n k, n ≤ N → k ≤ n → prefixInformation μ Q n k ≠ ⊤) : flowInformation μ Q f ≠ ⊤ := by
  rw [flowInformation_raw_states]
  apply ENNReal.sum_ne_top.mpr
  intro s _
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (hfin _ _ (by have h := s.1.isLt; omega) (by have h := s.2.isLt; omega))

theorem flowInformation_toReal_raw {N : ℕ} (μ : Measure Gap) (Q : FourPriors)
    (f : Flow N) (hf : FlowCone f)
    (hfin : ∀ n k, n ≤ N → k ≤ n → prefixInformation μ Q n k ≠ ⊤) :
    (flowInformation μ Q f).toReal = ∑ n ∈ Finset.range (N+1),
      rawLayer f.stopWeight (prefixReward μ Q) n := by
  rw [flowInformation_raw]
  rw [ENNReal.toReal_sum (fun n hn => ENNReal.sum_ne_top.mpr (fun k hk =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin _ _ (by have h := Finset.mem_range.mp hn; omega)
      (by have h := Finset.mem_range.mp hk; omega))))]
  apply Finset.sum_congr rfl
  intro n hn
  rw [ENNReal.toReal_sum (fun k hk => ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (hfin _ _ (by have h := Finset.mem_range.mp hn; omega) (by have h := Finset.mem_range.mp hk; omega)))]
  unfold rawLayer
  apply Finset.sum_congr rfl
  intro k _
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal]
  · rfl
  · apply mul_nonneg (Nat.cast_nonneg _)
    unfold arrayAt
    split_ifs <;> first | exact hf.stop_nonneg _ | exact le_rfl

end ThresholdHC.StoppingProgram
