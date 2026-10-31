import ThresholdHC.StoppingProgram.PrefixCoefficients

/-! Weighted telescoping of finite count flows. The root activation is
counted once, and terminal continuation has no contribution. -/

noncomputable section
open scoped BigOperators

namespace ThresholdHC.StoppingProgram

def rawLayer {N : ℕ} (u : CountState N → ℝ) (v : ℕ → ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n+1), rawArray u n k*v n k

def rawChildren {N : ℕ} (u : CountState N → ℝ) (v : ℕ → ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n+1), rawArray u n k*(v (n+1) k+v (n+1) (k+1))

theorem rawArray_outside {N : ℕ} (u : CountState N → ℝ) (n k : ℕ) (hk : n < k) : rawArray u n k = 0 := by
  simp [rawArray,Nat.choose_eq_zero_of_lt hk]

theorem raw_layer_conservation {N : ℕ} (f : Flow N) (hf : FlowCone f)
    (v : ℕ → ℕ → ℝ) (n : ℕ) (hn : n < N) :
    rawLayer f.stopWeight v (n+1)+rawLayer f.continueWeight v (n+1) =
      rawChildren f.continueWeight v n := by
  unfold rawLayer rawChildren
  rw [← Finset.sum_add_distrib]
  have he : (∑ k ∈ Finset.range (n+1+1),
      (rawArray f.stopWeight (n+1) k*v (n+1) k+rawArray f.continueWeight (n+1) k*v (n+1) k)) =
      (∑ k ∈ Finset.range (n+2), rawArray f.continueWeight n k*v (n+1) k)+
      ∑ k ∈ Finset.range (n+2), (if 0 < k then rawArray f.continueWeight n (k-1) else 0)*v (n+1) k := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [← add_mul,raw_flow_recursion f hf (n+1) k (by omega) (by omega) (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hk))]
    simp only [Nat.add_sub_cancel,add_mul]
  rw [he]
  rw [Finset.sum_range_succ (fun k => rawArray f.continueWeight n k*v (n+1) k) (n+1),
    rawArray_outside _ n (n+1) (by omega),zero_mul,add_zero]
  rw [Finset.sum_range_succ' (fun k => (if 0 < k then rawArray f.continueWeight n (k-1) else 0)*v (n+1) k) (n+1)]
  simp only [Nat.succ_pos,ite_true,Nat.add_sub_cancel,lt_self_iff_false,ite_false,zero_mul,add_zero]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

theorem rawArray_terminal {N : ℕ} (f : Flow N) (hf : FlowCone f) (k : ℕ) :
    rawArray f.continueWeight N k = 0 := by
  by_cases hk : k ≤ N
  · let s : CountState N := ⟨⟨N,by omega⟩,⟨k,by change k < N+1; omega⟩⟩
    rw [rawArray,show arrayAt f.continueWeight N k = f.continueWeight s from arrayAt_state _ s,
      hf.terminal s rfl,mul_zero]
  · exact rawArray_outside _ _ _ (by omega)

theorem raw_root_total {N : ℕ} (f : Flow N) (hf : FlowCone f) (v : ℕ → ℕ → ℝ) :
    rawLayer f.stopWeight v 0+rawLayer f.continueWeight v 0 = intensity f*v 0 0 := by
  simp only [rawLayer,zero_add,Finset.sum_range_one,rawArray,Nat.choose_zero_right,Nat.cast_one,one_mul]
  change f.stopWeight (rootState N)*v 0 0+f.continueWeight (rootState N)*v 0 0 = _
  rw [hf.root_stop,zero_mul,zero_add]
  rfl

theorem raw_weighted_telescope {N : ℕ} (f : Flow N) (hf : FlowCone f) (v : ℕ → ℕ → ℝ) :
    (∑ n ∈ Finset.range (N+1), (rawLayer f.stopWeight v n+rawLayer f.continueWeight v n-
      rawChildren f.continueWeight v n)) = intensity f*v 0 0 := by
  have hpartial (m : ℕ) (hm : m ≤ N) :
      (∑ n ∈ Finset.range (m+1), (rawLayer f.stopWeight v n+rawLayer f.continueWeight v n-
        rawChildren f.continueWeight v n)) =
      intensity f*v 0 0-rawChildren f.continueWeight v m := by
    induction m with
    | zero => simp only [zero_add,Finset.sum_range_one,raw_root_total f hf]
    | succ m ih =>
      rw [Finset.sum_range_succ,ih (by omega),raw_layer_conservation f hf v m (by omega)]
      ring
  rw [hpartial N le_rfl]
  simp only [rawChildren,rawArray_terminal f hf,zero_mul,Finset.sum_const_zero,sub_zero]

theorem rawLayer_countMean {N : ℕ} (μ : MeasureTheory.Measure ThresholdHC.Tier6.Gap)
    (q : ThresholdHC.Tier6.SignLaw) (u : CountState N → ℝ) :
    (∑ n ∈ Finset.range (N+1), rawLayer u (prefixCoefficient μ q) n) = countMean μ q u := by
  rw [countMean_raw]
  unfold rawLayer
  rw [Fintype.sum_sigma]
  symm
  calc
    _ = ∑ n : Fin (N+1), ∑ k ∈ Finset.range (n.val+1),
        rawArray u n.val k*prefixCoefficient μ q n.val k := by
      apply Finset.sum_congr rfl
      intro n _
      exact Fin.sum_univ_eq_sum_range (fun k => rawArray u n.val k*prefixCoefficient μ q n.val k) _
    _ = _ := Fin.sum_univ_eq_sum_range
      (fun n => ∑ k ∈ Finset.range (n+1), rawArray u n k*prefixCoefficient μ q n k) _

theorem countMean_stop_eq_intensity {N : ℕ} (μ : MeasureTheory.Measure ThresholdHC.Tier6.Gap)
    [MeasureTheory.IsProbabilityMeasure μ] (q : ThresholdHC.Tier6.SignLaw) (f : Flow N) (hf : FlowCone f) :
    countMean μ q f.stopWeight = intensity f := by
  have hc (n : ℕ) : rawChildren f.continueWeight (prefixCoefficient μ q) n =
      rawLayer f.continueWeight (prefixCoefficient μ q) n := by
    unfold rawChildren rawLayer
    apply Finset.sum_congr rfl
    intro k hk
    rw [prefixCoefficient_add μ q n k (by have h := Finset.mem_range.mp hk; omega)]
  have h := raw_weighted_telescope f hf (prefixCoefficient μ q)
  simp only [hc,add_sub_cancel_right,prefixCoefficient_root,mul_one] at h
  rwa [rawLayer_countMean] at h

end ThresholdHC.StoppingProgram
