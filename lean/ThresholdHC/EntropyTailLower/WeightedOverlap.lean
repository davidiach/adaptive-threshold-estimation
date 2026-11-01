import ThresholdHC.CriticalEntropy.FiniteGap

/-! Exponentially weighted overlap of actual stopping windows.
No termination under the fair-coin law is assumed. -/
noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace ThresholdHC.EntropyTailLower
open ThresholdHC.CriticalEntropy

theorem geometric_reciprocal_sum (n : ℕ) :
    (∑ i ∈ Finset.range n, (1/4 : ℝ)^i) ≤ 2 := by
  have h := geom_sum_mul_of_le_one (by norm_num : (1/4 : ℝ) ≤ 1) n
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/4) n]

theorem separated_square_gaps {K : ℕ} (d : Fin K → EntropyGap)
    (hgap : ∀ i j, j.val = i.val+1 → 2*(d j : ℝ) ≤ (d i : ℝ))
    (i j : Fin K) (hij : i ≤ j) :
    (4 : ℝ)^(j.val-i.val)*(d j : ℝ)^2 ≤ (d i : ℝ)^2 := by
  have h := inverse_gap_scales_separated d hgap i j hij
  have hi := sq_pos_of_pos (d i).property.1
  have hj := sq_pos_of_pos (d j).property.1
  rw [mul_one_div] at h
  simpa only [one_mul] using (div_le_div_iff₀ hi hj).mp h

theorem stopping_window_cost {R : Type} [MeasurableSpace R]
    (ν : Measure R) (A : SignTest R) (d : EntropyGap)
    (z : R × (ℕ → Bool)) (t : ℕ) (hstop : A.stop z = t)
    (hz : z ∈ signTestWindow A (entropyLowerTime d)
      (entropyUpperTime (expectedSignTestWork ν (signParameter d false) A).toReal)) :
    (1/2048 : ℝ) < (t:ℝ)*(d:ℝ)^2 ∧
      (t:ℝ)*(d:ℝ)^2 / 8 ≤
        (d:ℝ)^2*(expectedSignTestWork ν (signParameter d false) A).toReal := by
  have hd := sq_pos_of_pos d.property.1
  have hn := (entropyLowerTime_bounds d).1
  have hu := (entropyUpperTime_bounds
    (expectedSignTestWork ν (signParameter d false) A).toReal ENNReal.toReal_nonneg).2.2
  have hnt : entropyLowerTime d < t := by
    have h := hz.2.1
    rw [hstop] at h
    exact_mod_cast h
  have htu : t ≤ entropyUpperTime
      (expectedSignTestWork ν (signParameter d false) A).toReal := by
    have h := hz.2.2
    rw [hstop] at h
    exact_mod_cast h
  have hnt' : (entropyLowerTime d : ℝ) < t := by exact_mod_cast hnt
  have htu' : (t:ℝ) ≤ entropyUpperTime
      (expectedSignTestWork ν (signParameter d false) A).toReal := by exact_mod_cast htu
  have hfirst : (1/2048 : ℝ) < (t:ℝ)*(d:ℝ)^2 :=
    (div_lt_iff₀ hd).mp (hn.trans_lt hnt')
  have hdsq : (d:ℝ)^2 ≤ 1/16384 := by
    have h := (sq_le_sq₀ d.property.1.le (by norm_num : (0:ℝ) ≤ 1/128)).mpr d.property.2
    norm_num at h ⊢
    exact h
  have ht0 : (0:ℝ) ≤ t := Nat.cast_nonneg _
  have ht4 : (4:ℝ) ≤ t := by nlinarith
  constructor
  · exact hfirst
  · have hw : (t:ℝ)/8 ≤ (expectedSignTestWork ν (signParameter d false) A).toReal := by
      linarith
    nlinarith [mul_le_mul_of_nonneg_right hw hd.le]

theorem signTest_exponential_overlap {R : Type} [MeasurableSpace R]
    (ν : Measure R) (A : SignTest R) {K : ℕ} (d : Fin K → EntropyGap)
    (hgap : ∀ i j, j.val = i.val+1 → 2*(d j : ℝ) ≤ (d i : ℝ))
    (z : R × (ℕ → Bool)) :
    (∑ i, (signTestWindow A (entropyLowerTime (d i))
      (entropyUpperTime (expectedSignTestWork ν (signParameter (d i) false) A).toReal)).indicator
        (fun _ => exp (-((d i : ℝ)^2*
          (expectedSignTestWork ν (signParameter (d i) false) A).toReal))) z) ≤ 32768 := by
  classical
  let cost := fun i : Fin K => (d i : ℝ)^2*
    (expectedSignTestWork ν (signParameter (d i) false) A).toReal
  let events := fun i : Fin K => signTestWindow A (entropyLowerTime (d i))
    (entropyUpperTime (expectedSignTestWork ν (signParameter (d i) false) A).toReal)
  let s := Finset.univ.filter (fun i => z ∈ events i)
  change (∑ i, (events i).indicator (fun _ => exp (-cost i)) z) ≤ _
  have heq : (∑ i, (events i).indicator (fun _ => exp (-cost i)) z) =
      ∑ i ∈ s, exp (-cost i) := by
    simp only [s, Finset.sum_filter, Set.indicator_apply]
  rw [heq]
  by_cases hs : s.Nonempty
  · let j := s.max' hs
    have hj : j ∈ s := s.max'_mem hs
    have hzj : z ∈ events j := (Finset.mem_filter.mp hj).2
    cases hstop : A.stop z with
    | top =>
      have h := hzj.2.2
      rw [hstop] at h
      simp at h
    | coe t =>
      have hbase := (stopping_window_cost ν A (d j) z t hstop hzj).1
      have hi (i : Fin K) (his : i ∈ s) :
          exp (-cost i) ≤ 16384*(1/4 : ℝ)^(j.val-i.val) := by
        have hij : i ≤ j := s.le_max' i his
        have hwi := (stopping_window_cost ν A (d i) z t hstop
          (Finset.mem_filter.mp his).2).2
        have hsep := separated_square_gaps d hgap i j hij
        have ht : (0:ℝ) ≤ t := Nat.cast_nonneg _
        have hp : 0 < (4:ℝ)^(j.val-i.val) := by positivity
        have hc : (4:ℝ)^(j.val-i.val)/16384 ≤ cost i := by
          have h₁ := mul_le_mul_of_nonneg_left hsep ht
          have h₂ := mul_le_mul_of_nonneg_left hbase.le hp.le
          dsimp [cost]
          nlinarith
        have he : cost i ≤ exp (cost i) := by linarith [add_one_le_exp (cost i)]
        have hexp := hc.trans he
        have hpow : (4:ℝ)^(j.val-i.val)*(1/4:ℝ)^(j.val-i.val) = 1 := by
          rw [← mul_pow]
          norm_num
        rw [exp_neg, ← one_div]
        apply (div_le_iff₀ (exp_pos _)).mpr
        have hh := mul_le_mul_of_nonneg_right hexp (by positivity : 0 ≤ (1/4:ℝ)^(j.val-i.val))
        nlinarith
      have hinj : Set.InjOn (fun i : Fin K => j.val-i.val) (↑s : Set (Fin K)) := by
        intro a ha b hb hab
        have ha' : a.val ≤ j.val := s.le_max' a ha
        have hb' : b.val ≤ j.val := s.le_max' b hb
        change j.val-a.val = j.val-b.val at hab
        apply Fin.ext
        omega
      have hsubset : s.image (fun i : Fin K => j.val-i.val) ⊆ Finset.range (j.val+1) := by
        intro n hn
        obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hn
        simp only [Finset.mem_range]
        omega
      calc
        _ ≤ ∑ i ∈ s, 16384*(1/4 : ℝ)^(j.val-i.val) := Finset.sum_le_sum hi
        _ = 16384*∑ n ∈ s.image (fun i : Fin K => j.val-i.val), (1/4:ℝ)^n := by
          rw [Finset.sum_image hinj, Finset.mul_sum]
        _ ≤ 16384*∑ n ∈ Finset.range (j.val+1), (1/4:ℝ)^n := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => by positivity)
        _ ≤ 16384*2 := mul_le_mul_of_nonneg_left (geometric_reciprocal_sum _) (by norm_num)
        _ = 32768 := by norm_num
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [he]

end ThresholdHC.EntropyTailLower
