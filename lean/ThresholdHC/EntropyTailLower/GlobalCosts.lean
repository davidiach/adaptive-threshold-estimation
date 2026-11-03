import ThresholdHC.EntropyTailLower.FiniteAllocation
import ThresholdHC.EntropyTailLower.LabelAllocation
import ThresholdHC.EntropyTailLower.FiniteSelection

noncomputable section
namespace ThresholdHC.EntropyTailLower
open MeasureTheory Real
open scoped BigOperators ENNReal
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram

theorem scaled_min_bound (r x y c : ℝ) (hr : 0 ≤ r) (hc : 1 ≤ c) (hy : y ≤ c*x) :
    min r y ≤ c*min r x := by
  rcases le_total r x with h | h
  · rw [min_eq_left h]
    exact (min_le_left _ _).trans (by nlinarith only [mul_le_mul_of_nonneg_right hc hr])
  · rw [min_eq_right h]
    exact (min_le_right _ _).trans hy

theorem label_bound_le_annular_bound {N : ℕ} (C : Certificate N) (hV : 0 ≤ C.variance) :
    256*C.bias+4*sqrt C.variance ≤
      256*C.bias+sqrt ((4294967296*exp 48)*C.variance) := by
  have he : (1:ℝ) ≤ exp 48 := one_le_exp_iff.mpr (by norm_num)
  have hc : (16:ℝ) ≤ 4294967296*exp 48 := by linarith
  have hs := sqrt_le_sqrt (mul_le_mul_of_nonneg_right hc hV)
  rw [sqrt_mul (by norm_num : (0:ℝ) ≤ 16)] at hs
  norm_num at hs
  linarith

theorem certificate_all_band_finiteAllocationBound {I : Type} [Fintype I] {N : ℕ}
    (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ) (hB : 0 < B) (hN : 0 < N)
    (C : Certificate N) (hC : Feasible μ ρ B C)
    (j : I → ℕ) (hj : Function.Injective j) :
    FiniteAllocationBound (fun i => μ.real (ThresholdHC.EntropyTail.band (j i)))
      (fun i => 1/(sqrt B*((1/2:ℝ)^(j i+1)))) ρ
      (65*(256*C.bias+sqrt ((4294967296*exp 48)*C.variance))) := by
  classical
  intro r hr hr4 hρ
  let p := fun i => 6 ≤ j i
  let w := fun i => μ.real (ThresholdHC.EntropyTail.band (j i))
  let t := fun i => 1/(sqrt B*((1/2:ℝ)^(j i+1)))
  have hw (i) : 0 ≤ w i := measureReal_nonneg
  have hmass := Fintype.sum_subtype_add_sum_subtype p (fun i => w i*r i)
  have hlo : (∑ i : {i // p i}, w i*r i) ≤ ρ := by
    have hn := Finset.sum_nonneg (s := Finset.univ)
      (fun (i : {i // ¬p i}) _ => mul_nonneg (hw i) (hr i))
    change (∑ i, w i*r i) ≤ ρ at hρ
    linarith
  have hhi : (∑ i : {i // ¬p i}, w i*r i) ≤ ρ := by
    have hn := Finset.sum_nonneg (s := Finset.univ)
      (fun (i : {i // p i}) _ => mul_nonneg (hw i) (hr i))
    change (∑ i, w i*r i) ≤ ρ at hρ
    linarith
  have hl := certificate_canonical_finiteAllocationBound μ ρ B hB hN C hC
    (fun i : {i // p i} => j i) (fun _ _ h => Subtype.ext (hj h)) (fun i => i.property)
    (fun i => r i) (fun i => hr i) (fun i => hr4 i) hlo
  have hh := certificate_band_label_allocation μ ρ B hB C hC
    (fun i : {i // ¬p i} => j i) (fun _ _ h => Subtype.ext (hj h))
    (fun i => r i) (fun i => hr i) (fun i => by have := hr4 i; linarith) hhi
  have hterm (i : {i // ¬p i}) : w i*min (r i) (t i*sqrt (r i)) ≤
      64*(w i*min (r i) (sqrt (r i/B))) := by
    have hj6 : j i+1 ≤ 6 := by have := i.property; dsimp [p] at this; omega
    have hb : (1/64:ℝ) ≤ (1/2:ℝ)^(j i+1) := by
      have hp := pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/2)
        (by norm_num : (1/2:ℝ) ≤ 1) hj6
      norm_num at hp
      exact hp
    have he : t i*sqrt (r i) = sqrt (r i/B)/((1/2:ℝ)^(j i+1)) := by
      rw [sqrt_div (hr i)]
      dsimp [t]
      ring
    have hs : t i*sqrt (r i) ≤ 64*sqrt (r i/B) := by
      rw [he]
      apply (div_le_iff₀ (show (0:ℝ) < (1/2:ℝ)^(j i+1) by positivity)).mpr
      nlinarith only [mul_le_mul_of_nonneg_right hb (sqrt_nonneg (r i/B))]
    have hm := scaled_min_bound (r i) (sqrt (r i/B)) (t i*sqrt (r i)) 64 (hr i) (by norm_num) hs
    have hx := mul_le_mul_of_nonneg_left hm (hw i)
    nlinarith only [hx]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hterm i)
  rw [← Finset.mul_sum] at hsum
  have hlabel := label_bound_le_annular_bound C hC.variance_nonneg
  have hsplit := Fintype.sum_subtype_add_sum_subtype p (fun i => w i*min (r i) (t i*sqrt (r i)))
  change (∑ i : {i // p i}, w i*min (r i) (t i*sqrt (r i))) ≤ _ at hl
  change (∑ i : {i // ¬p i}, w i*min (r i) (sqrt (r i/B))) ≤ _ at hh
  change (∑ i, w i*min (r i) (t i*sqrt (r i))) ≤ _
  linarith

theorem certificate_all_band_ordinary_cost {n N : ℕ}
    (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ) (hρ : 0 < ρ)
    (hB : 0 < B) (hN : 0 < N) (C : Certificate N) (hC : Feasible μ ρ B C)
    (p : Fin n → Prop) [DecidablePred p]
    (hcap : ∀ i, p i → μ.real (ThresholdHC.EntropyTail.band i.val) ≤ 4*ρ)
    (hp : ∀ i, p i → 1/(sqrt B*((1/2:ℝ)^(i.val+1))) ≤ 1) :
    (∑ i, if p i then μ.real (ThresholdHC.EntropyTail.band i.val)/
      (sqrt B*((1/2:ℝ)^(i.val+1))) else 0) ≤
      2080*(256*C.bias+sqrt ((4294967296*exp 48)*C.variance)) := by
  let w := fun i : Fin n => μ.real (ThresholdHC.EntropyTail.band i.val)
  let v := fun i : Fin n => if p i then w i else 0
  let c := 1/sqrt B
  have hb := certificate_all_band_finiteAllocationBound μ ρ B hB hN C hC
    (fun i : Fin n => i.val) Fin.val_injective
  simp_rw [canonical_inverse_scale B hB] at hb
  have hrestrict := finiteAllocationBound_restrict _ _ ρ _ hb p
  have hv (i) : 0 ≤ v i := by dsimp [v,w]; split_ifs; exact measureReal_nonneg; exact le_rfl
  have hvcap (i) : v i ≤ 4*ρ := by
    dsimp [v,w]
    split_ifs with hi
    · exact hcap i hi
    · positivity
  have hvsmall (i) (hi : 0 < v i) : c*(2:ℝ)^(i.val+1) ≤ 1 := by
    by_cases hpi : p i
    · have hh := hp i hpi
      rwa [canonical_inverse_scale B hB] at hh
    · simp [v,hpi] at hi
  have hcost := finiteAllocationBound_dyadic_ordinary v ρ c _ hρ (by dsimp [c]; positivity)
    hv hvcap hvsmall hrestrict
  have hsum : (∑ i, if p i then w i/(sqrt B*((1/2:ℝ)^(i.val+1))) else 0) =
      c*(∑ i, v i*(2:ℝ)^(i.val+1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : p i
    · simp only [hi,ite_true,v]
      calc
        _ = w i*(1/(sqrt B*((1/2:ℝ)^(i.val+1)))) := by ring
        _ = _ := by rw [canonical_inverse_scale B hB]; dsimp [c]; ring
    · simp [hi,v]
  change (∑ i, if p i then w i/(sqrt B*((1/2:ℝ)^(i.val+1))) else 0) ≤ _
  rw [hsum]
  linarith

theorem certificate_all_band_ignored_cost {I : Type} [Fintype I] {N : ℕ}
    (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ) (hρ : 0 ≤ ρ)
    (hB : 0 < B) (hN : 0 < N) (C : Certificate N) (hC : Feasible μ ρ B C)
    (j : I → ℕ) (hj : Function.Injective j) (p : I → Prop) [DecidablePred p]
    (hp : ∀ i, p i → 1 ≤ 1/(sqrt B*((1/2:ℝ)^(j i+1)))) :
    min ρ (∑ i, if p i then μ.real (ThresholdHC.EntropyTail.band (j i)) else 0) ≤
      260*(256*C.bias+sqrt ((4294967296*exp 48)*C.variance)) := by
  have hb := finiteAllocationBound_restrict _ _ ρ _
    (certificate_all_band_finiteAllocationBound μ ρ B hB hN C hC j hj) p
  have hv (i) : 0 ≤ if p i then μ.real (ThresholdHC.EntropyTail.band (j i)) else 0 := by
    split_ifs; exact measureReal_nonneg; exact le_rfl
  have ht (i) (hi : 0 < if p i then μ.real (ThresholdHC.EntropyTail.band (j i)) else 0) :
      1 ≤ 1/(sqrt B*((1/2:ℝ)^(j i+1))) := by
    by_cases hh : p i
    · exact hp i hh
    · simp [hh] at hi
  have hh := finiteAllocationBound_ignored _ _ ρ _ hρ hv ht hb
  linarith

theorem certificate_optimal_ordinary_cost {n N : ℕ}
    (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ) (hρ : 0 < ρ)
    (hB : 0 < B) (hN : 0 < N) (C : Certificate N) (hC : Feasible μ ρ B C)
    (S : Finset (Fin n))
    (hopt : ∀ T, finiteSelectionScore ((1/sqrt B)*sqrt ρ)
      (fun i : Fin n => μ.real (ThresholdHC.EntropyTail.band i.val)/((1/2:ℝ)^(i.val+1))^2)
      (fun i => μ.real (ThresholdHC.EntropyTail.band i.val)*min 1 ((1/sqrt B)/((1/2:ℝ)^(i.val+1)))) S ≤
      finiteSelectionScore ((1/sqrt B)*sqrt ρ)
      (fun i : Fin n => μ.real (ThresholdHC.EntropyTail.band i.val)/((1/2:ℝ)^(i.val+1))^2)
      (fun i => μ.real (ThresholdHC.EntropyTail.band i.val)*min 1 ((1/sqrt B)/((1/2:ℝ)^(i.val+1)))) T) :
    (∑ i : Fin n, if i ∉ S ∧ 1/sqrt B ≤ (1/2:ℝ)^(i.val+1) then
      μ.real (ThresholdHC.EntropyTail.band i.val)/(sqrt B*((1/2:ℝ)^(i.val+1))) else 0) ≤
      2080*(256*C.bias+sqrt ((4294967296*exp 48)*C.variance)) := by
  apply certificate_all_band_ordinary_cost μ ρ B hρ hB hN C hC
  · intro i hi
    exact optimal_ordinary_band_mass (fun i : Fin n => μ.real (ThresholdHC.EntropyTail.band i.val))
      (fun i => (1/2:ℝ)^(i.val+1)) (fun _ => measureReal_nonneg) (fun _ => by positivity)
      ρ (1/sqrt B) hρ.le (by positivity) S hopt i hi.1 hi.2
  · intro i hi
    have he : 1/(sqrt B*((1/2:ℝ)^(i.val+1))) = (1/sqrt B)/((1/2:ℝ)^(i.val+1)) := by ring
    rw [he]
    exact (div_le_one (show (0:ℝ) < (1/2:ℝ)^(i.val+1) by positivity)).mpr hi.2

theorem certificate_prefix_ignored_cost {n N : ℕ}
    (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ) (hρ : 0 ≤ ρ)
    (hB : 0 < B) (hN : 0 < N) (C : Certificate N) (hC : Feasible μ ρ B C)
    (S : Finset (Fin n)) :
    min ρ (∑ i : Fin n, if i ∉ S ∧ (1/2:ℝ)^(i.val+1) < 1/sqrt B then
      μ.real (ThresholdHC.EntropyTail.band i.val) else 0) ≤
      260*(256*C.bias+sqrt ((4294967296*exp 48)*C.variance)) := by
  apply certificate_all_band_ignored_cost μ ρ B hρ hB hN C hC
    (fun i : Fin n => i.val) Fin.val_injective
  intro i hi
  have he : 1/(sqrt B*((1/2:ℝ)^(i.val+1))) = (1/sqrt B)/((1/2:ℝ)^(i.val+1)) := by ring
  rw [he]
  apply (le_div_iff₀ (show (0:ℝ) < (1/2:ℝ)^(i.val+1) by positivity)).mpr
  simpa using hi.2.le

theorem ordinary_ignored_penalty_split {I : Type} [Fintype I] [DecidableEq I]
    (w b : I → ℝ) (hb : ∀ i, 0 < b i) (h : ℝ) (S : Finset I) :
    (∑ i, if i ∈ S then 0 else w i*min 1 (h/b i)) =
      (∑ i, if i ∉ S ∧ h ≤ b i then w i*h/b i else 0)+
      (∑ i, if i ∉ S ∧ b i < h then w i else 0) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ S
  · simp [hi]
  · by_cases hh : h ≤ b i
    · simp only [hi,not_false_eq_true,hh,true_and,ite_false,ite_true,not_lt.mpr hh,
        min_eq_right ((div_le_one (hb i)).mpr hh),add_zero]
      ring
    · have hbh : b i < h := lt_of_not_ge hh
      have hx : 1 ≤ h/b i := (le_div_iff₀ (hb i)).mpr (by simpa using hbh.le)
      simp [hi,hh,hbh,min_eq_left hx]

end ThresholdHC.EntropyTailLower
