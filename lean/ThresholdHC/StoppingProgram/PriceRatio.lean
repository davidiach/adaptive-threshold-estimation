import ThresholdHC.StoppingProgram.Bellman

/-! A finite maximum of information-minus-price-times-work has a unique zero
at the maximal information/work ratio. Randomized mixtures cannot improve it. -/

noncomputable section
open scoped BigOperators

namespace ThresholdHC.StoppingProgram
variable {I : Type*} [Fintype I] [Nonempty I]

def priceValue (a c : I → ℝ) (κ : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => a i-κ*c i)

def ratioValue (a c : I → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => a i/c i)

theorem priceValue_attained (a c : I → ℝ) (κ : ℝ) : ∃ i, a i-κ*c i = priceValue a c κ := by
  obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => a i-κ*c i)
  exact ⟨i,hi.symm⟩

theorem ratioValue_attained (a c : I → ℝ) : ∃ i, a i/c i = ratioValue a c := by
  obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => a i/c i)
  exact ⟨i,hi.symm⟩

theorem le_priceValue (a c : I → ℝ) (κ : ℝ) (i : I) : a i-κ*c i ≤ priceValue a c κ :=
  Finset.le_sup' (fun j => a j-κ*c j) (Finset.mem_univ i)

theorem le_ratioValue (a c : I → ℝ) (i : I) : a i/c i ≤ ratioValue a c :=
  Finset.le_sup' (fun j => a j/c j) (Finset.mem_univ i)

theorem priceValue_le_zero_iff (a c : I → ℝ) (hc : ∀ i, 0 < c i) (κ : ℝ) :
    priceValue a c κ ≤ 0 ↔ ratioValue a c ≤ κ := by
  simp only [priceValue,ratioValue,Finset.sup'_le_iff,Finset.mem_univ,true_implies,
    sub_nonpos,div_le_iff₀ (hc _)]

theorem priceValue_at_ratio (a c : I → ℝ) (hc : ∀ i, 0 < c i) :
    priceValue a c (ratioValue a c) = 0 := by
  apply le_antisymm ((priceValue_le_zero_iff a c hc _).mpr le_rfl)
  obtain ⟨i,hi⟩ := ratioValue_attained a c
  have he : a i-ratioValue a c*c i = 0 := by rw [← hi,div_mul_cancel₀ _ (hc i).ne']; ring
  exact he.symm.le.trans (le_priceValue a c _ i)

theorem priceValue_strictAnti (a c : I → ℝ) (hc : ∀ i, 0 < c i) : StrictAnti (priceValue a c) := by
  intro x y hxy
  obtain ⟨i,hi⟩ := priceValue_attained a c y
  have h := mul_lt_mul_of_pos_right hxy (hc i)
  have hu := le_priceValue a c x i
  linarith

theorem priceValue_zero_iff (a c : I → ℝ) (hc : ∀ i, 0 < c i) (κ : ℝ) :
    priceValue a c κ = 0 ↔ κ = ratioValue a c := by
  constructor
  · intro h
    exact (priceValue_strictAnti a c hc).injective (h.trans (priceValue_at_ratio a c hc).symm)
  · rintro rfl
    exact priceValue_at_ratio a c hc

theorem ratioValue_nonneg (a c : I → ℝ) (ha : ∀ i, 0 ≤ a i) (hc : ∀ i, 0 ≤ c i) :
    0 ≤ ratioValue a c := by
  let i := Classical.choice (inferInstance : Nonempty I)
  exact (div_nonneg (ha i) (hc i)).trans (le_ratioValue a c i)

theorem randomized_price_le (a c p : I → ℝ) (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1) (κ : ℝ) :
    (∑ i, p i*a i)-κ*(∑ i, p i*c i) ≤ priceValue a c κ := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    mul_le_mul_of_nonneg_left (le_priceValue a c κ i) (hp i))
  simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,hpsum,one_mul] at h
  convert h using 1
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem rootBellman_eq_priceValue (r w : ℕ → ℕ → ℝ) (κ : ℝ) (d : ℕ) :
    rootBellman r w κ d = priceValue (rootInformation r d) (rootWork w d) κ := by
  obtain ⟨hu,a,ha⟩ := rootBellman_maximum r w κ d
  apply le_antisymm
  · exact ha.symm.le.trans (le_priceValue _ _ κ a)
  · exact Finset.sup'_le _ _ (fun a _ => hu a)

theorem rootBellman_strictAnti (r w : ℕ → ℕ → ℝ) (hw : ∀ n k, 0 ≤ w n k) (d : ℕ) :
    StrictAnti (fun κ => rootBellman r w κ d) := by
  have hc (a : StopTree d × StopTree d) : 0 < rootWork w d a := by
    unfold rootWork
    positivity [treeWork_nonneg w hw d 1 0 a.1,treeWork_nonneg w hw d 1 1 a.2]
  simpa only [rootBellman_eq_priceValue] using priceValue_strictAnti (rootInformation r d) (rootWork w d) hc

theorem rootBellman_zero_iff (r w : ℕ → ℕ → ℝ) (hw : ∀ n k, 0 ≤ w n k) (d : ℕ) (κ : ℝ) :
    rootBellman r w κ d = 0 ↔ κ = ratioValue (rootInformation r d) (rootWork w d) := by
  rw [rootBellman_eq_priceValue]
  apply priceValue_zero_iff
  intro a
  unfold rootWork
  positivity [treeWork_nonneg w hw d 1 0 a.1,treeWork_nonneg w hw d 1 1 a.2]

end ThresholdHC.StoppingProgram
