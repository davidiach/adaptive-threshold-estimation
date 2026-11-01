import ThresholdHC.EntropyTailLower.CertificateLabel
import ThresholdHC.EntropyTailLower.CanonicalBands

noncomputable section
namespace ThresholdHC.EntropyTailLower
open MeasureTheory Real
open scoped BigOperators ENNReal
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram

theorem certificate_localized_label_bound {T : Type} [Fintype T] {N : ℕ}
    (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ) (hB : 0 < B)
    (C : Certificate N) (hC : Feasible μ ρ B C)
    (S : T → Set Gap) (hS : ∀ i, MeasurableSet (S i))
    (hd : Pairwise (fun i j => Disjoint (S i) (S j))) (hm : ∀ i, μ (S i) ≠ 0)
    (r : T → ℝ) (hr : ∀ i, 0 < r i) (hr1 : ∀ i, r i ≤ 1)
    (hρ : ∑ i, μ.real (S i)*r i ≤ ρ)
    (u : T → ℝ) (hu : ∀ i, 0 ≤ u i) (hcap : ∀ i, u i ≤ μ.real (S i)*r i)
    (hcost : ∀ i, (u i)^2*B ≤ (μ.real (S i))^2*r i) :
    ∑ i, u i ≤ 256*C.bias+4*sqrt C.variance := by
  obtain ⟨D,w,hD,he,hv,hw⟩ := certificate_component_localization μ ρ B C hC
    S hS hd hm r (fun i => (hr i).le) hρ
  have ht (i) : 0 < μ.real (S i) := ENNReal.toReal_pos (hm i) (measure_ne_top μ (S i))
  let (i : T) : IsProbabilityMeasure (ProbabilityTheory.cond μ (S i)) :=
    ProbabilityTheory.cond_isProbabilityMeasure (hm i)
  have hg (i) (hsmall : μ.real (S i)*(D i).bias ≤ (μ.real (S i)*r i)/128) :
      (u i)^2*B ≤ 16*(μ.real (S i)*(D i).variance)*(μ.real (S i)*w i) := by
    have hbias : (D i).bias ≤ r i/128 := by
      have heq : (μ.real (S i)*r i)/128 = μ.real (S i)*(r i/128) := by ring
      rw [heq] at hsmall
      exact (mul_le_mul_iff_right₀ (ht i)).mp hsmall
    have hl := certificate_small_bias_label_floor (ProbabilityTheory.cond μ (S i))
      (r i) (w i) (hr i) (hr1 i) (D i) (hD i).2.2 hbias
    have hh := (hcost i).trans (mul_le_mul_of_nonneg_left hl (sq_nonneg (μ.real (S i))))
    convert hh using 1; ring
  have hh := finite_component_obstructions u
    (fun i => μ.real (S i)*(D i).bias) (fun i => μ.real (S i)*(D i).variance)
    (fun i => μ.real (S i)*w i) (fun i => μ.real (S i)*r i)
    B C.variance (2*C.bias) 16 128 hu
    (fun i => mul_nonneg (ht i).le (hD i).2.2.bias_nonneg)
    (fun i => mul_nonneg (ht i).le (hD i).2.2.variance_nonneg)
    (fun i => mul_nonneg (ht i).le (hD i).2.1) hB (by norm_num) (by norm_num)
    he hv hw (fun i _ => hcap i) hg
  rw [sqrt_mul (by norm_num : (0:ℝ) ≤ 16)] at hh
  norm_num at hh
  linarith

theorem certificate_disjoint_label_allocation {T : Type} [Fintype T] {N : ℕ}
    (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ) (hB : 0 < B)
    (C : Certificate N) (hC : Feasible μ ρ B C)
    (S : T → Set Gap) (hS : ∀ i, MeasurableSet (S i))
    (hd : Pairwise (fun i j => Disjoint (S i) (S j))) (hm : ∀ i, μ (S i) ≠ 0)
    (r : T → ℝ) (hr : ∀ i, 0 < r i) (hr1 : ∀ i, r i ≤ 1)
    (hρ : ∑ i, μ.real (S i)*r i ≤ ρ) :
    (∑ i, μ.real (S i)*min (r i) (sqrt (r i/B))) ≤ 256*C.bias+4*sqrt C.variance := by
  apply certificate_localized_label_bound μ ρ B hB C hC S hS hd hm r hr hr1 hρ
  · intro i
    exact mul_nonneg ENNReal.toReal_nonneg (le_min (hr i).le (sqrt_nonneg _))
  · intro i
    exact mul_le_mul_of_nonneg_left (min_le_left _ _) ENNReal.toReal_nonneg
  · intro i
    have hn : 0 ≤ min (r i) (sqrt (r i/B)) := le_min (hr i).le (sqrt_nonneg _)
    have hs : (min (r i) (sqrt (r i/B)))^2 ≤ r i/B :=
      ((sq_le_sq₀ hn (sqrt_nonneg _)).mpr (min_le_right _ _)).trans_eq
        (sq_sqrt (div_nonneg (hr i).le hB.le))
    have hh := mul_le_mul_of_nonneg_left
      ((mul_le_mul_of_nonneg_right hs hB.le).trans_eq (div_mul_cancel₀ _ hB.ne'))
      (sq_nonneg (μ.real (S i)))
    convert hh using 1; ring

theorem certificate_band_label_allocation {T : Type} [Fintype T] {N : ℕ}
    (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ) (hB : 0 < B)
    (C : Certificate N) (hC : Feasible μ ρ B C)
    (j : T → ℕ) (hj : Function.Injective j)
    (r : T → ℝ) (hr : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i ≤ 1)
    (hρ : ∑ i, μ.real (ThresholdHC.EntropyTail.band (j i))*r i ≤ ρ) :
    (∑ i, μ.real (ThresholdHC.EntropyTail.band (j i))*min (r i) (sqrt (r i/B))) ≤
      256*C.bias+4*sqrt C.variance := by
  classical
  let p := fun i => 0 < r i ∧ μ (ThresholdHC.EntropyTail.band (j i)) ≠ 0
  have hz (i : T) (hi : ¬p i) : r i = 0 ∨ μ (ThresholdHC.EntropyTail.band (j i)) = 0 := by
    by_cases hh : 0 < r i
    · exact Or.inr (by by_contra hn; exact hi ⟨hh,hn⟩)
    · exact Or.inl (le_antisymm (le_of_not_gt hh) (hr i))
  have hm : (∑ i : {i // p i}, μ.real (ThresholdHC.EntropyTail.band (j i))*r i) =
      ∑ i, μ.real (ThresholdHC.EntropyTail.band (j i))*r i := by
    apply sum_subtype_eq_of_zero p (fun i => μ.real (ThresholdHC.EntropyTail.band (j i))*r i)
    intro i hi
    rcases hz i hi with h | h <;> simp [h,Measure.real]
  have hc : (∑ i : {i // p i}, μ.real (ThresholdHC.EntropyTail.band (j i))*min (r i) (sqrt (r i/B))) =
      ∑ i, μ.real (ThresholdHC.EntropyTail.band (j i))*min (r i) (sqrt (r i/B)) := by
    apply sum_subtype_eq_of_zero p (fun i => μ.real (ThresholdHC.EntropyTail.band (j i))*min (r i) (sqrt (r i/B)))
    intro i hi
    rcases hz i hi with h | h <;> simp [h,Measure.real]
  have hh := certificate_disjoint_label_allocation μ ρ B hB C hC
    (fun i : {i // p i} => ThresholdHC.EntropyTail.band (j i))
    (fun i => ThresholdHC.EntropyTail.measurableSet_band (j i))
    (fun i k hik => ThresholdHC.EntropyTail.band_disjoint (fun he => hik (Subtype.ext (hj he))))
    (fun i => i.property.2) (fun i => r i) (fun i => i.property.1) (fun i => hr1 i)
    (by rw [hm]; exact hρ)
  rwa [hc] at hh

end ThresholdHC.EntropyTailLower
